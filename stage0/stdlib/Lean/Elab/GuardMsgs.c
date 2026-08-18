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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Subarray_split___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Message_isTrace___boxed(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_CodeAction_insertBuiltin(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Diff_Action_linePrefix(uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "guard_msgs"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(149, 116, 183, 228, 179, 151, 45, 148)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(183, 103, 150, 225, 110, 223, 115, 232)}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "When true, show a diff between expected and actual messages if they don't match. "};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__3_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__6_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__6_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__6_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__0_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(172, 38, 186, 54, 247, 153, 194, 0)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__6_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__6_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__1_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 100, 105, 248, 32, 123, 59, 131)}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__6_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__6_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_guard__msgs_diff;
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
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "guardMsgsFilterAction"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 4, 244, 232, 164, 150, 223, 103)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 15, 254, 184, 37, 99, 251, 84)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "drop"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__5_value),LEAN_SCALAR_PTR_LITERAL(134, 195, 191, 35, 155, 125, 225, 61)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pass"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__7_value),LEAN_SCALAR_PTR_LITERAL(130, 109, 187, 122, 38, 7, 169, 2)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8_value;
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
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 215, 239, 32, 31, 172, 250, 25)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 247, 236, 102, 6, 79, 161, 127)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(177, 63, 183, 36, 16, 73, 158, 237)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "warning"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 92, 21, 183, 34, 222, 2, 74)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(127, 232, 111, 183, 142, 221, 154, 104)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 108, 205, 157, 13, 129, 29, 60)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "guardMsgsFilter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(20, 187, 182, 29, 56, 60, 165, 253)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "guardMsgsWhitespace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(8, 106, 1, 198, 8, 55, 77, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "guardMsgsOrdering"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 53, 236, 42, 85, 133, 64, 61)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "guardMsgsPositions"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(41, 241, 109, 166, 211, 83, 245, 15)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "guardMsgsSubstring"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(23, 68, 193, 70, 193, 109, 117, 133)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(97, 134, 219, 90, 90, 45, 96, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(234, 149, 90, 50, 108, 230, 18, 172)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "guardMsgsPositionsArg"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(72, 235, 102, 225, 139, 166, 36, 119)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "guardMsgsOrderingArg"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(126, 165, 201, 178, 250, 91, 17, 12)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(255, 187, 8, 190, 181, 123, 198, 7)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sorted"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(242, 25, 158, 210, 170, 109, 109, 131)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "guardMsgsWhitespaceArg"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(133, 245, 235, 68, 150, 72, 242, 178)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "normalized"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__26_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(204, 250, 226, 34, 169, 84, 107, 235)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__28_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__4_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object*);
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
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0 = (const lean_object*)&l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__2;
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__0 = (const lean_object*)&l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__0_value;
static const lean_ctor_object l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__1 = (const lean_object*)&l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__1_value;
static const lean_ctor_object l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__0_value),((lean_object*)&l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__1_value)}};
static const lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2 = (const lean_object*)&l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4_value),LEAN_SCALAR_PTR_LITERAL(80, 121, 62, 112, 73, 11, 102, 99)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabGuardMsgs"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_array_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__0_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__1_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_instImpl___closed__2_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(48, 139, 31, 76, 158, 95, 94, 217)}};
static const lean_ctor_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 172, 183, 87, 120, 30, 187, 134)}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__6_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_54_ = l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(v___x_51_, v___x_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4____boxed(lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_();
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(lean_object* v_line_59_, lean_object* v_pos_60_){
_start:
{
lean_object* v_line_61_; lean_object* v_column_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_line_61_ = lean_ctor_get(v_pos_60_, 0);
lean_inc(v_line_61_);
v_column_62_ = lean_ctor_get(v_pos_60_, 1);
lean_inc(v_column_62_);
lean_dec_ref(v_pos_60_);
v___x_63_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__0));
v___x_64_ = lean_nat_sub(v_line_61_, v_line_59_);
lean_dec(v_line_61_);
v___x_65_ = l_Nat_reprFast(v___x_64_);
v___x_66_ = lean_string_append(v___x_63_, v___x_65_);
lean_dec_ref(v___x_65_);
v___x_67_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__1));
v___x_68_ = lean_string_append(v___x_66_, v___x_67_);
v___x_69_ = l_Nat_reprFast(v_column_62_);
v___x_70_ = lean_string_append(v___x_68_, v___x_69_);
lean_dec_ref(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___boxed(lean_object* v_line_71_, lean_object* v_pos_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v_line_71_, v_pos_72_);
lean_dec(v_line_71_);
return v_res_73_;
}
}
static lean_object* _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_84_ = lean_string_utf8_byte_size(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(lean_object* v_msg_87_, lean_object* v_reportPos_x3f_88_){
_start:
{
lean_object* v___y_91_; lean_object* v___y_95_; uint8_t v___y_96_; lean_object* v___y_98_; uint8_t v___y_99_; uint32_t v___y_100_; lean_object* v_str_104_; lean_object* v_pos_116_; lean_object* v_endPos_117_; uint8_t v_severity_118_; lean_object* v_caption_119_; lean_object* v_data_120_; lean_object* v___x_121_; lean_object* v___y_123_; lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v_str_136_; lean_object* v_str_148_; lean_object* v___y_159_; lean_object* v_str_163_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_pos_116_ = lean_ctor_get(v_msg_87_, 1);
lean_inc_ref(v_pos_116_);
v_endPos_117_ = lean_ctor_get(v_msg_87_, 2);
lean_inc(v_endPos_117_);
v_severity_118_ = lean_ctor_get_uint8(v_msg_87_, sizeof(void*)*5 + 1);
v_caption_119_ = lean_ctor_get(v_msg_87_, 3);
v_data_120_ = lean_ctor_get(v_msg_87_, 4);
lean_inc(v_data_120_);
v___x_121_ = l_Lean_MessageData_toString(v_data_120_);
v___x_170_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_171_ = lean_string_dec_eq(v_caption_119_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__11));
lean_inc_ref(v_caption_119_);
v___x_173_ = lean_string_append(v_caption_119_, v___x_172_);
v___x_174_ = lean_string_append(v___x_173_, v___x_121_);
lean_dec_ref(v___x_121_);
v_str_163_ = v___x_174_;
goto v___jp_162_;
}
else
{
v_str_163_ = v___x_121_;
goto v___jp_162_;
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_93_ = lean_string_append(v___y_91_, v___x_92_);
return v___x_93_;
}
v___jp_94_:
{
if (v___y_96_ == 0)
{
return v___y_95_;
}
else
{
v___y_91_ = v___y_95_;
goto v___jp_90_;
}
}
v___jp_97_:
{
uint32_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 10;
v___x_102_ = lean_uint32_dec_eq(v___y_100_, v___x_101_);
if (v___x_102_ == 0)
{
v___y_91_ = v___y_98_;
goto v___jp_90_;
}
else
{
v___y_95_ = v___y_98_;
v___y_96_ = v___y_99_;
goto v___jp_94_;
}
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_105_ = lean_string_utf8_byte_size(v_str_104_);
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_nat_dec_eq(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_inc_ref(v_str_104_);
v___x_108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_108_, 0, v_str_104_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
v___x_109_ = l_String_Slice_Pos_prev_x3f(v___x_108_, v___x_105_);
if (lean_obj_tag(v___x_109_) == 0)
{
uint32_t v___x_110_; 
lean_dec_ref_known(v___x_108_, 3);
v___x_110_ = 65;
v___y_98_ = v_str_104_;
v___y_99_ = v___x_107_;
v___y_100_ = v___x_110_;
goto v___jp_97_;
}
else
{
lean_object* v_val_111_; lean_object* v___x_112_; 
v_val_111_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_val_111_);
lean_dec_ref_known(v___x_109_, 1);
v___x_112_ = l_String_Slice_Pos_get_x3f(v___x_108_, v_val_111_);
lean_dec(v_val_111_);
lean_dec_ref_known(v___x_108_, 3);
if (lean_obj_tag(v___x_112_) == 0)
{
uint32_t v___x_113_; 
v___x_113_ = 65;
v___y_98_ = v_str_104_;
v___y_99_ = v___x_107_;
v___y_100_ = v___x_113_;
goto v___jp_97_;
}
else
{
lean_object* v_val_114_; uint32_t v___x_115_; 
v_val_114_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_val_114_);
lean_dec_ref_known(v___x_112_, 1);
v___x_115_ = lean_unbox_uint32(v_val_114_);
lean_dec(v_val_114_);
v___y_98_ = v_str_104_;
v___y_99_ = v___x_107_;
v___y_100_ = v___x_115_;
goto v___jp_97_;
}
}
}
else
{
v___y_95_ = v_str_104_;
v___y_96_ = v___x_107_;
goto v___jp_94_;
}
}
v___jp_122_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_126_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__1));
v___x_127_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v___y_124_, v_pos_116_);
v___x_128_ = lean_string_append(v___x_126_, v___x_127_);
lean_dec_ref(v___x_127_);
v___x_129_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2));
v___x_130_ = lean_string_append(v___x_128_, v___x_129_);
v___x_131_ = lean_string_append(v___x_130_, v___y_125_);
lean_dec_ref(v___y_125_);
v___x_132_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_133_ = lean_string_append(v___x_131_, v___x_132_);
v___x_134_ = lean_string_append(v___x_133_, v___y_123_);
lean_dec_ref(v___y_123_);
v_str_104_ = v___x_134_;
goto v___jp_103_;
}
v___jp_135_:
{
if (lean_obj_tag(v_reportPos_x3f_88_) == 1)
{
if (lean_obj_tag(v_endPos_117_) == 0)
{
lean_object* v_val_137_; lean_object* v___x_138_; 
v_val_137_ = lean_ctor_get(v_reportPos_x3f_88_, 0);
v___x_138_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__3));
v___y_123_ = v_str_136_;
v___y_124_ = v_val_137_;
v___y_125_ = v___x_138_;
goto v___jp_122_;
}
else
{
lean_object* v_val_139_; lean_object* v_val_140_; lean_object* v_line_141_; lean_object* v_column_142_; lean_object* v_line_143_; uint8_t v___x_144_; 
v_val_139_ = lean_ctor_get(v_endPos_117_, 0);
lean_inc(v_val_139_);
lean_dec_ref_known(v_endPos_117_, 1);
v_val_140_ = lean_ctor_get(v_reportPos_x3f_88_, 0);
v_line_141_ = lean_ctor_get(v_val_139_, 0);
v_column_142_ = lean_ctor_get(v_val_139_, 1);
v_line_143_ = lean_ctor_get(v_pos_116_, 0);
v___x_144_ = lean_nat_dec_eq(v_line_141_, v_line_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
v___x_145_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v_val_140_, v_val_139_);
v___y_123_ = v_str_136_;
v___y_124_ = v_val_140_;
v___y_125_ = v___x_145_;
goto v___jp_122_;
}
else
{
lean_object* v___x_146_; 
lean_inc(v_column_142_);
lean_dec(v_val_139_);
v___x_146_ = l_Nat_reprFast(v_column_142_);
v___y_123_ = v_str_136_;
v___y_124_ = v_val_140_;
v___y_125_ = v___x_146_;
goto v___jp_122_;
}
}
}
else
{
lean_dec(v_endPos_117_);
lean_dec_ref(v_pos_116_);
v_str_104_ = v_str_136_;
goto v___jp_103_;
}
}
v___jp_147_:
{
uint8_t v___x_149_; 
v___x_149_ = l_Lean_Message_isTrace(v_msg_87_);
lean_dec_ref(v_msg_87_);
if (v___x_149_ == 0)
{
switch(v_severity_118_)
{
case 0:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__4));
v___x_151_ = lean_string_append(v___x_150_, v_str_148_);
lean_dec_ref(v_str_148_);
v_str_136_ = v___x_151_;
goto v___jp_135_;
}
case 1:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__5));
v___x_153_ = lean_string_append(v___x_152_, v_str_148_);
lean_dec_ref(v_str_148_);
v_str_136_ = v___x_153_;
goto v___jp_135_;
}
default: 
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__6));
v___x_155_ = lean_string_append(v___x_154_, v_str_148_);
lean_dec_ref(v_str_148_);
v_str_136_ = v___x_155_;
goto v___jp_135_;
}
}
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__7));
v___x_157_ = lean_string_append(v___x_156_, v_str_148_);
lean_dec_ref(v_str_148_);
v_str_136_ = v___x_157_;
goto v___jp_135_;
}
}
v___jp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_161_ = lean_string_append(v___x_160_, v___y_159_);
lean_dec_ref(v___y_159_);
v_str_148_ = v___x_161_;
goto v___jp_147_;
}
v___jp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_165_ = lean_string_utf8_byte_size(v_str_163_);
v___x_166_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_167_ = lean_nat_dec_le(v___x_166_, v___x_165_);
if (v___x_167_ == 0)
{
v___y_159_ = v_str_163_;
goto v___jp_158_;
}
else
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_string_memcmp(v_str_163_, v___x_164_, v___x_168_, v___x_168_, v___x_166_);
if (v___x_169_ == 0)
{
v___y_159_ = v_str_163_;
goto v___jp_158_;
}
else
{
v_str_148_ = v_str_163_;
goto v___jp_147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___boxed(lean_object* v_msg_175_, lean_object* v_reportPos_x3f_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_msg_175_, v_reportPos_x3f_176_);
lean_dec(v_reportPos_x3f_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(uint8_t v_x_179_){
_start:
{
switch(v_x_179_)
{
case 0:
{
lean_object* v___x_180_; 
v___x_180_ = lean_unsigned_to_nat(0u);
return v___x_180_;
}
case 1:
{
lean_object* v___x_181_; 
v___x_181_ = lean_unsigned_to_nat(1u);
return v___x_181_;
}
default: 
{
lean_object* v___x_182_; 
v___x_182_ = lean_unsigned_to_nat(2u);
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___boxed(lean_object* v_x_183_){
_start:
{
uint8_t v_x_boxed_184_; lean_object* v_res_185_; 
v_x_boxed_184_ = lean_unbox(v_x_183_);
v_res_185_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(v_x_boxed_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(lean_object* v_k_186_){
_start:
{
lean_inc(v_k_186_);
return v_k_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg___boxed(lean_object* v_k_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(v_k_187_);
lean_dec(v_k_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(lean_object* v_motive_189_, lean_object* v_ctorIdx_190_, uint8_t v_t_191_, lean_object* v_h_192_, lean_object* v_k_193_){
_start:
{
lean_inc(v_k_193_);
return v_k_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___boxed(lean_object* v_motive_194_, lean_object* v_ctorIdx_195_, lean_object* v_t_196_, lean_object* v_h_197_, lean_object* v_k_198_){
_start:
{
uint8_t v_t_boxed_199_; lean_object* v_res_200_; 
v_t_boxed_199_ = lean_unbox(v_t_196_);
v_res_200_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(v_motive_194_, v_ctorIdx_195_, v_t_boxed_199_, v_h_197_, v_k_198_);
lean_dec(v_k_198_);
lean_dec(v_ctorIdx_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(lean_object* v_check_201_){
_start:
{
lean_inc(v_check_201_);
return v_check_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg___boxed(lean_object* v_check_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(v_check_202_);
lean_dec(v_check_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(lean_object* v_motive_204_, uint8_t v_t_205_, lean_object* v_h_206_, lean_object* v_check_207_){
_start:
{
lean_inc(v_check_207_);
return v_check_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___boxed(lean_object* v_motive_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_check_211_){
_start:
{
uint8_t v_t_boxed_212_; lean_object* v_res_213_; 
v_t_boxed_212_ = lean_unbox(v_t_209_);
v_res_213_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(v_motive_208_, v_t_boxed_212_, v_h_210_, v_check_211_);
lean_dec(v_check_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(lean_object* v_drop_214_){
_start:
{
lean_inc(v_drop_214_);
return v_drop_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg___boxed(lean_object* v_drop_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(v_drop_215_);
lean_dec(v_drop_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(lean_object* v_motive_217_, uint8_t v_t_218_, lean_object* v_h_219_, lean_object* v_drop_220_){
_start:
{
lean_inc(v_drop_220_);
return v_drop_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___boxed(lean_object* v_motive_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_drop_224_){
_start:
{
uint8_t v_t_boxed_225_; lean_object* v_res_226_; 
v_t_boxed_225_ = lean_unbox(v_t_222_);
v_res_226_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(v_motive_221_, v_t_boxed_225_, v_h_223_, v_drop_224_);
lean_dec(v_drop_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(lean_object* v_pass_227_){
_start:
{
lean_inc(v_pass_227_);
return v_pass_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg___boxed(lean_object* v_pass_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(v_pass_228_);
lean_dec(v_pass_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(lean_object* v_motive_230_, uint8_t v_t_231_, lean_object* v_h_232_, lean_object* v_pass_233_){
_start:
{
lean_inc(v_pass_233_);
return v_pass_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___boxed(lean_object* v_motive_234_, lean_object* v_t_235_, lean_object* v_h_236_, lean_object* v_pass_237_){
_start:
{
uint8_t v_t_boxed_238_; lean_object* v_res_239_; 
v_t_boxed_238_ = lean_unbox(v_t_235_);
v_res_239_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(v_motive_234_, v_t_boxed_238_, v_h_236_, v_pass_237_);
lean_dec(v_pass_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(uint8_t v_x_240_){
_start:
{
switch(v_x_240_)
{
case 0:
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(0u);
return v___x_241_;
}
case 1:
{
lean_object* v___x_242_; 
v___x_242_ = lean_unsigned_to_nat(1u);
return v___x_242_;
}
default: 
{
lean_object* v___x_243_; 
v___x_243_ = lean_unsigned_to_nat(2u);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___boxed(lean_object* v_x_244_){
_start:
{
uint8_t v_x_boxed_245_; lean_object* v_res_246_; 
v_x_boxed_245_ = lean_unbox(v_x_244_);
v_res_246_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(v_x_boxed_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(lean_object* v_k_247_){
_start:
{
lean_inc(v_k_247_);
return v_k_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg___boxed(lean_object* v_k_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(v_k_248_);
lean_dec(v_k_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(lean_object* v_motive_250_, lean_object* v_ctorIdx_251_, uint8_t v_t_252_, lean_object* v_h_253_, lean_object* v_k_254_){
_start:
{
lean_inc(v_k_254_);
return v_k_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___boxed(lean_object* v_motive_255_, lean_object* v_ctorIdx_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_k_259_){
_start:
{
uint8_t v_t_boxed_260_; lean_object* v_res_261_; 
v_t_boxed_260_ = lean_unbox(v_t_257_);
v_res_261_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(v_motive_255_, v_ctorIdx_256_, v_t_boxed_260_, v_h_258_, v_k_259_);
lean_dec(v_k_259_);
lean_dec(v_ctorIdx_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(lean_object* v_exact_262_){
_start:
{
lean_inc(v_exact_262_);
return v_exact_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg___boxed(lean_object* v_exact_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(v_exact_263_);
lean_dec(v_exact_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(lean_object* v_motive_265_, uint8_t v_t_266_, lean_object* v_h_267_, lean_object* v_exact_268_){
_start:
{
lean_inc(v_exact_268_);
return v_exact_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___boxed(lean_object* v_motive_269_, lean_object* v_t_270_, lean_object* v_h_271_, lean_object* v_exact_272_){
_start:
{
uint8_t v_t_boxed_273_; lean_object* v_res_274_; 
v_t_boxed_273_ = lean_unbox(v_t_270_);
v_res_274_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(v_motive_269_, v_t_boxed_273_, v_h_271_, v_exact_272_);
lean_dec(v_exact_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(lean_object* v_normalized_275_){
_start:
{
lean_inc(v_normalized_275_);
return v_normalized_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg___boxed(lean_object* v_normalized_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(v_normalized_276_);
lean_dec(v_normalized_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(lean_object* v_motive_278_, uint8_t v_t_279_, lean_object* v_h_280_, lean_object* v_normalized_281_){
_start:
{
lean_inc(v_normalized_281_);
return v_normalized_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___boxed(lean_object* v_motive_282_, lean_object* v_t_283_, lean_object* v_h_284_, lean_object* v_normalized_285_){
_start:
{
uint8_t v_t_boxed_286_; lean_object* v_res_287_; 
v_t_boxed_286_ = lean_unbox(v_t_283_);
v_res_287_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(v_motive_282_, v_t_boxed_286_, v_h_284_, v_normalized_285_);
lean_dec(v_normalized_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(lean_object* v_lax_288_){
_start:
{
lean_inc(v_lax_288_);
return v_lax_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg___boxed(lean_object* v_lax_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(v_lax_289_);
lean_dec(v_lax_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(lean_object* v_motive_291_, uint8_t v_t_292_, lean_object* v_h_293_, lean_object* v_lax_294_){
_start:
{
lean_inc(v_lax_294_);
return v_lax_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___boxed(lean_object* v_motive_295_, lean_object* v_t_296_, lean_object* v_h_297_, lean_object* v_lax_298_){
_start:
{
uint8_t v_t_boxed_299_; lean_object* v_res_300_; 
v_t_boxed_299_ = lean_unbox(v_t_296_);
v_res_300_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(v_motive_295_, v_t_boxed_299_, v_h_297_, v_lax_298_);
lean_dec(v_lax_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(uint8_t v_x_301_){
_start:
{
if (v_x_301_ == 0)
{
lean_object* v___x_302_; 
v___x_302_ = lean_unsigned_to_nat(0u);
return v___x_302_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_unsigned_to_nat(1u);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___boxed(lean_object* v_x_304_){
_start:
{
uint8_t v_x_boxed_305_; lean_object* v_res_306_; 
v_x_boxed_305_ = lean_unbox(v_x_304_);
v_res_306_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(v_x_boxed_305_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(lean_object* v_k_307_){
_start:
{
lean_inc(v_k_307_);
return v_k_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg___boxed(lean_object* v_k_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(v_k_308_);
lean_dec(v_k_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(lean_object* v_motive_310_, lean_object* v_ctorIdx_311_, uint8_t v_t_312_, lean_object* v_h_313_, lean_object* v_k_314_){
_start:
{
lean_inc(v_k_314_);
return v_k_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___boxed(lean_object* v_motive_315_, lean_object* v_ctorIdx_316_, lean_object* v_t_317_, lean_object* v_h_318_, lean_object* v_k_319_){
_start:
{
uint8_t v_t_boxed_320_; lean_object* v_res_321_; 
v_t_boxed_320_ = lean_unbox(v_t_317_);
v_res_321_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(v_motive_315_, v_ctorIdx_316_, v_t_boxed_320_, v_h_318_, v_k_319_);
lean_dec(v_k_319_);
lean_dec(v_ctorIdx_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(lean_object* v_exact_322_){
_start:
{
lean_inc(v_exact_322_);
return v_exact_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg___boxed(lean_object* v_exact_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(v_exact_323_);
lean_dec(v_exact_323_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(lean_object* v_motive_325_, uint8_t v_t_326_, lean_object* v_h_327_, lean_object* v_exact_328_){
_start:
{
lean_inc(v_exact_328_);
return v_exact_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___boxed(lean_object* v_motive_329_, lean_object* v_t_330_, lean_object* v_h_331_, lean_object* v_exact_332_){
_start:
{
uint8_t v_t_boxed_333_; lean_object* v_res_334_; 
v_t_boxed_333_ = lean_unbox(v_t_330_);
v_res_334_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(v_motive_329_, v_t_boxed_333_, v_h_331_, v_exact_332_);
lean_dec(v_exact_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(lean_object* v_sorted_335_){
_start:
{
lean_inc(v_sorted_335_);
return v_sorted_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg___boxed(lean_object* v_sorted_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(v_sorted_336_);
lean_dec(v_sorted_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(lean_object* v_motive_338_, uint8_t v_t_339_, lean_object* v_h_340_, lean_object* v_sorted_341_){
_start:
{
lean_inc(v_sorted_341_);
return v_sorted_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___boxed(lean_object* v_motive_342_, lean_object* v_t_343_, lean_object* v_h_344_, lean_object* v_sorted_345_){
_start:
{
uint8_t v_t_boxed_346_; lean_object* v_res_347_; 
v_t_boxed_346_ = lean_unbox(v_t_343_);
v_res_347_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(v_motive_342_, v_t_boxed_346_, v_h_344_, v_sorted_345_);
lean_dec(v_sorted_345_);
return v_res_347_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_box(0);
v___x_349_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg(){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___boxed(lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(lean_object* v_00_u03b1_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___boxed(lean_object* v_00_u03b1_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(v_00_u03b1_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(lean_object* v_action_x3f_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
if (lean_obj_tag(v_action_x3f_383_) == 1)
{
lean_object* v_val_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_418_; 
v_val_387_ = lean_ctor_get(v_action_x3f_383_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v_action_x3f_383_);
if (v_isSharedCheck_418_ == 0)
{
v___x_389_ = v_action_x3f_383_;
v_isShared_390_ = v_isSharedCheck_418_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_val_387_);
lean_dec(v_action_x3f_383_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_418_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1));
lean_inc(v_val_387_);
v___x_392_ = l_Lean_Syntax_isOfKind(v_val_387_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_del_object(v___x_389_);
lean_dec(v_val_387_);
v___x_393_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_393_;
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = l_Lean_Syntax_getArg(v_val_387_, v___x_394_);
lean_dec(v_val_387_);
v___x_396_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4));
lean_inc(v___x_395_);
v___x_397_ = l_Lean_Syntax_isOfKind(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6));
lean_inc(v___x_395_);
v___x_399_ = l_Lean_Syntax_isOfKind(v___x_395_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8));
v___x_401_ = l_Lean_Syntax_isOfKind(v___x_395_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_del_object(v___x_389_);
v___x_402_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_402_;
}
else
{
uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = 2;
v___x_404_ = lean_box(v___x_403_);
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 0);
lean_ctor_set(v___x_389_, 0, v___x_404_);
v___x_406_ = v___x_389_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
lean_dec(v___x_395_);
v___x_408_ = 1;
v___x_409_ = lean_box(v___x_408_);
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 0);
lean_ctor_set(v___x_389_, 0, v___x_409_);
v___x_411_ = v___x_389_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
else
{
uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
lean_dec(v___x_395_);
v___x_413_ = 0;
v___x_414_ = lean_box(v___x_413_);
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 0);
lean_ctor_set(v___x_389_, 0, v___x_414_);
v___x_416_ = v___x_389_;
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
}
}
else
{
uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_action_x3f_383_);
v___x_419_ = 0;
v___x_420_ = lean_box(v___x_419_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___boxed(lean_object* v_action_x3f_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
return v_res_426_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(uint8_t v___x_427_, lean_object* v_x_428_){
_start:
{
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed(lean_object* v___x_429_, lean_object* v_x_430_){
_start:
{
uint8_t v___x_1582__boxed_431_; uint8_t v_res_432_; lean_object* v_r_433_; 
v___x_1582__boxed_431_ = lean_unbox(v___x_429_);
v_res_432_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_1582__boxed_431_, v_x_430_);
lean_dec_ref(v_x_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(uint8_t v___x_434_, lean_object* v_msg_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_Lean_Message_isTrace(v_msg_435_);
if (v___x_436_ == 0)
{
uint8_t v_severity_437_; uint8_t v___x_438_; uint8_t v___x_439_; 
v_severity_437_ = lean_ctor_get_uint8(v_msg_435_, sizeof(void*)*5 + 1);
v___x_438_ = 2;
v___x_439_ = l_Lean_instBEqMessageSeverity_beq(v_severity_437_, v___x_438_);
return v___x_439_;
}
else
{
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object* v___x_440_, lean_object* v_msg_441_){
_start:
{
uint8_t v___x_1588__boxed_442_; uint8_t v_res_443_; lean_object* v_r_444_; 
v___x_1588__boxed_442_ = lean_unbox(v___x_440_);
v_res_443_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_1588__boxed_442_, v_msg_441_);
lean_dec_ref(v_msg_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(uint8_t v___x_445_, lean_object* v_msg_446_){
_start:
{
uint8_t v___x_447_; 
v___x_447_ = l_Lean_Message_isTrace(v_msg_446_);
if (v___x_447_ == 0)
{
uint8_t v_severity_448_; uint8_t v___x_449_; uint8_t v___x_450_; 
v_severity_448_ = lean_ctor_get_uint8(v_msg_446_, sizeof(void*)*5 + 1);
v___x_449_ = 1;
v___x_450_ = l_Lean_instBEqMessageSeverity_beq(v_severity_448_, v___x_449_);
return v___x_450_;
}
else
{
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object* v___x_451_, lean_object* v_msg_452_){
_start:
{
uint8_t v___x_1597__boxed_453_; uint8_t v_res_454_; lean_object* v_r_455_; 
v___x_1597__boxed_453_ = lean_unbox(v___x_451_);
v_res_454_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_1597__boxed_453_, v_msg_452_);
lean_dec_ref(v_msg_452_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(uint8_t v___x_456_, lean_object* v_msg_457_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = l_Lean_Message_isTrace(v_msg_457_);
if (v___x_458_ == 0)
{
uint8_t v_severity_459_; uint8_t v___x_460_; uint8_t v___x_461_; 
v_severity_459_ = lean_ctor_get_uint8(v_msg_457_, sizeof(void*)*5 + 1);
v___x_460_ = 0;
v___x_461_ = l_Lean_instBEqMessageSeverity_beq(v_severity_459_, v___x_460_);
return v___x_461_;
}
else
{
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object* v___x_462_, lean_object* v_msg_463_){
_start:
{
uint8_t v___x_1606__boxed_464_; uint8_t v_res_465_; lean_object* v_r_466_; 
v___x_1606__boxed_464_ = lean_unbox(v___x_462_);
v_res_465_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_1606__boxed_464_, v_msg_463_);
lean_dec_ref(v_msg_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(lean_object* v_x_492_){
_start:
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1));
lean_inc(v_x_492_);
v___x_495_ = l_Lean_Syntax_isOfKind(v_x_492_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
lean_dec(v_x_492_);
v___x_496_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_496_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = l_Lean_Syntax_getArg(v_x_492_, v___x_497_);
lean_dec(v_x_492_);
v___x_499_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3));
lean_inc(v___x_498_);
v___x_500_ = l_Lean_Syntax_isOfKind(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5));
lean_inc(v___x_498_);
v___x_502_ = l_Lean_Syntax_isOfKind(v___x_498_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7));
lean_inc(v___x_498_);
v___x_504_ = l_Lean_Syntax_isOfKind(v___x_498_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9));
lean_inc(v___x_498_);
v___x_506_ = l_Lean_Syntax_isOfKind(v___x_498_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11));
v___x_508_ = l_Lean_Syntax_isOfKind(v___x_498_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v___f_511_; lean_object* v___x_512_; 
v___x_510_ = lean_box(v___x_508_);
v___f_511_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_511_, 0, v___x_510_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___f_511_);
return v___x_512_;
}
}
else
{
lean_object* v___x_513_; lean_object* v___f_514_; lean_object* v___x_515_; 
lean_dec(v___x_498_);
v___x_513_ = lean_box(v___x_504_);
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_514_, 0, v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___f_514_);
return v___x_515_;
}
}
else
{
lean_object* v___x_516_; lean_object* v___f_517_; lean_object* v___x_518_; 
lean_dec(v___x_498_);
v___x_516_ = lean_box(v___x_502_);
v___f_517_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_517_, 0, v___x_516_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___f_517_);
return v___x_518_;
}
}
else
{
lean_object* v___x_519_; lean_object* v___f_520_; lean_object* v___x_521_; 
lean_dec(v___x_498_);
v___x_519_ = lean_box(v___x_500_);
v___f_520_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_520_, 0, v___x_519_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___f_520_);
return v___x_521_;
}
}
else
{
lean_object* v___f_522_; lean_object* v___x_523_; 
lean_dec(v___x_498_);
v___f_522_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12));
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___f_522_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___boxed(lean_object* v_x_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(lean_object* v_x_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_527_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___boxed(lean_object* v_x_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(v_x_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
return v_res_536_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object* v_x_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = 0;
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object* v_x_539_){
_start:
{
uint8_t v_res_540_; lean_object* v_r_541_; 
v_res_540_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(v_x_539_);
lean_dec_ref(v_x_539_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(lean_object* v_snd_542_, lean_object* v___y_543_){
_start:
{
if (lean_obj_tag(v_snd_542_) == 0)
{
uint8_t v___x_544_; 
lean_dec_ref(v___y_543_);
v___x_544_ = 0;
return v___x_544_;
}
else
{
lean_object* v_val_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_val_545_ = lean_ctor_get(v_snd_542_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v_snd_542_, 1);
v___x_546_ = lean_apply_1(v_val_545_, v___y_543_);
v___x_547_ = lean_unbox(v___x_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed(lean_object* v_snd_548_, lean_object* v___y_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(v_snd_548_, v___y_549_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(lean_object* v_a_552_, lean_object* v_snd_553_, uint8_t v_a_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_556_; uint8_t v___x_557_; 
lean_inc_ref(v___y_555_);
v___x_556_ = lean_apply_1(v_a_552_, v___y_555_);
v___x_557_ = lean_unbox(v___x_556_);
if (v___x_557_ == 0)
{
if (lean_obj_tag(v_snd_553_) == 0)
{
uint8_t v___x_558_; 
lean_dec_ref(v___y_555_);
v___x_558_ = 2;
return v___x_558_;
}
else
{
lean_object* v_val_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_val_559_ = lean_ctor_get(v_snd_553_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v_snd_553_, 1);
v___x_560_ = lean_apply_1(v_val_559_, v___y_555_);
v___x_561_ = lean_unbox(v___x_560_);
return v___x_561_;
}
}
else
{
lean_dec_ref(v___y_555_);
lean_dec(v_snd_553_);
return v_a_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed(lean_object* v_a_562_, lean_object* v_snd_563_, lean_object* v_a_564_, lean_object* v___y_565_){
_start:
{
uint8_t v_a_11568__boxed_566_; uint8_t v_res_567_; lean_object* v_r_568_; 
v_a_11568__boxed_566_ = lean_unbox(v_a_564_);
v_res_567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_562_, v_snd_563_, v_a_11568__boxed_566_, v___y_565_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object* v_as_629_, size_t v_sz_630_, size_t v_i_631_, lean_object* v_b_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_a_637_; uint8_t v___x_641_; 
v___x_641_ = lean_usize_dec_lt(v_i_631_, v_sz_630_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v_b_632_);
return v___x_642_;
}
else
{
lean_object* v_snd_643_; lean_object* v_snd_644_; lean_object* v_snd_645_; lean_object* v_fst_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_953_; 
v_snd_643_ = lean_ctor_get(v_b_632_, 1);
lean_inc(v_snd_643_);
v_snd_644_ = lean_ctor_get(v_snd_643_, 1);
lean_inc(v_snd_644_);
v_snd_645_ = lean_ctor_get(v_snd_644_, 1);
lean_inc(v_snd_645_);
v_fst_646_ = lean_ctor_get(v_b_632_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v_b_632_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v_b_632_, 1);
lean_dec(v_unused_954_);
v___x_648_ = v_b_632_;
v_isShared_649_ = v_isSharedCheck_953_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_fst_646_);
lean_dec(v_b_632_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_953_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_fst_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_951_; 
v_fst_650_ = lean_ctor_get(v_snd_643_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v_snd_643_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v_snd_643_, 1);
lean_dec(v_unused_952_);
v___x_652_ = v_snd_643_;
v_isShared_653_ = v_isSharedCheck_951_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_fst_650_);
lean_dec(v_snd_643_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_951_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_fst_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_949_; 
v_fst_654_ = lean_ctor_get(v_snd_644_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_snd_644_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v_snd_644_, 1);
lean_dec(v_unused_950_);
v___x_656_ = v_snd_644_;
v_isShared_657_ = v_isSharedCheck_949_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_fst_654_);
lean_dec(v_snd_644_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_949_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_fst_658_; lean_object* v_snd_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_948_; 
v_fst_658_ = lean_ctor_get(v_snd_645_, 0);
v_snd_659_ = lean_ctor_get(v_snd_645_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_snd_645_);
if (v_isSharedCheck_948_ == 0)
{
v___x_661_ = v_snd_645_;
v_isShared_662_ = v_isSharedCheck_948_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_snd_659_);
lean_inc(v_fst_658_);
lean_dec(v_snd_645_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_948_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_a_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_a_663_ = lean_array_uget_borrowed(v_as_629_, v_i_631_);
v___x_664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_a_663_);
v___x_665_ = l_Lean_Syntax_isOfKind(v_a_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_668_; 
lean_dec_ref_known(v___x_666_, 1);
if (v_isShared_662_ == 0)
{
v___x_668_ = v___x_661_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_fst_658_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_snd_659_);
v___x_668_ = v_reuseFailAlloc_678_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_670_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v___x_668_);
v___x_670_ = v___x_656_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_fst_654_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_668_);
v___x_670_ = v_reuseFailAlloc_677_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_672_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_670_);
v___x_672_ = v___x_652_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_fst_650_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_670_);
v___x_672_ = v_reuseFailAlloc_676_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_674_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___x_672_);
v___x_674_ = v___x_648_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_fst_646_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
v_a_637_ = v___x_674_;
goto v___jp_636_;
}
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_del_object(v___x_661_);
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_del_object(v___x_656_);
lean_dec(v_fst_654_);
lean_del_object(v___x_652_);
lean_dec(v_fst_650_);
lean_del_object(v___x_648_);
lean_dec(v_fst_646_);
v_a_679_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_666_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_666_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_action_x3f_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = l_Lean_Syntax_getArg(v_a_663_, v___x_687_);
v___x_729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3));
lean_inc(v___x_688_);
v___x_730_ = l_Lean_Syntax_isOfKind(v___x_688_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; uint8_t v___x_732_; 
lean_del_object(v___x_661_);
lean_del_object(v___x_656_);
lean_del_object(v___x_652_);
lean_del_object(v___x_648_);
v___x_731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5));
lean_inc(v___x_688_);
v___x_732_ = l_Lean_Syntax_isOfKind(v___x_688_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; uint8_t v_reportPositions_734_; 
v___x_733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7));
lean_inc(v___x_688_);
v_reportPositions_734_ = l_Lean_Syntax_isOfKind(v___x_688_, v___x_733_);
if (v_reportPositions_734_ == 0)
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9));
lean_inc(v___x_688_);
v___x_736_ = l_Lean_Syntax_isOfKind(v___x_688_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11));
lean_inc(v___x_688_);
v___x_738_ = l_Lean_Syntax_isOfKind(v___x_688_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
lean_dec(v___x_688_);
v___x_739_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec_ref_known(v___x_739_, 1);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_fst_658_);
lean_ctor_set(v___x_740_, 1, v_snd_659_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_fst_654_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v_fst_650_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v_fst_646_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v_a_637_ = v___x_743_;
goto v___jp_636_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_dec(v_fst_654_);
lean_dec(v_fst_650_);
lean_dec(v_fst_646_);
v_a_744_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_739_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_739_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_752_ = lean_unsigned_to_nat(2u);
v___x_753_ = l_Lean_Syntax_getArg(v___x_688_, v___x_752_);
lean_dec(v___x_688_);
v___x_754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_753_);
v___x_755_ = l_Lean_Syntax_isOfKind(v___x_753_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_757_ = l_Lean_Syntax_isOfKind(v___x_753_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec_ref_known(v___x_758_, 1);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_fst_658_);
lean_ctor_set(v___x_759_, 1, v_snd_659_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v_fst_654_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v_fst_650_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v_fst_646_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v_a_637_ = v___x_762_;
goto v___jp_636_;
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_dec(v_fst_654_);
lean_dec(v_fst_650_);
lean_dec(v_fst_646_);
v_a_763_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_758_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_758_);
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
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v_fst_658_);
v___x_771_ = lean_box(v_reportPositions_734_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v_snd_659_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_fst_654_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_fst_650_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_fst_646_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v_a_637_ = v___x_775_;
goto v___jp_636_;
}
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec(v___x_753_);
lean_dec(v_fst_658_);
v___x_776_ = lean_box(v___x_665_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v_snd_659_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v_fst_654_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_fst_650_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_fst_646_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v_a_637_ = v___x_780_;
goto v___jp_636_;
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_781_ = lean_unsigned_to_nat(2u);
v___x_782_ = l_Lean_Syntax_getArg(v___x_688_, v___x_781_);
lean_dec(v___x_688_);
v___x_783_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17));
lean_inc(v___x_782_);
v___x_784_ = l_Lean_Syntax_isOfKind(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v___x_782_);
v___x_785_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec_ref_known(v___x_785_, 1);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_fst_658_);
lean_ctor_set(v___x_786_, 1, v_snd_659_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_fst_654_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_fst_650_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_fst_646_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v_a_637_ = v___x_789_;
goto v___jp_636_;
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_dec(v_fst_654_);
lean_dec(v_fst_650_);
lean_dec(v_fst_646_);
v_a_790_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_785_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_785_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_798_ = l_Lean_Syntax_getArg(v___x_782_, v___x_687_);
lean_dec(v___x_782_);
v___x_799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_798_);
v___x_800_ = l_Lean_Syntax_isOfKind(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_801_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_802_ = l_Lean_Syntax_isOfKind(v___x_798_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec_ref_known(v___x_803_, 1);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_fst_658_);
lean_ctor_set(v___x_804_, 1, v_snd_659_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v_fst_654_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_fst_650_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_fst_646_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v_a_637_ = v___x_807_;
goto v___jp_636_;
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_dec(v_fst_654_);
lean_dec(v_fst_650_);
lean_dec(v_fst_646_);
v_a_808_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_803_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_803_);
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
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec(v_fst_654_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_fst_658_);
lean_ctor_set(v___x_816_, 1, v_snd_659_);
v___x_817_ = lean_box(v_reportPositions_734_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v___x_816_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_fst_650_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_fst_646_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v_a_637_ = v___x_820_;
goto v___jp_636_;
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec(v___x_798_);
lean_dec(v_fst_654_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_fst_658_);
lean_ctor_set(v___x_821_, 1, v_snd_659_);
v___x_822_ = lean_box(v___x_665_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_821_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_fst_650_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_fst_646_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v_a_637_ = v___x_825_;
goto v___jp_636_;
}
}
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_826_ = lean_unsigned_to_nat(2u);
v___x_827_ = l_Lean_Syntax_getArg(v___x_688_, v___x_826_);
lean_dec(v___x_688_);
v___x_828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19));
lean_inc(v___x_827_);
v___x_829_ = l_Lean_Syntax_isOfKind(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
lean_dec(v___x_827_);
v___x_830_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec_ref_known(v___x_830_, 1);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_fst_658_);
lean_ctor_set(v___x_831_, 1, v_snd_659_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_fst_654_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_fst_650_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_fst_646_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v_a_637_ = v___x_834_;
goto v___jp_636_;
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_dec(v_fst_654_);
lean_dec(v_fst_650_);
lean_dec(v_fst_646_);
v_a_835_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_830_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_830_);
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
else
{
lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_843_ = l_Lean_Syntax_getArg(v___x_827_, v___x_687_);
lean_dec(v___x_827_);
v___x_844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_843_);
v___x_845_ = l_Lean_Syntax_isOfKind(v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23));
v___x_847_ = l_Lean_Syntax_isOfKind(v___x_843_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec_ref_known(v___x_848_, 1);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_fst_658_);
lean_ctor_set(v___x_849_, 1, v_snd_659_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_fst_654_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v_fst_650_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v_fst_646_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v_a_637_ = v___x_852_;
goto v___jp_636_;
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_dec(v_fst_654_);
lean_dec(v_fst_650_);
lean_dec(v_fst_646_);
v_a_853_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_848_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_848_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
else
{
uint8_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec(v_fst_650_);
v___x_861_ = 1;
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_fst_658_);
lean_ctor_set(v___x_862_, 1, v_snd_659_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_fst_654_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_box(v___x_861_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_863_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v_fst_646_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v_a_637_ = v___x_866_;
goto v___jp_636_;
}
}
else
{
uint8_t v_ordering_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v___x_843_);
lean_dec(v_fst_650_);
v_ordering_867_ = 0;
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v_fst_658_);
lean_ctor_set(v___x_868_, 1, v_snd_659_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v_fst_654_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_box(v_ordering_867_);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_869_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_fst_646_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v_a_637_ = v___x_872_;
goto v___jp_636_;
}
}
}
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_873_ = lean_unsigned_to_nat(2u);
v___x_874_ = l_Lean_Syntax_getArg(v___x_688_, v___x_873_);
lean_dec(v___x_688_);
v___x_875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25));
lean_inc(v___x_874_);
v___x_876_ = l_Lean_Syntax_isOfKind(v___x_874_, v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; 
lean_dec(v___x_874_);
v___x_877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec_ref_known(v___x_877_, 1);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_fst_658_);
lean_ctor_set(v___x_878_, 1, v_snd_659_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_fst_654_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_fst_650_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v_fst_646_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v_a_637_ = v___x_881_;
goto v___jp_636_;
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_dec(v_fst_654_);
lean_dec(v_fst_650_);
lean_dec(v_fst_646_);
v_a_882_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_877_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_877_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_890_ = l_Lean_Syntax_getArg(v___x_874_, v___x_687_);
lean_dec(v___x_874_);
v___x_891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_890_);
v___x_892_ = l_Lean_Syntax_isOfKind(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27));
lean_inc(v___x_890_);
v___x_894_ = l_Lean_Syntax_isOfKind(v___x_890_, v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29));
v___x_896_ = l_Lean_Syntax_isOfKind(v___x_890_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec_ref_known(v___x_897_, 1);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v_fst_658_);
lean_ctor_set(v___x_898_, 1, v_snd_659_);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v_fst_654_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v_fst_650_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v_fst_646_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v_a_637_ = v___x_901_;
goto v___jp_636_;
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_dec(v_fst_654_);
lean_dec(v_fst_650_);
lean_dec(v_fst_646_);
v_a_902_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_897_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_897_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec(v_fst_646_);
v___x_910_ = 2;
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_fst_658_);
lean_ctor_set(v___x_911_, 1, v_snd_659_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_fst_654_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_fst_650_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_box(v___x_910_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_913_);
v_a_637_ = v___x_915_;
goto v___jp_636_;
}
}
else
{
uint8_t v_whitespace_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
lean_dec(v___x_890_);
lean_dec(v_fst_646_);
v_whitespace_916_ = 1;
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_fst_658_);
lean_ctor_set(v___x_917_, 1, v_snd_659_);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v_fst_654_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_fst_650_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_box(v_whitespace_916_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_919_);
v_a_637_ = v___x_921_;
goto v___jp_636_;
}
}
else
{
uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v___x_890_);
lean_dec(v_fst_646_);
v___x_922_ = 0;
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_fst_658_);
lean_ctor_set(v___x_923_, 1, v_snd_659_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v_fst_654_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_fst_650_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_box(v___x_922_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_925_);
v_a_637_ = v___x_927_;
goto v___jp_636_;
}
}
}
}
else
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = l_Lean_Syntax_getArg(v___x_688_, v___x_687_);
v___x_929_ = l_Lean_Syntax_isNone(v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_928_);
v___x_931_ = l_Lean_Syntax_matchesNull(v___x_928_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec(v___x_928_);
lean_dec(v___x_688_);
lean_del_object(v___x_661_);
lean_del_object(v___x_656_);
lean_del_object(v___x_652_);
lean_del_object(v___x_648_);
v___x_932_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec_ref_known(v___x_932_, 1);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_fst_658_);
lean_ctor_set(v___x_933_, 1, v_snd_659_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_fst_654_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v_fst_650_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_fst_646_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v_a_637_ = v___x_936_;
goto v___jp_636_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_dec(v_fst_654_);
lean_dec(v_fst_650_);
lean_dec(v_fst_646_);
v_a_937_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_932_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_932_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = l_Lean_Syntax_getArg(v___x_928_, v___x_687_);
lean_dec(v___x_928_);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
v_action_x3f_690_ = v___x_946_;
v___y_691_ = v___y_633_;
v___y_692_ = v___y_634_;
goto v___jp_689_;
}
}
else
{
lean_object* v___x_947_; 
lean_dec(v___x_928_);
v___x_947_ = lean_box(0);
v_action_x3f_690_ = v___x_947_;
v___y_691_ = v___y_633_;
v___y_692_ = v___y_634_;
goto v___jp_689_;
}
}
v___jp_689_:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = l_Lean_Syntax_getArg(v___x_688_, v___x_695_);
lean_dec(v___x_688_);
v___x_697_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v___x_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___f_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___f_699_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_699_, 0, v_a_698_);
lean_closure_set(v___f_699_, 1, v_snd_659_);
lean_closure_set(v___f_699_, 2, v_a_694_);
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v___f_699_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_700_);
v___x_702_ = v___x_661_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_fst_658_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_712_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v___x_702_);
v___x_704_ = v___x_656_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_fst_654_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_702_);
v___x_704_ = v_reuseFailAlloc_711_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_704_);
v___x_706_ = v___x_652_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_fst_650_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___x_706_);
v___x_708_ = v___x_648_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_fst_646_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
v_a_637_ = v___x_708_;
goto v___jp_636_;
}
}
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_a_694_);
lean_del_object(v___x_661_);
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_del_object(v___x_656_);
lean_dec(v_fst_654_);
lean_del_object(v___x_652_);
lean_dec(v_fst_650_);
lean_del_object(v___x_648_);
lean_dec(v_fst_646_);
v_a_713_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_697_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_697_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec(v___x_688_);
lean_del_object(v___x_661_);
lean_dec(v_snd_659_);
lean_dec(v_fst_658_);
lean_del_object(v___x_656_);
lean_dec(v_fst_654_);
lean_del_object(v___x_652_);
lean_dec(v_fst_650_);
lean_del_object(v___x_648_);
lean_dec(v_fst_646_);
v_a_721_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_693_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_693_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
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
v___jp_636_:
{
size_t v___x_638_; size_t v___x_639_; 
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_add(v_i_631_, v___x_638_);
v_i_631_ = v___x_639_;
v_b_632_ = v_a_637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object* v_as_955_, lean_object* v_sz_956_, lean_object* v_i_957_, lean_object* v_b_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
size_t v_sz_boxed_962_; size_t v_i_boxed_963_; lean_object* v_res_964_; 
v_sz_boxed_962_ = lean_unbox_usize(v_sz_956_);
lean_dec(v_sz_956_);
v_i_boxed_963_ = lean_unbox_usize(v_i_957_);
lean_dec(v_i_957_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v_as_955_, v_sz_boxed_962_, v_i_boxed_963_, v_b_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec_ref(v_as_955_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(size_t v_sz_965_, size_t v_i_966_, lean_object* v_bs_967_){
_start:
{
uint8_t v___x_968_; 
v___x_968_ = lean_usize_dec_lt(v_i_966_, v_sz_965_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v_bs_967_);
return v___x_969_;
}
else
{
lean_object* v_v_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v_v_970_ = lean_array_uget(v_bs_967_, v_i_966_);
v___x_971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_v_970_);
v___x_972_ = l_Lean_Syntax_isOfKind(v_v_970_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; 
lean_dec(v_v_970_);
lean_dec_ref(v_bs_967_);
v___x_973_ = lean_box(0);
return v___x_973_;
}
else
{
lean_object* v___x_974_; lean_object* v_bs_x27_975_; size_t v___x_976_; size_t v___x_977_; lean_object* v___x_978_; 
v___x_974_ = lean_unsigned_to_nat(0u);
v_bs_x27_975_ = lean_array_uset(v_bs_967_, v_i_966_, v___x_974_);
v___x_976_ = ((size_t)1ULL);
v___x_977_ = lean_usize_add(v_i_966_, v___x_976_);
v___x_978_ = lean_array_uset(v_bs_x27_975_, v_i_966_, v_v_970_);
v_i_966_ = v___x_977_;
v_bs_967_ = v___x_978_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1___boxed(lean_object* v_sz_980_, lean_object* v_i_981_, lean_object* v_bs_982_){
_start:
{
size_t v_sz_boxed_983_; size_t v_i_boxed_984_; lean_object* v_res_985_; 
v_sz_boxed_983_ = lean_unbox_usize(v_sz_980_);
lean_dec(v_sz_980_);
v_i_boxed_984_ = lean_unbox_usize(v_i_981_);
lean_dec(v_i_981_);
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_boxed_983_, v_i_boxed_984_, v_bs_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(uint8_t v___x_986_, lean_object* v_as_987_, size_t v_i_988_, size_t v_stop_989_, lean_object* v_b_990_){
_start:
{
lean_object* v___y_992_; uint8_t v___x_996_; 
v___x_996_ = lean_usize_dec_eq(v_i_988_, v_stop_989_);
if (v___x_996_ == 0)
{
lean_object* v_fst_997_; uint8_t v___x_998_; 
v_fst_997_ = lean_ctor_get(v_b_990_, 0);
v___x_998_ = lean_unbox(v_fst_997_);
if (v___x_998_ == 0)
{
lean_object* v_snd_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1007_; 
v_snd_999_ = lean_ctor_get(v_b_990_, 1);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_b_990_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; 
v_unused_1008_ = lean_ctor_get(v_b_990_, 0);
lean_dec(v_unused_1008_);
v___x_1001_ = v_b_990_;
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snd_999_);
lean_dec(v_b_990_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_box(v___x_986_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_snd_999_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v___y_992_ = v___x_1005_;
goto v___jp_991_;
}
}
}
else
{
lean_object* v_snd_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1019_; 
v_snd_1009_ = lean_ctor_get(v_b_990_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_b_990_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; 
v_unused_1020_ = lean_ctor_get(v_b_990_, 0);
lean_dec(v_unused_1020_);
v___x_1011_ = v_b_990_;
v_isShared_1012_ = v_isSharedCheck_1019_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_snd_1009_);
lean_dec(v_b_990_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1019_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1013_ = lean_array_uget_borrowed(v_as_987_, v_i_988_);
lean_inc(v___x_1013_);
v___x_1014_ = lean_array_push(v_snd_1009_, v___x_1013_);
v___x_1015_ = lean_box(v___x_996_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v___x_1014_);
lean_ctor_set(v___x_1011_, 0, v___x_1015_);
v___x_1017_ = v___x_1011_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v___x_1014_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
v___y_992_ = v___x_1017_;
goto v___jp_991_;
}
}
}
}
else
{
return v_b_990_;
}
v___jp_991_:
{
size_t v___x_993_; size_t v___x_994_; 
v___x_993_ = ((size_t)1ULL);
v___x_994_ = lean_usize_add(v_i_988_, v___x_993_);
v_i_988_ = v___x_994_;
v_b_990_ = v___y_992_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object* v___x_1021_, lean_object* v_as_1022_, lean_object* v_i_1023_, lean_object* v_stop_1024_, lean_object* v_b_1025_){
_start:
{
uint8_t v___x_12443__boxed_1026_; size_t v_i_boxed_1027_; size_t v_stop_boxed_1028_; lean_object* v_res_1029_; 
v___x_12443__boxed_1026_ = lean_unbox(v___x_1021_);
v_i_boxed_1027_ = lean_unbox_usize(v_i_1023_);
lean_dec(v_i_1023_);
v_stop_boxed_1028_ = lean_unbox_usize(v_stop_1024_);
lean_dec(v_stop_1024_);
v_res_1029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_12443__boxed_1026_, v_as_1022_, v_i_boxed_1027_, v_stop_boxed_1028_, v_b_1025_);
lean_dec_ref(v_as_1022_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object* v_spec_x3f_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_elts_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1102_; lean_object* v_cfg_1116_; 
v_cfg_1116_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5));
if (lean_obj_tag(v_spec_x3f_1058_) == 1)
{
lean_object* v_val_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_val_1117_ = lean_ctor_get(v_spec_x3f_1058_, 0);
lean_inc_n(v_val_1117_, 2);
lean_dec_ref_known(v_spec_x3f_1058_, 1);
v___x_1118_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7));
v___x_1119_ = l_Lean_Syntax_isOfKind(v_val_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_val_1117_);
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
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = l_Lean_Syntax_getArg(v_val_1117_, v___x_1129_);
lean_dec(v_val_1117_);
v___x_1131_ = l_Lean_Syntax_getArgs(v___x_1130_);
lean_dec(v___x_1130_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8));
v___x_1134_ = lean_array_get_size(v___x_1131_);
v___x_1135_ = lean_nat_dec_lt(v___x_1132_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_dec_ref(v___x_1131_);
v___y_1102_ = v___x_1133_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1136_ = lean_box(v___x_1119_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___x_1133_);
v___x_1138_ = lean_nat_dec_le(v___x_1134_, v___x_1134_);
if (v___x_1138_ == 0)
{
if (v___x_1135_ == 0)
{
lean_dec_ref_known(v___x_1137_, 2);
lean_dec_ref(v___x_1131_);
v___y_1102_ = v___x_1133_;
goto v___jp_1101_;
}
else
{
size_t v___x_1139_; size_t v___x_1140_; lean_object* v___x_1141_; lean_object* v_snd_1142_; 
v___x_1139_ = ((size_t)0ULL);
v___x_1140_ = lean_usize_of_nat(v___x_1134_);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1119_, v___x_1131_, v___x_1139_, v___x_1140_, v___x_1137_);
lean_dec_ref(v___x_1131_);
v_snd_1142_ = lean_ctor_get(v___x_1141_, 1);
lean_inc(v_snd_1142_);
lean_dec_ref(v___x_1141_);
v___y_1102_ = v_snd_1142_;
goto v___jp_1101_;
}
}
else
{
size_t v___x_1143_; size_t v___x_1144_; lean_object* v___x_1145_; lean_object* v_snd_1146_; 
v___x_1143_ = ((size_t)0ULL);
v___x_1144_ = lean_usize_of_nat(v___x_1134_);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1119_, v___x_1131_, v___x_1143_, v___x_1144_, v___x_1137_);
lean_dec_ref(v___x_1131_);
v_snd_1146_ = lean_ctor_get(v___x_1145_, 1);
lean_inc(v_snd_1146_);
lean_dec_ref(v___x_1145_);
v___y_1102_ = v_snd_1146_;
goto v___jp_1101_;
}
}
}
}
else
{
lean_object* v___x_1147_; 
lean_dec(v_spec_x3f_1058_);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_cfg_1116_);
return v___x_1147_;
}
v___jp_1062_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; size_t v_sz_1068_; size_t v___x_1069_; lean_object* v___x_1070_; 
v___x_1066_ = l_Array_reverse___redArg(v_elts_1063_);
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4));
v_sz_1068_ = lean_array_size(v___x_1066_);
v___x_1069_ = ((size_t)0ULL);
v___x_1070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v___x_1066_, v_sz_1068_, v___x_1069_, v___x_1067_, v___y_1064_, v___y_1065_);
lean_dec_ref(v___x_1066_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1092_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1092_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1092_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v_snd_1075_; lean_object* v_snd_1076_; lean_object* v_snd_1077_; lean_object* v_fst_1078_; lean_object* v_fst_1079_; lean_object* v_fst_1080_; lean_object* v_fst_1081_; lean_object* v_snd_1082_; lean_object* v___y_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; uint8_t v___x_1086_; uint8_t v___x_1087_; uint8_t v___x_1088_; lean_object* v___x_1090_; 
v_snd_1075_ = lean_ctor_get(v_a_1071_, 1);
lean_inc(v_snd_1075_);
v_snd_1076_ = lean_ctor_get(v_snd_1075_, 1);
lean_inc(v_snd_1076_);
v_snd_1077_ = lean_ctor_get(v_snd_1076_, 1);
lean_inc(v_snd_1077_);
v_fst_1078_ = lean_ctor_get(v_a_1071_, 0);
lean_inc(v_fst_1078_);
lean_dec(v_a_1071_);
v_fst_1079_ = lean_ctor_get(v_snd_1075_, 0);
lean_inc(v_fst_1079_);
lean_dec(v_snd_1075_);
v_fst_1080_ = lean_ctor_get(v_snd_1076_, 0);
lean_inc(v_fst_1080_);
lean_dec(v_snd_1076_);
v_fst_1081_ = lean_ctor_get(v_snd_1077_, 0);
lean_inc(v_fst_1081_);
v_snd_1082_ = lean_ctor_get(v_snd_1077_, 1);
lean_inc(v_snd_1082_);
lean_dec(v_snd_1077_);
v___y_1083_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___y_1083_, 0, v_snd_1082_);
v___x_1084_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1084_, 0, v___y_1083_);
v___x_1085_ = lean_unbox(v_fst_1078_);
lean_dec(v_fst_1078_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*1, v___x_1085_);
v___x_1086_ = lean_unbox(v_fst_1079_);
lean_dec(v_fst_1079_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*1 + 1, v___x_1086_);
v___x_1087_ = lean_unbox(v_fst_1080_);
lean_dec(v_fst_1080_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*1 + 2, v___x_1087_);
v___x_1088_ = lean_unbox(v_fst_1081_);
lean_dec(v_fst_1081_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*1 + 3, v___x_1088_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1084_);
v___x_1090_ = v___x_1073_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1084_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1070_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1070_);
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
v___jp_1101_:
{
size_t v_sz_1103_; size_t v___x_1104_; lean_object* v___x_1105_; 
v_sz_1103_ = lean_array_size(v___y_1102_);
v___x_1104_ = ((size_t)0ULL);
v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_1103_, v___x_1104_, v___y_1102_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v___x_1106_; lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v___x_1106_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
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
else
{
lean_object* v_val_1115_; 
v_val_1115_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_val_1115_);
lean_dec_ref_known(v___x_1105_, 1);
v_elts_1063_ = v_val_1115_;
v___y_1064_ = v_a_1059_;
v___y_1065_ = v_a_1060_;
goto v___jp_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object* v_spec_x3f_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v_spec_x3f_1148_, v_a_1149_, v_a_1150_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(lean_object* v_s_1165_, lean_object* v_replacement_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_){
_start:
{
lean_object* v_it_1170_; lean_object* v_startPos_1171_; lean_object* v_endPos_1172_; lean_object* v_it_1181_; 
switch(lean_obj_tag(v_a_1167_))
{
case 0:
{
lean_object* v_pos_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1199_; 
v_pos_1187_ = lean_ctor_get(v_a_1167_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_a_1167_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1189_ = v_a_1167_;
v_isShared_1190_ = v_isSharedCheck_1199_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_pos_1187_);
lean_dec(v_a_1167_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1199_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_startInclusive_1191_; lean_object* v_endExclusive_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v_startInclusive_1191_ = lean_ctor_get(v_s_1165_, 1);
v_endExclusive_1192_ = lean_ctor_get(v_s_1165_, 2);
v___x_1193_ = lean_nat_sub(v_endExclusive_1192_, v_startInclusive_1191_);
v___x_1194_ = lean_nat_dec_eq(v_pos_1187_, v___x_1193_);
lean_dec(v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1196_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 1);
v___x_1196_ = v___x_1189_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_pos_1187_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
v_it_1181_ = v___x_1196_;
goto v___jp_1180_;
}
}
else
{
lean_object* v___x_1198_; 
lean_del_object(v___x_1189_);
lean_dec(v_pos_1187_);
v___x_1198_ = lean_box(3);
v_it_1181_ = v___x_1198_;
goto v___jp_1180_;
}
}
}
case 1:
{
lean_object* v_pos_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1212_; 
v_pos_1200_ = lean_ctor_get(v_a_1167_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_a_1167_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1202_ = v_a_1167_;
v_isShared_1203_ = v_isSharedCheck_1212_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_pos_1200_);
lean_dec(v_a_1167_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1212_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_str_1204_; lean_object* v_startInclusive_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v_str_1204_ = lean_ctor_get(v_s_1165_, 0);
v_startInclusive_1205_ = lean_ctor_get(v_s_1165_, 1);
v___x_1206_ = lean_nat_add(v_startInclusive_1205_, v_pos_1200_);
v___x_1207_ = lean_string_utf8_next_fast(v_str_1204_, v___x_1206_);
lean_dec(v___x_1206_);
v___x_1208_ = lean_nat_sub(v___x_1207_, v_startInclusive_1205_);
lean_inc(v___x_1208_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set_tag(v___x_1202_, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1208_);
v___x_1210_ = v___x_1202_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
v_it_1170_ = v___x_1210_;
v_startPos_1171_ = v_pos_1200_;
v_endPos_1172_ = v___x_1208_;
goto v___jp_1169_;
}
}
}
case 2:
{
lean_object* v_needle_1213_; lean_object* v_table_1214_; lean_object* v_stackPos_1215_; lean_object* v_needlePos_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1275_; 
v_needle_1213_ = lean_ctor_get(v_a_1167_, 0);
v_table_1214_ = lean_ctor_get(v_a_1167_, 1);
v_stackPos_1215_ = lean_ctor_get(v_a_1167_, 2);
v_needlePos_1216_ = lean_ctor_get(v_a_1167_, 3);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_a_1167_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1218_ = v_a_1167_;
v_isShared_1219_ = v_isSharedCheck_1275_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_needlePos_1216_);
lean_inc(v_stackPos_1215_);
lean_inc(v_table_1214_);
lean_inc(v_needle_1213_);
lean_dec(v_a_1167_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1275_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v_str_1220_; lean_object* v_startInclusive_1221_; lean_object* v_endExclusive_1222_; lean_object* v_str_1223_; lean_object* v_startInclusive_1224_; lean_object* v_endExclusive_1225_; lean_object* v_basePos_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_str_1220_ = lean_ctor_get(v_needle_1213_, 0);
v_startInclusive_1221_ = lean_ctor_get(v_needle_1213_, 1);
v_endExclusive_1222_ = lean_ctor_get(v_needle_1213_, 2);
v_str_1223_ = lean_ctor_get(v_s_1165_, 0);
v_startInclusive_1224_ = lean_ctor_get(v_s_1165_, 1);
v_endExclusive_1225_ = lean_ctor_get(v_s_1165_, 2);
v_basePos_1226_ = lean_nat_sub(v_stackPos_1215_, v_needlePos_1216_);
v___x_1227_ = lean_nat_sub(v_endExclusive_1222_, v_startInclusive_1221_);
v___x_1228_ = lean_nat_add(v_basePos_1226_, v___x_1227_);
v___x_1229_ = lean_nat_sub(v_endExclusive_1225_, v_startInclusive_1224_);
v___x_1230_ = lean_nat_dec_le(v___x_1228_, v___x_1229_);
lean_dec(v___x_1228_);
if (v___x_1230_ == 0)
{
uint8_t v___x_1231_; 
lean_dec(v___x_1227_);
lean_del_object(v___x_1218_);
lean_dec(v_needlePos_1216_);
lean_dec(v_stackPos_1215_);
lean_dec_ref(v_table_1214_);
lean_dec_ref(v_needle_1213_);
v___x_1231_ = lean_nat_dec_lt(v_basePos_1226_, v___x_1229_);
if (v___x_1231_ == 0)
{
lean_dec(v___x_1229_);
lean_dec(v_basePos_1226_);
lean_dec_ref(v_s_1165_);
return v_b_1168_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = l_String_Slice_pos_x21(v_s_1165_, v_basePos_1226_);
lean_dec(v_basePos_1226_);
v___x_1233_ = lean_box(3);
v_it_1170_ = v___x_1233_;
v_startPos_1171_ = v___x_1232_;
v_endPos_1172_ = v___x_1229_;
goto v___jp_1169_;
}
}
else
{
lean_object* v___x_1234_; uint8_t v_stackByte_1235_; lean_object* v___x_1236_; uint8_t v_patByte_1237_; uint8_t v___x_1238_; 
lean_dec(v___x_1229_);
v___x_1234_ = lean_nat_add(v_startInclusive_1224_, v_stackPos_1215_);
v_stackByte_1235_ = lean_string_get_byte_fast(v_str_1223_, v___x_1234_);
v___x_1236_ = lean_nat_add(v_startInclusive_1221_, v_needlePos_1216_);
v_patByte_1237_ = lean_string_get_byte_fast(v_str_1220_, v___x_1236_);
v___x_1238_ = lean_uint8_dec_eq(v_stackByte_1235_, v_patByte_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
lean_dec(v___x_1227_);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_nat_dec_eq(v_needlePos_1216_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v_newNeedlePos_1243_; uint8_t v___x_1244_; 
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_sub(v_needlePos_1216_, v___x_1241_);
lean_dec(v_needlePos_1216_);
v_newNeedlePos_1243_ = lean_array_fget_borrowed(v_table_1214_, v___x_1242_);
lean_dec(v___x_1242_);
v___x_1244_ = lean_nat_dec_eq(v_newNeedlePos_1243_, v___x_1239_);
if (v___x_1244_ == 0)
{
lean_object* v_oldBasePos_1245_; lean_object* v___x_1246_; lean_object* v_newBasePos_1247_; lean_object* v___x_1249_; 
lean_inc(v_newNeedlePos_1243_);
v_oldBasePos_1245_ = l_String_Slice_pos_x21(v_s_1165_, v_basePos_1226_);
lean_dec(v_basePos_1226_);
v___x_1246_ = lean_nat_sub(v_stackPos_1215_, v_newNeedlePos_1243_);
v_newBasePos_1247_ = l_String_Slice_pos_x21(v_s_1165_, v___x_1246_);
lean_dec(v___x_1246_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 3, v_newNeedlePos_1243_);
v___x_1249_ = v___x_1218_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_needle_1213_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_table_1214_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_stackPos_1215_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_newNeedlePos_1243_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
v_it_1170_ = v___x_1249_;
v_startPos_1171_ = v_oldBasePos_1245_;
v_endPos_1172_ = v_newBasePos_1247_;
goto v___jp_1169_;
}
}
else
{
lean_object* v_basePos_1251_; lean_object* v_nextStackPos_1252_; lean_object* v___x_1254_; 
v_basePos_1251_ = l_String_Slice_pos_x21(v_s_1165_, v_basePos_1226_);
lean_dec(v_basePos_1226_);
v_nextStackPos_1252_ = l_String_Slice_posGE___redArg(v_s_1165_, v_stackPos_1215_);
lean_inc(v_nextStackPos_1252_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 3, v___x_1239_);
lean_ctor_set(v___x_1218_, 2, v_nextStackPos_1252_);
v___x_1254_ = v___x_1218_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_needle_1213_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_table_1214_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_nextStackPos_1252_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v___x_1239_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
v_it_1170_ = v___x_1254_;
v_startPos_1171_ = v_basePos_1251_;
v_endPos_1172_ = v_nextStackPos_1252_;
goto v___jp_1169_;
}
}
}
else
{
lean_object* v_basePos_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v_nextStackPos_1259_; lean_object* v___x_1261_; 
lean_dec(v_basePos_1226_);
lean_dec(v_needlePos_1216_);
v_basePos_1256_ = l_String_Slice_pos_x21(v_s_1165_, v_stackPos_1215_);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_add(v_stackPos_1215_, v___x_1257_);
lean_dec(v_stackPos_1215_);
v_nextStackPos_1259_ = l_String_Slice_posGE___redArg(v_s_1165_, v___x_1258_);
lean_inc(v_nextStackPos_1259_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 3, v___x_1239_);
lean_ctor_set(v___x_1218_, 2, v_nextStackPos_1259_);
v___x_1261_ = v___x_1218_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_needle_1213_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_table_1214_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v_nextStackPos_1259_);
lean_ctor_set(v_reuseFailAlloc_1262_, 3, v___x_1239_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
v_it_1170_ = v___x_1261_;
v_startPos_1171_ = v_basePos_1256_;
v_endPos_1172_ = v_nextStackPos_1259_;
goto v___jp_1169_;
}
}
}
else
{
lean_object* v___x_1263_; lean_object* v_nextStackPos_1264_; lean_object* v_nextNeedlePos_1265_; uint8_t v___x_1266_; 
lean_dec(v_basePos_1226_);
v___x_1263_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1264_ = lean_nat_add(v_stackPos_1215_, v___x_1263_);
lean_dec(v_stackPos_1215_);
v_nextNeedlePos_1265_ = lean_nat_add(v_needlePos_1216_, v___x_1263_);
lean_dec(v_needlePos_1216_);
v___x_1266_ = lean_nat_dec_eq(v_nextNeedlePos_1265_, v___x_1227_);
lean_dec(v___x_1227_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1268_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 3, v_nextNeedlePos_1265_);
lean_ctor_set(v___x_1218_, 2, v_nextStackPos_1264_);
v___x_1268_ = v___x_1218_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_needle_1213_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_table_1214_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_nextStackPos_1264_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_nextNeedlePos_1265_);
v___x_1268_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
v_a_1167_ = v___x_1268_;
goto _start;
}
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
lean_dec(v_nextNeedlePos_1265_);
v___x_1271_ = lean_unsigned_to_nat(0u);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 3, v___x_1271_);
lean_ctor_set(v___x_1218_, 2, v_nextStackPos_1264_);
v___x_1273_ = v___x_1218_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_needle_1213_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_table_1214_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_nextStackPos_1264_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
v_it_1181_ = v___x_1273_;
goto v___jp_1180_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1165_);
return v_b_1168_;
}
}
v___jp_1169_:
{
lean_object* v___x_1173_; lean_object* v_str_1174_; lean_object* v_startInclusive_1175_; lean_object* v_endExclusive_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_inc_ref(v_s_1165_);
v___x_1173_ = l_String_Slice_slice_x21(v_s_1165_, v_startPos_1171_, v_endPos_1172_);
lean_dec(v_endPos_1172_);
lean_dec(v_startPos_1171_);
v_str_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc_ref(v_str_1174_);
v_startInclusive_1175_ = lean_ctor_get(v___x_1173_, 1);
lean_inc(v_startInclusive_1175_);
v_endExclusive_1176_ = lean_ctor_get(v___x_1173_, 2);
lean_inc(v_endExclusive_1176_);
lean_dec_ref(v___x_1173_);
v___x_1177_ = lean_string_utf8_extract_fast(v_str_1174_, v_startInclusive_1175_, v_endExclusive_1176_);
lean_dec(v_endExclusive_1176_);
lean_dec(v_startInclusive_1175_);
lean_dec_ref(v_str_1174_);
v___x_1178_ = lean_string_append(v_b_1168_, v___x_1177_);
lean_dec_ref(v___x_1177_);
v_a_1167_ = v_it_1170_;
v_b_1168_ = v___x_1178_;
goto _start;
}
v___jp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = lean_string_utf8_byte_size(v_replacement_1166_);
v___x_1184_ = lean_string_utf8_extract_fast(v_replacement_1166_, v___x_1182_, v___x_1183_);
v___x_1185_ = lean_string_append(v_b_1168_, v___x_1184_);
lean_dec_ref(v___x_1184_);
v_a_1167_ = v_it_1181_;
v_b_1168_ = v___x_1185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg___boxed(lean_object* v_s_1276_, lean_object* v_replacement_1277_, lean_object* v_a_1278_, lean_object* v_b_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1276_, v_replacement_1277_, v_a_1278_, v_b_1279_);
lean_dec_ref(v_replacement_1277_);
return v_res_1280_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1283_ = lean_string_utf8_byte_size(v___x_1282_);
return v___x_1283_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1286_ = lean_nat_dec_eq(v___x_1285_, v___x_1284_);
return v___x_1286_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1287_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___x_1288_);
lean_ctor_set(v___x_1290_, 2, v___x_1287_);
return v___x_1290_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1292_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4);
v___x_1295_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1296_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v___x_1294_);
lean_ctor_set(v___x_1296_, 2, v___x_1293_);
lean_ctor_set(v___x_1296_, 3, v___x_1293_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object* v_s_1299_, lean_object* v_replacement_1300_){
_start:
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1302_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5);
v___x_1304_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1299_, v_replacement_1300_, v___x_1303_, v___x_1301_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1306_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1299_, v_replacement_1300_, v___x_1305_, v___x_1301_);
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___boxed(lean_object* v_s_1307_, lean_object* v_replacement_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1307_, v_replacement_1308_);
lean_dec_ref(v_replacement_1308_);
return v_res_1309_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1312_ = lean_string_utf8_byte_size(v___x_1311_);
return v___x_1312_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1315_ = lean_nat_dec_eq(v___x_1314_, v___x_1313_);
return v___x_1315_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1316_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v___x_1317_);
lean_ctor_set(v___x_1319_, 2, v___x_1316_);
return v___x_1319_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1321_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1322_ = lean_unsigned_to_nat(0u);
v___x_1323_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4);
v___x_1324_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1325_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___x_1323_);
lean_ctor_set(v___x_1325_, 2, v___x_1322_);
lean_ctor_set(v___x_1325_, 3, v___x_1322_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object* v_s_1326_, lean_object* v_replacement_1327_){
_start:
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1329_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5);
v___x_1331_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1326_, v_replacement_1327_, v___x_1330_, v___x_1328_);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1333_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1326_, v_replacement_1327_, v___x_1332_, v___x_1328_);
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object* v_s_1334_, lean_object* v_replacement_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1334_, v_replacement_1335_);
lean_dec_ref(v_replacement_1335_);
return v_res_1336_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1339_ = lean_string_utf8_byte_size(v___x_1338_);
return v___x_1339_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1340_ = lean_unsigned_to_nat(0u);
v___x_1341_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1342_ = lean_nat_dec_eq(v___x_1341_, v___x_1340_);
return v___x_1342_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1343_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___x_1344_);
lean_ctor_set(v___x_1346_, 2, v___x_1343_);
return v___x_1346_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1348_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1347_);
return v___x_1348_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4);
v___x_1351_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1352_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v___x_1350_);
lean_ctor_set(v___x_1352_, 2, v___x_1349_);
lean_ctor_set(v___x_1352_, 3, v___x_1349_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(lean_object* v_s_1353_, lean_object* v_replacement_1354_){
_start:
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1356_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5);
v___x_1358_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1353_, v_replacement_1354_, v___x_1357_, v___x_1355_);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1360_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1353_, v_replacement_1354_, v___x_1359_, v___x_1355_);
return v___x_1360_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___boxed(lean_object* v_s_1361_, lean_object* v_replacement_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1361_, v_replacement_1362_);
lean_dec_ref(v_replacement_1362_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object* v_s_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1368_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0));
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_string_utf8_byte_size(v_s_1367_);
v___x_1371_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1371_, 0, v_s_1367_);
lean_ctor_set(v___x_1371_, 1, v___x_1369_);
lean_ctor_set(v___x_1371_, 2, v___x_1370_);
v___x_1372_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1371_, v___x_1368_);
v___x_1373_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1));
v___x_1374_ = lean_string_utf8_byte_size(v___x_1372_);
v___x_1375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1372_);
lean_ctor_set(v___x_1375_, 1, v___x_1369_);
lean_ctor_set(v___x_1375_, 2, v___x_1374_);
v___x_1376_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v___x_1375_, v___x_1373_);
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2));
v___x_1378_ = lean_string_utf8_byte_size(v___x_1376_);
v___x_1379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1376_);
lean_ctor_set(v___x_1379_, 1, v___x_1369_);
lean_ctor_set(v___x_1379_, 2, v___x_1378_);
v___x_1380_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v___x_1379_, v___x_1377_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(lean_object* v_s_1381_, lean_object* v_pattern_1382_, lean_object* v_replacement_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1381_, v_replacement_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___boxed(lean_object* v_s_1385_, lean_object* v_pattern_1386_, lean_object* v_replacement_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(v_s_1385_, v_pattern_1386_, v_replacement_1387_);
lean_dec_ref(v_replacement_1387_);
lean_dec_ref(v_pattern_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(lean_object* v_s_1389_, lean_object* v_pattern_1390_, lean_object* v_replacement_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1389_, v_replacement_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___boxed(lean_object* v_s_1393_, lean_object* v_pattern_1394_, lean_object* v_replacement_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(v_s_1393_, v_pattern_1394_, v_replacement_1395_);
lean_dec_ref(v_replacement_1395_);
lean_dec_ref(v_pattern_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(lean_object* v_s_1397_, lean_object* v_pattern_1398_, lean_object* v_replacement_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1397_, v_replacement_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___boxed(lean_object* v_s_1401_, lean_object* v_pattern_1402_, lean_object* v_replacement_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(v_s_1401_, v_pattern_1402_, v_replacement_1403_);
lean_dec_ref(v_replacement_1403_);
lean_dec_ref(v_pattern_1402_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(lean_object* v_s_1405_, lean_object* v_replacement_1406_, lean_object* v_inst_1407_, lean_object* v_R_1408_, lean_object* v_a_1409_, lean_object* v_b_1410_, lean_object* v_c_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1405_, v_replacement_1406_, v_a_1409_, v_b_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___boxed(lean_object* v_s_1413_, lean_object* v_replacement_1414_, lean_object* v_inst_1415_, lean_object* v_R_1416_, lean_object* v_a_1417_, lean_object* v_b_1418_, lean_object* v_c_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(v_s_1413_, v_replacement_1414_, v_inst_1415_, v_R_1416_, v_a_1417_, v_b_1418_, v_c_1419_);
lean_dec_ref(v_replacement_1414_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object* v_s_1421_){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1422_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = lean_string_utf8_byte_size(v_s_1421_);
v___x_1425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1425_, 0, v_s_1421_);
lean_ctor_set(v___x_1425_, 1, v___x_1423_);
lean_ctor_set(v___x_1425_, 2, v___x_1424_);
v___x_1426_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1425_, v___x_1422_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object* v_s_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0));
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object* v_s_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v_s_1431_);
lean_dec_ref(v_s_1431_);
return v_res_1432_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___x_1434_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1435_ = lean_nat_dec_eq(v___x_1434_, v___x_1433_);
return v___x_1435_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1436_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
lean_ctor_set(v___x_1439_, 1, v___x_1437_);
lean_ctor_set(v___x_1439_, 2, v___x_1436_);
return v___x_1439_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1441_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1440_);
return v___x_1441_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2);
v___x_1444_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1445_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v___x_1443_);
lean_ctor_set(v___x_1445_, 2, v___x_1442_);
lean_ctor_set(v___x_1445_, 3, v___x_1442_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object* v_s_1446_, lean_object* v_replacement_1447_){
_start:
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1449_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3);
v___x_1451_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1446_, v_replacement_1447_, v___x_1450_, v___x_1448_);
return v___x_1451_;
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1453_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1446_, v_replacement_1447_, v___x_1452_, v___x_1448_);
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object* v_s_1454_, lean_object* v_replacement_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1454_, v_replacement_1455_);
lean_dec_ref(v_replacement_1455_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object* v_s_1457_, lean_object* v___x_1458_, lean_object* v___x_1459_, lean_object* v_a_1460_, lean_object* v_b_1461_){
_start:
{
lean_object* v_it_1463_; lean_object* v_startInclusive_1464_; lean_object* v_endExclusive_1465_; 
if (lean_obj_tag(v_a_1460_) == 0)
{
lean_object* v_currPos_1473_; lean_object* v_searcher_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1509_; 
v_currPos_1473_ = lean_ctor_get(v_a_1460_, 0);
v_searcher_1474_ = lean_ctor_get(v_a_1460_, 1);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_a_1460_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1476_ = v_a_1460_;
v_isShared_1477_ = v_isSharedCheck_1509_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_searcher_1474_);
lean_inc(v_currPos_1473_);
lean_dec(v_a_1460_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1509_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
uint8_t v___y_1489_; lean_object* v_startInclusive_1493_; lean_object* v_endExclusive_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v_startInclusive_1493_ = lean_ctor_get(v___x_1458_, 1);
v_endExclusive_1494_ = lean_ctor_get(v___x_1458_, 2);
v___x_1495_ = lean_nat_sub(v_endExclusive_1494_, v_startInclusive_1493_);
v___x_1496_ = lean_nat_dec_eq(v_searcher_1474_, v___x_1495_);
lean_dec(v___x_1495_);
if (v___x_1496_ == 0)
{
uint32_t v___x_1497_; uint8_t v___y_1499_; uint32_t v___x_1504_; uint8_t v___x_1505_; 
v___x_1497_ = lean_string_utf8_get_fast(v_s_1457_, v_searcher_1474_);
v___x_1504_ = 32;
v___x_1505_ = lean_uint32_dec_eq(v___x_1497_, v___x_1504_);
if (v___x_1505_ == 0)
{
uint32_t v___x_1506_; uint8_t v___x_1507_; 
v___x_1506_ = 9;
v___x_1507_ = lean_uint32_dec_eq(v___x_1497_, v___x_1506_);
v___y_1499_ = v___x_1507_;
goto v___jp_1498_;
}
else
{
v___y_1499_ = v___x_1505_;
goto v___jp_1498_;
}
v___jp_1498_:
{
if (v___y_1499_ == 0)
{
uint32_t v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = 13;
v___x_1501_ = lean_uint32_dec_eq(v___x_1497_, v___x_1500_);
if (v___x_1501_ == 0)
{
uint32_t v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = 10;
v___x_1503_ = lean_uint32_dec_eq(v___x_1497_, v___x_1502_);
v___y_1489_ = v___x_1503_;
goto v___jp_1488_;
}
else
{
v___y_1489_ = v___x_1501_;
goto v___jp_1488_;
}
}
else
{
goto v___jp_1478_;
}
}
}
else
{
lean_object* v___x_1508_; 
lean_del_object(v___x_1476_);
lean_dec(v_searcher_1474_);
v___x_1508_ = lean_box(1);
lean_inc(v___x_1459_);
v_it_1463_ = v___x_1508_;
v_startInclusive_1464_ = v_currPos_1473_;
v_endExclusive_1465_ = v___x_1459_;
goto v___jp_1462_;
}
v___jp_1478_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_slice_1482_; lean_object* v_nextIt_1484_; 
v___x_1479_ = lean_string_utf8_next_fast(v_s_1457_, v_searcher_1474_);
v___x_1480_ = lean_nat_sub(v___x_1479_, v_searcher_1474_);
v___x_1481_ = lean_nat_add(v_searcher_1474_, v___x_1480_);
lean_dec(v___x_1480_);
v_slice_1482_ = l_String_Slice_subslice_x21(v___x_1458_, v_currPos_1473_, v_searcher_1474_);
lean_inc(v___x_1481_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v___x_1481_);
lean_ctor_set(v___x_1476_, 0, v___x_1481_);
v_nextIt_1484_ = v___x_1476_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1481_);
v_nextIt_1484_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v_startInclusive_1485_; lean_object* v_endExclusive_1486_; 
v_startInclusive_1485_ = lean_ctor_get(v_slice_1482_, 0);
lean_inc(v_startInclusive_1485_);
v_endExclusive_1486_ = lean_ctor_get(v_slice_1482_, 1);
lean_inc(v_endExclusive_1486_);
lean_dec_ref(v_slice_1482_);
v_it_1463_ = v_nextIt_1484_;
v_startInclusive_1464_ = v_startInclusive_1485_;
v_endExclusive_1465_ = v_endExclusive_1486_;
goto v___jp_1462_;
}
}
v___jp_1488_:
{
if (v___y_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_del_object(v___x_1476_);
v___x_1490_ = lean_string_utf8_next_fast(v_s_1457_, v_searcher_1474_);
lean_dec(v_searcher_1474_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_currPos_1473_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v_a_1460_ = v___x_1491_;
goto _start;
}
else
{
goto v___jp_1478_;
}
}
}
}
else
{
lean_dec(v___x_1459_);
lean_dec_ref(v_s_1457_);
return v_b_1461_;
}
v___jp_1462_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = lean_nat_sub(v_endExclusive_1465_, v_startInclusive_1464_);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = lean_nat_dec_eq(v___x_1466_, v___x_1467_);
lean_dec(v___x_1466_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_inc_ref(v_s_1457_);
v___x_1469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1469_, 0, v_s_1457_);
lean_ctor_set(v___x_1469_, 1, v_startInclusive_1464_);
lean_ctor_set(v___x_1469_, 2, v_endExclusive_1465_);
v___x_1470_ = lean_array_push(v_b_1461_, v___x_1469_);
v_a_1460_ = v_it_1463_;
v_b_1461_ = v___x_1470_;
goto _start;
}
else
{
lean_dec(v_endExclusive_1465_);
lean_dec(v_startInclusive_1464_);
v_a_1460_ = v_it_1463_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object* v_s_1510_, lean_object* v___x_1511_, lean_object* v___x_1512_, lean_object* v_a_1513_, lean_object* v_b_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1510_, v___x_1511_, v___x_1512_, v_a_1513_, v_b_1514_);
lean_dec_ref(v___x_1511_);
return v_res_1515_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1517_ = lean_string_utf8_byte_size(v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1518_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0);
v___x_1519_ = lean_unsigned_to_nat(0u);
v___x_1520_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1519_);
lean_ctor_set(v___x_1521_, 2, v___x_1518_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t v_mode_1524_, lean_object* v_s_1525_){
_start:
{
switch(v_mode_1524_)
{
case 0:
{
return v_s_1525_;
}
case 1:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1526_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_string_utf8_byte_size(v_s_1525_);
v___x_1529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1529_, 0, v_s_1525_);
lean_ctor_set(v___x_1529_, 1, v___x_1527_);
lean_ctor_set(v___x_1529_, 2, v___x_1528_);
v___x_1530_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v___x_1529_, v___x_1526_);
return v___x_1530_;
}
default: 
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1);
v___x_1533_ = lean_string_utf8_byte_size(v_s_1525_);
lean_inc_ref(v_s_1525_);
v___x_1534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1534_, 0, v_s_1525_);
lean_ctor_set(v___x_1534_, 1, v___x_1531_);
lean_ctor_set(v___x_1534_, 2, v___x_1533_);
v___x_1535_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v___x_1534_);
v___x_1536_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__2));
v___x_1537_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1525_, v___x_1534_, v___x_1533_, v___x_1535_, v___x_1536_);
lean_dec_ref_known(v___x_1534_, 3);
v___x_1538_ = lean_array_to_list(v___x_1537_);
v___x_1539_ = l_String_Slice_intercalate(v___x_1532_, v___x_1538_);
lean_dec(v___x_1538_);
return v___x_1539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object* v_mode_1540_, lean_object* v_s_1541_){
_start:
{
uint8_t v_mode_boxed_1542_; lean_object* v_res_1543_; 
v_mode_boxed_1542_ = lean_unbox(v_mode_1540_);
v_res_1543_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v_mode_boxed_1542_, v_s_1541_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object* v_s_1544_, lean_object* v_pattern_1545_, lean_object* v_replacement_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1544_, v_replacement_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object* v_s_1548_, lean_object* v_pattern_1549_, lean_object* v_replacement_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(v_s_1548_, v_pattern_1549_, v_replacement_1550_);
lean_dec_ref(v_replacement_1550_);
lean_dec_ref(v_pattern_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object* v_s_1552_, lean_object* v___x_1553_, lean_object* v___x_1554_, lean_object* v_inst_1555_, lean_object* v_R_1556_, lean_object* v_a_1557_, lean_object* v_b_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1552_, v___x_1553_, v___x_1554_, v_a_1557_, v_b_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___boxed(lean_object* v_s_1560_, lean_object* v___x_1561_, lean_object* v___x_1562_, lean_object* v_inst_1563_, lean_object* v_R_1564_, lean_object* v_a_1565_, lean_object* v_b_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(v_s_1560_, v___x_1561_, v___x_1562_, v_inst_1563_, v_R_1564_, v_a_1565_, v_b_1566_);
lean_dec_ref(v___x_1561_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(lean_object* v_hi_1568_, lean_object* v_pivot_1569_, lean_object* v_as_1570_, lean_object* v_i_1571_, lean_object* v_k_1572_){
_start:
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_nat_dec_lt(v_k_1572_, v_hi_1568_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_dec(v_k_1572_);
v___x_1574_ = lean_array_fswap(v_as_1570_, v_i_1571_, v_hi_1568_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v_i_1571_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
return v___x_1575_;
}
else
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_array_fget_borrowed(v_as_1570_, v_k_1572_);
v___x_1577_ = lean_string_dec_lt(v___x_1576_, v_pivot_1569_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_add(v_k_1572_, v___x_1578_);
lean_dec(v_k_1572_);
v_k_1572_ = v___x_1579_;
goto _start;
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1581_ = lean_array_fswap(v_as_1570_, v_i_1571_, v_k_1572_);
v___x_1582_ = lean_unsigned_to_nat(1u);
v___x_1583_ = lean_nat_add(v_i_1571_, v___x_1582_);
lean_dec(v_i_1571_);
v___x_1584_ = lean_nat_add(v_k_1572_, v___x_1582_);
lean_dec(v_k_1572_);
v_as_1570_ = v___x_1581_;
v_i_1571_ = v___x_1583_;
v_k_1572_ = v___x_1584_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg___boxed(lean_object* v_hi_1586_, lean_object* v_pivot_1587_, lean_object* v_as_1588_, lean_object* v_i_1589_, lean_object* v_k_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1586_, v_pivot_1587_, v_as_1588_, v_i_1589_, v_k_1590_);
lean_dec_ref(v_pivot_1587_);
lean_dec(v_hi_1586_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object* v_n_1592_, lean_object* v_as_1593_, lean_object* v_lo_1594_, lean_object* v_hi_1595_){
_start:
{
lean_object* v___y_1597_; uint8_t v___x_1607_; 
v___x_1607_ = lean_nat_dec_lt(v_lo_1594_, v_hi_1595_);
if (v___x_1607_ == 0)
{
lean_dec(v_lo_1594_);
return v_as_1593_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v_mid_1610_; lean_object* v___y_1612_; lean_object* v___y_1618_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1608_ = lean_nat_add(v_lo_1594_, v_hi_1595_);
v___x_1609_ = lean_unsigned_to_nat(1u);
v_mid_1610_ = lean_nat_shiftr(v___x_1608_, v___x_1609_);
lean_dec(v___x_1608_);
v___x_1623_ = lean_array_fget_borrowed(v_as_1593_, v_mid_1610_);
v___x_1624_ = lean_array_fget_borrowed(v_as_1593_, v_lo_1594_);
v___x_1625_ = lean_string_dec_lt(v___x_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
v___y_1618_ = v_as_1593_;
goto v___jp_1617_;
}
else
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_array_fswap(v_as_1593_, v_lo_1594_, v_mid_1610_);
v___y_1618_ = v___x_1626_;
goto v___jp_1617_;
}
v___jp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1613_ = lean_array_fget_borrowed(v___y_1612_, v_mid_1610_);
v___x_1614_ = lean_array_fget_borrowed(v___y_1612_, v_hi_1595_);
v___x_1615_ = lean_string_dec_lt(v___x_1613_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_dec(v_mid_1610_);
v___y_1597_ = v___y_1612_;
goto v___jp_1596_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_array_fswap(v___y_1612_, v_mid_1610_, v_hi_1595_);
lean_dec(v_mid_1610_);
v___y_1597_ = v___x_1616_;
goto v___jp_1596_;
}
}
v___jp_1617_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1619_ = lean_array_fget_borrowed(v___y_1618_, v_hi_1595_);
v___x_1620_ = lean_array_fget_borrowed(v___y_1618_, v_lo_1594_);
v___x_1621_ = lean_string_dec_lt(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
v___y_1612_ = v___y_1618_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_array_fswap(v___y_1618_, v_lo_1594_, v_hi_1595_);
v___y_1612_ = v___x_1622_;
goto v___jp_1611_;
}
}
}
v___jp_1596_:
{
lean_object* v_pivot_1598_; lean_object* v___x_1599_; lean_object* v_fst_1600_; lean_object* v_snd_1601_; uint8_t v___x_1602_; 
v_pivot_1598_ = lean_array_fget(v___y_1597_, v_hi_1595_);
lean_inc_n(v_lo_1594_, 2);
v___x_1599_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1595_, v_pivot_1598_, v___y_1597_, v_lo_1594_, v_lo_1594_);
lean_dec(v_pivot_1598_);
v_fst_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_fst_1600_);
v_snd_1601_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_snd_1601_);
lean_dec_ref(v___x_1599_);
v___x_1602_ = lean_nat_dec_le(v_hi_1595_, v_fst_1600_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1592_, v_snd_1601_, v_lo_1594_, v_fst_1600_);
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_nat_add(v_fst_1600_, v___x_1604_);
lean_dec(v_fst_1600_);
v_as_1593_ = v___x_1603_;
v_lo_1594_ = v___x_1605_;
goto _start;
}
else
{
lean_dec(v_fst_1600_);
lean_dec(v_lo_1594_);
return v_snd_1601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object* v_n_1627_, lean_object* v_as_1628_, lean_object* v_lo_1629_, lean_object* v_hi_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1627_, v_as_1628_, v_lo_1629_, v_hi_1630_);
lean_dec(v_hi_1630_);
lean_dec(v_n_1627_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t v_mode_1632_, lean_object* v_msgs_1633_){
_start:
{
if (v_mode_1632_ == 0)
{
return v_msgs_1633_;
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1634_ = lean_array_mk(v_msgs_1633_);
v___x_1635_ = lean_array_get_size(v___x_1634_);
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = lean_nat_dec_eq(v___x_1635_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___y_1646_; uint8_t v___x_1648_; 
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_sub(v___x_1635_, v___x_1643_);
v___x_1648_ = lean_nat_dec_le(v___x_1641_, v___x_1644_);
if (v___x_1648_ == 0)
{
lean_inc(v___x_1644_);
v___y_1646_ = v___x_1644_;
goto v___jp_1645_;
}
else
{
v___y_1646_ = v___x_1641_;
goto v___jp_1645_;
}
v___jp_1645_:
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_nat_dec_le(v___y_1646_, v___x_1644_);
if (v___x_1647_ == 0)
{
lean_dec(v___x_1644_);
lean_inc(v___y_1646_);
v___y_1637_ = v___y_1646_;
v___y_1638_ = v___y_1646_;
goto v___jp_1636_;
}
else
{
v___y_1637_ = v___y_1646_;
v___y_1638_ = v___x_1644_;
goto v___jp_1636_;
}
}
}
else
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_array_to_list(v___x_1634_);
return v___x_1649_;
}
v___jp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v___x_1635_, v___x_1634_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
v___x_1640_ = lean_array_to_list(v___x_1639_);
return v___x_1640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* v_mode_1650_, lean_object* v_msgs_1651_){
_start:
{
uint8_t v_mode_boxed_1652_; lean_object* v_res_1653_; 
v_mode_boxed_1652_ = lean_unbox(v_mode_1650_);
v_res_1653_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_boxed_1652_, v_msgs_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object* v_n_1654_, lean_object* v_as_1655_, lean_object* v_lo_1656_, lean_object* v_hi_1657_, lean_object* v_w_1658_, lean_object* v_hlo_1659_, lean_object* v_hhi_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1654_, v_as_1655_, v_lo_1656_, v_hi_1657_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object* v_n_1662_, lean_object* v_as_1663_, lean_object* v_lo_1664_, lean_object* v_hi_1665_, lean_object* v_w_1666_, lean_object* v_hlo_1667_, lean_object* v_hhi_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(v_n_1662_, v_as_1663_, v_lo_1664_, v_hi_1665_, v_w_1666_, v_hlo_1667_, v_hhi_1668_);
lean_dec(v_hi_1665_);
lean_dec(v_n_1662_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(lean_object* v_n_1670_, lean_object* v_lo_1671_, lean_object* v_hi_1672_, lean_object* v_hhi_1673_, lean_object* v_pivot_1674_, lean_object* v_as_1675_, lean_object* v_i_1676_, lean_object* v_k_1677_, lean_object* v_ilo_1678_, lean_object* v_ik_1679_, lean_object* v_w_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1672_, v_pivot_1674_, v_as_1675_, v_i_1676_, v_k_1677_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___boxed(lean_object* v_n_1682_, lean_object* v_lo_1683_, lean_object* v_hi_1684_, lean_object* v_hhi_1685_, lean_object* v_pivot_1686_, lean_object* v_as_1687_, lean_object* v_i_1688_, lean_object* v_k_1689_, lean_object* v_ilo_1690_, lean_object* v_ik_1691_, lean_object* v_w_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(v_n_1682_, v_lo_1683_, v_hi_1684_, v_hhi_1685_, v_pivot_1686_, v_as_1687_, v_i_1688_, v_k_1689_, v_ilo_1690_, v_ik_1691_, v_w_1692_);
lean_dec_ref(v_pivot_1686_);
lean_dec(v_hi_1684_);
lean_dec(v_lo_1683_);
lean_dec(v_n_1682_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object* v_as_1694_, size_t v_i_1695_, size_t v_stop_1696_, lean_object* v_b_1697_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_usize_dec_eq(v_i_1695_, v_stop_1696_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v_diagnostics_1700_; lean_object* v_msgLog_1701_; lean_object* v___x_1702_; size_t v___x_1703_; size_t v___x_1704_; 
v___x_1699_ = lean_array_uget_borrowed(v_as_1694_, v_i_1695_);
v_diagnostics_1700_ = lean_ctor_get(v___x_1699_, 1);
v_msgLog_1701_ = lean_ctor_get(v_diagnostics_1700_, 0);
lean_inc_ref(v_msgLog_1701_);
v___x_1702_ = l_Lean_MessageLog_append(v_b_1697_, v_msgLog_1701_);
v___x_1703_ = ((size_t)1ULL);
v___x_1704_ = lean_usize_add(v_i_1695_, v___x_1703_);
v_i_1695_ = v___x_1704_;
v_b_1697_ = v___x_1702_;
goto _start;
}
else
{
return v_b_1697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0___boxed(lean_object* v_as_1706_, lean_object* v_i_1707_, lean_object* v_stop_1708_, lean_object* v_b_1709_){
_start:
{
size_t v_i_boxed_1710_; size_t v_stop_boxed_1711_; lean_object* v_res_1712_; 
v_i_boxed_1710_ = lean_unbox_usize(v_i_1707_);
lean_dec(v_i_1707_);
v_stop_boxed_1711_ = lean_unbox_usize(v_stop_1708_);
lean_dec(v_stop_1708_);
v_res_1712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v_as_1706_, v_i_boxed_1710_, v_stop_boxed_1711_, v_b_1709_);
lean_dec_ref(v_as_1706_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object* v_as_1713_, size_t v_i_1714_, size_t v_stop_1715_, lean_object* v_b_1716_){
_start:
{
lean_object* v___y_1718_; uint8_t v___x_1722_; 
v___x_1722_ = lean_usize_dec_eq(v_i_1714_, v_stop_1715_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1723_ = lean_array_uget_borrowed(v_as_1713_, v_i_1714_);
v___x_1724_ = l_Lean_MessageLog_empty;
lean_inc(v___x_1723_);
v___x_1725_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1723_);
v___x_1726_ = l_Lean_Language_SnapshotTree_getAll(v___x_1725_);
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = lean_array_get_size(v___x_1726_);
v___x_1729_ = lean_nat_dec_lt(v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref(v___x_1726_);
v___x_1730_ = l_Lean_MessageLog_append(v_b_1716_, v___x_1724_);
v___y_1718_ = v___x_1730_;
goto v___jp_1717_;
}
else
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_nat_dec_le(v___x_1728_, v___x_1728_);
if (v___x_1731_ == 0)
{
if (v___x_1729_ == 0)
{
lean_object* v___x_1732_; 
lean_dec_ref(v___x_1726_);
v___x_1732_ = l_Lean_MessageLog_append(v_b_1716_, v___x_1724_);
v___y_1718_ = v___x_1732_;
goto v___jp_1717_;
}
else
{
size_t v___x_1733_; size_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1733_ = ((size_t)0ULL);
v___x_1734_ = lean_usize_of_nat(v___x_1728_);
v___x_1735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1726_, v___x_1733_, v___x_1734_, v___x_1724_);
lean_dec_ref(v___x_1726_);
v___x_1736_ = l_Lean_MessageLog_append(v_b_1716_, v___x_1735_);
v___y_1718_ = v___x_1736_;
goto v___jp_1717_;
}
}
else
{
size_t v___x_1737_; size_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1737_ = ((size_t)0ULL);
v___x_1738_ = lean_usize_of_nat(v___x_1728_);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1726_, v___x_1737_, v___x_1738_, v___x_1724_);
lean_dec_ref(v___x_1726_);
v___x_1740_ = l_Lean_MessageLog_append(v_b_1716_, v___x_1739_);
v___y_1718_ = v___x_1740_;
goto v___jp_1717_;
}
}
}
else
{
return v_b_1716_;
}
v___jp_1717_:
{
size_t v___x_1719_; size_t v___x_1720_; 
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1714_, v___x_1719_);
v_i_1714_ = v___x_1720_;
v_b_1716_ = v___y_1718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1___boxed(lean_object* v_as_1741_, lean_object* v_i_1742_, lean_object* v_stop_1743_, lean_object* v_b_1744_){
_start:
{
size_t v_i_boxed_1745_; size_t v_stop_boxed_1746_; lean_object* v_res_1747_; 
v_i_boxed_1745_ = lean_unbox_usize(v_i_1742_);
lean_dec(v_i_1742_);
v_stop_boxed_1746_ = lean_unbox_usize(v_stop_1743_);
lean_dec(v_stop_1743_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_as_1741_, v_i_boxed_1745_, v_stop_boxed_1746_, v_b_1744_);
lean_dec_ref(v_as_1741_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object* v_cmd_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_fileName_1754_; lean_object* v_fileMap_1755_; lean_object* v_currRecDepth_1756_; lean_object* v_cmdPos_1757_; lean_object* v_macroStack_1758_; lean_object* v_quotContext_x3f_1759_; lean_object* v_currMacroScope_1760_; lean_object* v_ref_1761_; lean_object* v_cancelTk_x3f_1762_; uint8_t v_suppressElabErrors_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v_fileName_1754_ = lean_ctor_get(v_a_1751_, 0);
v_fileMap_1755_ = lean_ctor_get(v_a_1751_, 1);
v_currRecDepth_1756_ = lean_ctor_get(v_a_1751_, 2);
v_cmdPos_1757_ = lean_ctor_get(v_a_1751_, 3);
v_macroStack_1758_ = lean_ctor_get(v_a_1751_, 4);
v_quotContext_x3f_1759_ = lean_ctor_get(v_a_1751_, 5);
v_currMacroScope_1760_ = lean_ctor_get(v_a_1751_, 6);
v_ref_1761_ = lean_ctor_get(v_a_1751_, 7);
v_cancelTk_x3f_1762_ = lean_ctor_get(v_a_1751_, 9);
v_suppressElabErrors_1763_ = lean_ctor_get_uint8(v_a_1751_, sizeof(void*)*10);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
v___x_1766_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1762_);
lean_inc(v_ref_1761_);
lean_inc(v_currMacroScope_1760_);
lean_inc(v_quotContext_x3f_1759_);
lean_inc(v_macroStack_1758_);
lean_inc(v_cmdPos_1757_);
lean_inc(v_currRecDepth_1756_);
lean_inc_ref(v_fileMap_1755_);
lean_inc_ref(v_fileName_1754_);
v___x_1767_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1767_, 0, v_fileName_1754_);
lean_ctor_set(v___x_1767_, 1, v_fileMap_1755_);
lean_ctor_set(v___x_1767_, 2, v_currRecDepth_1756_);
lean_ctor_set(v___x_1767_, 3, v_cmdPos_1757_);
lean_ctor_set(v___x_1767_, 4, v_macroStack_1758_);
lean_ctor_set(v___x_1767_, 5, v_quotContext_x3f_1759_);
lean_ctor_set(v___x_1767_, 6, v_currMacroScope_1760_);
lean_ctor_set(v___x_1767_, 7, v_ref_1761_);
lean_ctor_set(v___x_1767_, 8, v___x_1766_);
lean_ctor_set(v___x_1767_, 9, v_cancelTk_x3f_1762_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*10, v_suppressElabErrors_1763_);
v___x_1768_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1750_, v___x_1765_, v___x_1767_, v_a_1752_);
lean_dec_ref_known(v___x_1767_, 10);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1813_; 
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v___x_1768_, 0);
lean_dec(v_unused_1814_);
v___x_1770_ = v___x_1768_;
v_isShared_1771_ = v_isSharedCheck_1813_;
goto v_resetjp_1769_;
}
else
{
lean_dec(v___x_1768_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1813_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v_messages_1774_; lean_object* v___y_1776_; lean_object* v_snapshotTasks_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1772_ = lean_st_ref_get(v_a_1752_);
v___x_1773_ = lean_st_ref_get(v_a_1752_);
v_messages_1774_ = lean_ctor_get(v___x_1772_, 1);
lean_inc_ref(v_messages_1774_);
lean_dec(v___x_1772_);
v_snapshotTasks_1802_ = lean_ctor_get(v___x_1773_, 10);
lean_inc_ref(v_snapshotTasks_1802_);
lean_dec(v___x_1773_);
v___x_1803_ = l_Lean_MessageLog_empty;
v___x_1804_ = lean_array_get_size(v_snapshotTasks_1802_);
v___x_1805_ = lean_nat_dec_lt(v___x_1764_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_dec_ref(v_snapshotTasks_1802_);
v___y_1776_ = v___x_1803_;
goto v___jp_1775_;
}
else
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_nat_dec_le(v___x_1804_, v___x_1804_);
if (v___x_1806_ == 0)
{
if (v___x_1805_ == 0)
{
lean_dec_ref(v_snapshotTasks_1802_);
v___y_1776_ = v___x_1803_;
goto v___jp_1775_;
}
else
{
size_t v___x_1807_; size_t v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = ((size_t)0ULL);
v___x_1808_ = lean_usize_of_nat(v___x_1804_);
v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1802_, v___x_1807_, v___x_1808_, v___x_1803_);
lean_dec_ref(v_snapshotTasks_1802_);
v___y_1776_ = v___x_1809_;
goto v___jp_1775_;
}
}
else
{
size_t v___x_1810_; size_t v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = ((size_t)0ULL);
v___x_1811_ = lean_usize_of_nat(v___x_1804_);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1802_, v___x_1810_, v___x_1811_, v___x_1803_);
lean_dec_ref(v_snapshotTasks_1802_);
v___y_1776_ = v___x_1812_;
goto v___jp_1775_;
}
}
v___jp_1775_:
{
lean_object* v___x_1777_; lean_object* v_env_1778_; lean_object* v_messages_1779_; lean_object* v_scopes_1780_; lean_object* v_usedQuotCtxts_1781_; lean_object* v_nextMacroScope_1782_; lean_object* v_maxRecDepth_1783_; lean_object* v_ngen_1784_; lean_object* v_auxDeclNGen_1785_; lean_object* v_infoState_1786_; lean_object* v_traceState_1787_; lean_object* v_prevLinterStates_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1800_; 
v___x_1777_ = lean_st_ref_take(v_a_1752_);
v_env_1778_ = lean_ctor_get(v___x_1777_, 0);
v_messages_1779_ = lean_ctor_get(v___x_1777_, 1);
v_scopes_1780_ = lean_ctor_get(v___x_1777_, 2);
v_usedQuotCtxts_1781_ = lean_ctor_get(v___x_1777_, 3);
v_nextMacroScope_1782_ = lean_ctor_get(v___x_1777_, 4);
v_maxRecDepth_1783_ = lean_ctor_get(v___x_1777_, 5);
v_ngen_1784_ = lean_ctor_get(v___x_1777_, 6);
v_auxDeclNGen_1785_ = lean_ctor_get(v___x_1777_, 7);
v_infoState_1786_ = lean_ctor_get(v___x_1777_, 8);
v_traceState_1787_ = lean_ctor_get(v___x_1777_, 9);
v_prevLinterStates_1788_ = lean_ctor_get(v___x_1777_, 11);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v___x_1777_, 10);
lean_dec(v_unused_1801_);
v___x_1790_ = v___x_1777_;
v_isShared_1791_ = v_isSharedCheck_1800_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_prevLinterStates_1788_);
lean_inc(v_traceState_1787_);
lean_inc(v_infoState_1786_);
lean_inc(v_auxDeclNGen_1785_);
lean_inc(v_ngen_1784_);
lean_inc(v_maxRecDepth_1783_);
lean_inc(v_nextMacroScope_1782_);
lean_inc(v_usedQuotCtxts_1781_);
lean_inc(v_scopes_1780_);
lean_inc(v_messages_1779_);
lean_inc(v_env_1778_);
lean_dec(v___x_1777_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1800_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 10, v___x_1765_);
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_env_1778_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_messages_1779_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_scopes_1780_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_usedQuotCtxts_1781_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_nextMacroScope_1782_);
lean_ctor_set(v_reuseFailAlloc_1799_, 5, v_maxRecDepth_1783_);
lean_ctor_set(v_reuseFailAlloc_1799_, 6, v_ngen_1784_);
lean_ctor_set(v_reuseFailAlloc_1799_, 7, v_auxDeclNGen_1785_);
lean_ctor_set(v_reuseFailAlloc_1799_, 8, v_infoState_1786_);
lean_ctor_set(v_reuseFailAlloc_1799_, 9, v_traceState_1787_);
lean_ctor_set(v_reuseFailAlloc_1799_, 10, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1799_, 11, v_prevLinterStates_1788_);
v___x_1793_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1794_ = lean_st_ref_put(v_a_1752_, v___x_1793_);
v___x_1795_ = l_Lean_MessageLog_append(v_messages_1774_, v___y_1776_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1795_);
v___x_1797_ = v___x_1770_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
v_a_1815_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1768_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1768_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1823_, v_a_1824_, v_a_1825_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
return v_res_1827_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1828_, lean_object* v_opt_1829_){
_start:
{
lean_object* v_name_1830_; lean_object* v_defValue_1831_; lean_object* v_map_1832_; lean_object* v___x_1833_; 
v_name_1830_ = lean_ctor_get(v_opt_1829_, 0);
v_defValue_1831_ = lean_ctor_get(v_opt_1829_, 1);
v_map_1832_ = lean_ctor_get(v_opts_1828_, 0);
v___x_1833_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1832_, v_name_1830_);
if (lean_obj_tag(v___x_1833_) == 0)
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_unbox(v_defValue_1831_);
return v___x_1834_;
}
else
{
lean_object* v_val_1835_; 
v_val_1835_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_val_1835_);
lean_dec_ref_known(v___x_1833_, 1);
if (lean_obj_tag(v_val_1835_) == 1)
{
uint8_t v_v_1836_; 
v_v_1836_ = lean_ctor_get_uint8(v_val_1835_, 0);
lean_dec_ref_known(v_val_1835_, 0);
return v_v_1836_;
}
else
{
uint8_t v___x_1837_; 
lean_dec(v_val_1835_);
v___x_1837_ = lean_unbox(v_defValue_1831_);
return v___x_1837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1838_, lean_object* v_opt_1839_){
_start:
{
uint8_t v_res_1840_; lean_object* v_r_1841_; 
v_res_1840_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1838_, v_opt_1839_);
lean_dec_ref(v_opt_1839_);
lean_dec_ref(v_opts_1838_);
v_r_1841_ = lean_box(v_res_1840_);
return v_r_1841_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0));
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1846_);
lean_dec_ref(v_s_1846_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_1848_, size_t v_sz_1849_, size_t v_i_1850_, lean_object* v_b_1851_){
_start:
{
lean_object* v_a_1853_; uint8_t v___x_1857_; 
v___x_1857_ = lean_usize_dec_lt(v_i_1850_, v_sz_1849_);
if (v___x_1857_ == 0)
{
return v_b_1851_;
}
else
{
lean_object* v_a_1858_; lean_object* v_fst_1859_; lean_object* v_snd_1860_; lean_object* v_out_1861_; uint8_t v___x_1862_; 
v_a_1858_ = lean_array_uget_borrowed(v_as_1848_, v_i_1850_);
v_fst_1859_ = lean_ctor_get(v_a_1858_, 0);
v_snd_1860_ = lean_ctor_get(v_a_1858_, 1);
v_out_1861_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1862_ = lean_string_dec_eq(v_snd_1860_, v_out_1861_);
if (v___x_1862_ == 0)
{
uint8_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1863_ = lean_unbox(v_fst_1859_);
v___x_1864_ = l_Lean_Diff_Action_linePrefix(v___x_1863_);
v___x_1865_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1866_ = lean_string_append(v___x_1864_, v___x_1865_);
v___x_1867_ = lean_string_append(v___x_1866_, v_snd_1860_);
v___x_1868_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1869_ = lean_string_append(v___x_1867_, v___x_1868_);
v___x_1870_ = lean_string_append(v_b_1851_, v___x_1869_);
lean_dec_ref(v___x_1869_);
v_a_1853_ = v___x_1870_;
goto v___jp_1852_;
}
else
{
uint8_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1871_ = lean_unbox(v_fst_1859_);
v___x_1872_ = l_Lean_Diff_Action_linePrefix(v___x_1871_);
v___x_1873_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1874_ = lean_string_append(v___x_1872_, v___x_1873_);
v___x_1875_ = lean_string_append(v_b_1851_, v___x_1874_);
lean_dec_ref(v___x_1874_);
v_a_1853_ = v___x_1875_;
goto v___jp_1852_;
}
}
v___jp_1852_:
{
size_t v___x_1854_; size_t v___x_1855_; 
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_add(v_i_1850_, v___x_1854_);
v_i_1850_ = v___x_1855_;
v_b_1851_ = v_a_1853_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_1876_, lean_object* v_sz_1877_, lean_object* v_i_1878_, lean_object* v_b_1879_){
_start:
{
size_t v_sz_boxed_1880_; size_t v_i_boxed_1881_; lean_object* v_res_1882_; 
v_sz_boxed_1880_ = lean_unbox_usize(v_sz_1877_);
lean_dec(v_sz_1877_);
v_i_boxed_1881_ = lean_unbox_usize(v_i_1878_);
lean_dec(v_i_1878_);
v_res_1882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_1876_, v_sz_boxed_1880_, v_i_boxed_1881_, v_b_1879_);
lean_dec_ref(v_as_1876_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_1883_){
_start:
{
lean_object* v_out_1884_; size_t v_sz_1885_; size_t v___x_1886_; lean_object* v___x_1887_; 
v_out_1884_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v_sz_1885_ = lean_array_size(v_lines_1883_);
v___x_1886_ = ((size_t)0ULL);
v___x_1887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_1883_, v_sz_1885_, v___x_1886_, v_out_1884_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_1888_);
lean_dec_ref(v_lines_1888_);
return v_res_1889_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1890_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
return v___x_1892_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
lean_ctor_set(v___x_1895_, 2, v___x_1894_);
lean_ctor_set(v___x_1895_, 3, v___x_1894_);
lean_ctor_set(v___x_1895_, 4, v___x_1893_);
lean_ctor_set(v___x_1895_, 5, v___x_1893_);
lean_ctor_set(v___x_1895_, 6, v___x_1893_);
lean_ctor_set(v___x_1895_, 7, v___x_1893_);
lean_ctor_set(v___x_1895_, 8, v___x_1893_);
lean_ctor_set(v___x_1895_, 9, v___x_1893_);
lean_ctor_set(v___x_1895_, 10, v___x_1893_);
return v___x_1895_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = lean_unsigned_to_nat(32u);
v___x_1897_ = lean_mk_empty_array_with_capacity(v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1899_ = ((size_t)5ULL);
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = lean_unsigned_to_nat(32u);
v___x_1902_ = lean_mk_empty_array_with_capacity(v___x_1901_);
v___x_1903_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1904_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v___x_1902_);
lean_ctor_set(v___x_1904_, 2, v___x_1900_);
lean_ctor_set(v___x_1904_, 3, v___x_1900_);
lean_ctor_set_usize(v___x_1904_, 4, v___x_1899_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1905_ = lean_box(1);
v___x_1906_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1907_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v___x_1906_);
lean_ctor_set(v___x_1908_, 2, v___x_1905_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; lean_object* v_env_1913_; lean_object* v___x_1914_; lean_object* v_scopes_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v_opts_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1912_ = lean_st_ref_get(v___y_1910_);
v_env_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc_ref(v_env_1913_);
lean_dec(v___x_1912_);
v___x_1914_ = lean_st_ref_get(v___y_1910_);
v_scopes_1915_ = lean_ctor_get(v___x_1914_, 2);
lean_inc(v_scopes_1915_);
lean_dec(v___x_1914_);
v___x_1916_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1917_ = l_List_head_x21___redArg(v___x_1916_, v_scopes_1915_);
lean_dec(v_scopes_1915_);
v_opts_1918_ = lean_ctor_get(v___x_1917_, 1);
lean_inc_ref(v_opts_1918_);
lean_dec(v___x_1917_);
v___x_1919_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1920_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1921_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1921_, 0, v_env_1913_);
lean_ctor_set(v___x_1921_, 1, v___x_1919_);
lean_ctor_set(v___x_1921_, 2, v___x_1920_);
lean_ctor_set(v___x_1921_, 3, v_opts_1918_);
v___x_1922_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v_msgData_1909_);
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1924_, v___y_1925_);
lean_dec(v___y_1925_);
return v_res_1927_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__0(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_box(1);
v___x_1929_ = l_Lean_MessageData_ofFormat(v___x_1928_);
return v___x_1929_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__3(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__2));
v___x_1934_ = l_Lean_MessageData_ofFormat(v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45(lean_object* v_x_1935_, lean_object* v_x_1936_){
_start:
{
if (lean_obj_tag(v_x_1936_) == 0)
{
return v_x_1935_;
}
else
{
lean_object* v_head_1937_; lean_object* v_tail_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1960_; 
v_head_1937_ = lean_ctor_get(v_x_1936_, 0);
v_tail_1938_ = lean_ctor_get(v_x_1936_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_x_1936_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1940_ = v_x_1936_;
v_isShared_1941_ = v_isSharedCheck_1960_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_tail_1938_);
lean_inc(v_head_1937_);
lean_dec(v_x_1936_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1960_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_before_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1958_; 
v_before_1942_ = lean_ctor_get(v_head_1937_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_head_1937_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; 
v_unused_1959_ = lean_ctor_get(v_head_1937_, 1);
lean_dec(v_unused_1959_);
v___x_1944_ = v_head_1937_;
v_isShared_1945_ = v_isSharedCheck_1958_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_before_1942_);
lean_dec(v_head_1937_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1958_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__0);
if (v_isShared_1945_ == 0)
{
lean_ctor_set_tag(v___x_1944_, 7);
lean_ctor_set(v___x_1944_, 1, v___x_1946_);
lean_ctor_set(v___x_1944_, 0, v_x_1935_);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_x_1935_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1949_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__3);
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 7);
lean_ctor_set(v___x_1940_, 1, v___x_1949_);
lean_ctor_set(v___x_1940_, 0, v___x_1948_);
v___x_1951_ = v___x_1940_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = l_Lean_MessageData_ofSyntax(v_before_1942_);
v___x_1953_ = l_Lean_indentD(v___x_1952_);
v___x_1954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1951_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v_x_1935_ = v___x_1954_;
v_x_1936_ = v_tail_1938_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__2(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__1));
v___x_1965_ = l_Lean_MessageData_ofFormat(v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg(lean_object* v_msgData_1966_, lean_object* v_macroStack_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___x_1970_; lean_object* v_scopes_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_opts_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1970_ = lean_st_ref_get(v___y_1968_);
v_scopes_1971_ = lean_ctor_get(v___x_1970_, 2);
lean_inc(v_scopes_1971_);
lean_dec(v___x_1970_);
v___x_1972_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1973_ = l_List_head_x21___redArg(v___x_1972_, v_scopes_1971_);
lean_dec(v_scopes_1971_);
v_opts_1974_ = lean_ctor_get(v___x_1973_, 1);
lean_inc_ref(v_opts_1974_);
lean_dec(v___x_1973_);
v___x_1975_ = l_Lean_Elab_pp_macroStack;
v___x_1976_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1974_, v___x_1975_);
lean_dec_ref(v_opts_1974_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_dec(v_macroStack_1967_);
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_msgData_1966_);
return v___x_1977_;
}
else
{
if (lean_obj_tag(v_macroStack_1967_) == 0)
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v_msgData_1966_);
return v___x_1978_;
}
else
{
lean_object* v_head_1979_; lean_object* v_after_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1995_; 
v_head_1979_ = lean_ctor_get(v_macroStack_1967_, 0);
lean_inc(v_head_1979_);
v_after_1980_ = lean_ctor_get(v_head_1979_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_head_1979_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v_head_1979_, 0);
lean_dec(v_unused_1996_);
v___x_1982_ = v_head_1979_;
v_isShared_1983_ = v_isSharedCheck_1995_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_after_1980_);
lean_dec(v_head_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1995_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45___closed__0);
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 7);
lean_ctor_set(v___x_1982_, 1, v___x_1984_);
lean_ctor_set(v___x_1982_, 0, v_msgData_1966_);
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_msgData_1966_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v_msgData_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1987_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___closed__2);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = l_Lean_MessageData_ofSyntax(v_after_1980_);
v___x_1990_ = l_Lean_indentD(v___x_1989_);
v_msgData_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1991_, 0, v___x_1988_);
lean_ctor_set(v_msgData_1991_, 1, v___x_1990_);
v___x_1992_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40_spec__45(v_msgData_1991_, v_macroStack_1967_);
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
return v___x_1993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg___boxed(lean_object* v_msgData_1997_, lean_object* v_macroStack_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg(v_msgData_1997_, v_macroStack_1998_, v___y_1999_);
lean_dec(v___y_1999_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34___redArg(lean_object* v_msg_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_Elab_Command_getRef___redArg(v___y_2003_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v_macroStack_2008_; lean_object* v___x_2009_; lean_object* v_a_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2021_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v_macroStack_2008_ = lean_ctor_get(v___y_2003_, 4);
v___x_2009_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_2002_, v___y_2004_);
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_2009_);
v___x_2011_ = l_Lean_Elab_getBetterRef(v_a_2007_, v_macroStack_2008_);
lean_dec(v_a_2007_);
lean_inc(v_macroStack_2008_);
v___x_2012_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg(v_a_2010_, v_macroStack_2008_, v___y_2004_);
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2011_);
lean_ctor_set(v___x_2017_, 1, v_a_2013_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set_tag(v___x_2015_, 1);
lean_ctor_set(v___x_2015_, 0, v___x_2017_);
v___x_2019_ = v___x_2015_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec_ref(v_msg_2002_);
v_a_2022_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2006_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2006_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34___redArg___boxed(lean_object* v_msg_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34___redArg(v_msg_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_2035_, lean_object* v_msg_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_Elab_Command_getRef___redArg(v___y_2037_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v_fileName_2042_; lean_object* v_fileMap_2043_; lean_object* v_currRecDepth_2044_; lean_object* v_cmdPos_2045_; lean_object* v_macroStack_2046_; lean_object* v_quotContext_x3f_2047_; lean_object* v_currMacroScope_2048_; lean_object* v_snap_x3f_2049_; lean_object* v_cancelTk_x3f_2050_; uint8_t v_suppressElabErrors_2051_; lean_object* v_ref_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v_fileName_2042_ = lean_ctor_get(v___y_2037_, 0);
v_fileMap_2043_ = lean_ctor_get(v___y_2037_, 1);
v_currRecDepth_2044_ = lean_ctor_get(v___y_2037_, 2);
v_cmdPos_2045_ = lean_ctor_get(v___y_2037_, 3);
v_macroStack_2046_ = lean_ctor_get(v___y_2037_, 4);
v_quotContext_x3f_2047_ = lean_ctor_get(v___y_2037_, 5);
v_currMacroScope_2048_ = lean_ctor_get(v___y_2037_, 6);
v_snap_x3f_2049_ = lean_ctor_get(v___y_2037_, 8);
v_cancelTk_x3f_2050_ = lean_ctor_get(v___y_2037_, 9);
v_suppressElabErrors_2051_ = lean_ctor_get_uint8(v___y_2037_, sizeof(void*)*10);
v_ref_2052_ = l_Lean_replaceRef(v_ref_2035_, v_a_2041_);
lean_dec(v_a_2041_);
lean_inc(v_cancelTk_x3f_2050_);
lean_inc(v_snap_x3f_2049_);
lean_inc(v_currMacroScope_2048_);
lean_inc(v_quotContext_x3f_2047_);
lean_inc(v_macroStack_2046_);
lean_inc(v_cmdPos_2045_);
lean_inc(v_currRecDepth_2044_);
lean_inc_ref(v_fileMap_2043_);
lean_inc_ref(v_fileName_2042_);
v___x_2053_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2053_, 0, v_fileName_2042_);
lean_ctor_set(v___x_2053_, 1, v_fileMap_2043_);
lean_ctor_set(v___x_2053_, 2, v_currRecDepth_2044_);
lean_ctor_set(v___x_2053_, 3, v_cmdPos_2045_);
lean_ctor_set(v___x_2053_, 4, v_macroStack_2046_);
lean_ctor_set(v___x_2053_, 5, v_quotContext_x3f_2047_);
lean_ctor_set(v___x_2053_, 6, v_currMacroScope_2048_);
lean_ctor_set(v___x_2053_, 7, v_ref_2052_);
lean_ctor_set(v___x_2053_, 8, v_snap_x3f_2049_);
lean_ctor_set(v___x_2053_, 9, v_cancelTk_x3f_2050_);
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*10, v_suppressElabErrors_2051_);
v___x_2054_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34___redArg(v_msg_2036_, v___x_2053_, v___y_2038_);
lean_dec_ref_known(v___x_2053_, 10);
return v___x_2054_;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref(v_msg_2036_);
v_a_2055_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2040_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2040_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_2063_, lean_object* v_msg_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_2063_, v_msg_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v_ref_2063_);
return v_res_2068_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_2071_ = l_Lean_stringToMessageData(v___x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_val_2086_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = l_Lean_Syntax_getArg(v_stx_2075_, v___x_2093_);
switch(lean_obj_tag(v___x_2094_))
{
case 2:
{
lean_object* v_val_2095_; 
lean_dec(v_stx_2075_);
v_val_2095_ = lean_ctor_get(v___x_2094_, 1);
lean_inc_ref(v_val_2095_);
lean_dec_ref_known(v___x_2094_, 2);
v_val_2086_ = v_val_2095_;
goto v___jp_2085_;
}
case 1:
{
lean_object* v_kind_2096_; 
v_kind_2096_ = lean_ctor_get(v___x_2094_, 1);
lean_inc(v_kind_2096_);
if (lean_obj_tag(v_kind_2096_) == 1)
{
lean_object* v_pre_2097_; 
v_pre_2097_ = lean_ctor_get(v_kind_2096_, 0);
lean_inc(v_pre_2097_);
if (lean_obj_tag(v_pre_2097_) == 1)
{
lean_object* v_pre_2098_; 
v_pre_2098_ = lean_ctor_get(v_pre_2097_, 0);
lean_inc(v_pre_2098_);
if (lean_obj_tag(v_pre_2098_) == 1)
{
lean_object* v_pre_2099_; 
v_pre_2099_ = lean_ctor_get(v_pre_2098_, 0);
lean_inc(v_pre_2099_);
if (lean_obj_tag(v_pre_2099_) == 1)
{
lean_object* v_pre_2100_; 
v_pre_2100_ = lean_ctor_get(v_pre_2099_, 0);
if (lean_obj_tag(v_pre_2100_) == 0)
{
lean_object* v_str_2101_; lean_object* v_str_2102_; lean_object* v_str_2103_; lean_object* v_str_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_str_2101_ = lean_ctor_get(v_kind_2096_, 1);
lean_inc_ref(v_str_2101_);
lean_dec_ref_known(v_kind_2096_, 2);
v_str_2102_ = lean_ctor_get(v_pre_2097_, 1);
lean_inc_ref(v_str_2102_);
lean_dec_ref_known(v_pre_2097_, 2);
v_str_2103_ = lean_ctor_get(v_pre_2098_, 1);
lean_inc_ref(v_str_2103_);
lean_dec_ref_known(v_pre_2098_, 2);
v_str_2104_ = lean_ctor_get(v_pre_2099_, 1);
lean_inc_ref(v_str_2104_);
lean_dec_ref_known(v_pre_2099_, 2);
v___x_2105_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_2106_ = lean_string_dec_eq(v_str_2104_, v___x_2105_);
lean_dec_ref(v_str_2104_);
if (v___x_2106_ == 0)
{
lean_dec_ref(v_str_2103_);
lean_dec_ref(v_str_2102_);
lean_dec_ref(v_str_2101_);
lean_dec_ref_known(v___x_2094_, 3);
goto v___jp_2079_;
}
else
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2108_ = lean_string_dec_eq(v_str_2103_, v___x_2107_);
lean_dec_ref(v_str_2103_);
if (v___x_2108_ == 0)
{
lean_dec_ref(v_str_2102_);
lean_dec_ref(v_str_2101_);
lean_dec_ref_known(v___x_2094_, 3);
goto v___jp_2079_;
}
else
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2110_ = lean_string_dec_eq(v_str_2102_, v___x_2109_);
lean_dec_ref(v_str_2102_);
if (v___x_2110_ == 0)
{
lean_dec_ref(v_str_2101_);
lean_dec_ref_known(v___x_2094_, 3);
goto v___jp_2079_;
}
else
{
lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2112_ = lean_string_dec_eq(v_str_2101_, v___x_2111_);
lean_dec_ref(v_str_2101_);
if (v___x_2112_ == 0)
{
lean_dec_ref_known(v___x_2094_, 3);
goto v___jp_2079_;
}
else
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2114_ = l_Lean_Syntax_getArg(v___x_2094_, v___x_2113_);
lean_dec_ref_known(v___x_2094_, 3);
if (lean_obj_tag(v___x_2114_) == 2)
{
lean_object* v_val_2115_; 
lean_dec(v_stx_2075_);
v_val_2115_ = lean_ctor_get(v___x_2114_, 1);
lean_inc_ref(v_val_2115_);
lean_dec_ref_known(v___x_2114_, 2);
v_val_2086_ = v_val_2115_;
goto v___jp_2085_;
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_dec(v___x_2114_);
v___x_2116_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2075_);
v___x_2117_ = l_Lean_MessageData_ofSyntax(v_stx_2075_);
v___x_2118_ = l_Lean_indentD(v___x_2117_);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2116_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2075_, v___x_2119_, v___y_2076_, v___y_2077_);
lean_dec(v_stx_2075_);
return v___x_2120_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2099_, 2);
lean_dec_ref_known(v_pre_2098_, 2);
lean_dec_ref_known(v_pre_2097_, 2);
lean_dec_ref_known(v_kind_2096_, 2);
lean_dec_ref_known(v___x_2094_, 3);
goto v___jp_2079_;
}
}
else
{
lean_dec(v_pre_2099_);
lean_dec_ref_known(v_pre_2098_, 2);
lean_dec_ref_known(v_pre_2097_, 2);
lean_dec_ref_known(v_kind_2096_, 2);
lean_dec_ref_known(v___x_2094_, 3);
goto v___jp_2079_;
}
}
else
{
lean_dec(v_pre_2098_);
lean_dec_ref_known(v_pre_2097_, 2);
lean_dec_ref_known(v_kind_2096_, 2);
lean_dec_ref_known(v___x_2094_, 3);
goto v___jp_2079_;
}
}
else
{
lean_dec_ref_known(v_kind_2096_, 2);
lean_dec(v_pre_2097_);
lean_dec_ref_known(v___x_2094_, 3);
goto v___jp_2079_;
}
}
else
{
lean_dec_ref_known(v___x_2094_, 3);
lean_dec(v_kind_2096_);
goto v___jp_2079_;
}
}
default: 
{
lean_dec(v___x_2094_);
goto v___jp_2079_;
}
}
v___jp_2079_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2080_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2075_);
v___x_2081_ = l_Lean_MessageData_ofSyntax(v_stx_2075_);
v___x_2082_ = l_Lean_indentD(v___x_2081_);
v___x_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2080_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2075_, v___x_2083_, v___y_2076_, v___y_2077_);
lean_dec(v_stx_2075_);
return v___x_2084_;
}
v___jp_2085_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = lean_string_utf8_byte_size(v_val_2086_);
v___x_2089_ = lean_unsigned_to_nat(2u);
v___x_2090_ = lean_nat_sub(v___x_2088_, v___x_2089_);
v___x_2091_ = lean_string_utf8_extract(v_val_2086_, v___x_2087_, v___x_2090_);
lean_dec(v___x_2090_);
lean_dec_ref(v_val_2086_);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2126_, lean_object* v_as_x27_2127_, lean_object* v_b_2128_){
_start:
{
if (lean_obj_tag(v_as_x27_2127_) == 0)
{
lean_object* v___x_2130_; 
lean_dec_ref(v_filterFn_2126_);
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v_b_2128_);
return v___x_2130_;
}
else
{
lean_object* v_head_2131_; uint8_t v_isSilent_2132_; 
v_head_2131_ = lean_ctor_get(v_as_x27_2127_, 0);
v_isSilent_2132_ = lean_ctor_get_uint8(v_head_2131_, sizeof(void*)*5 + 2);
if (v_isSilent_2132_ == 0)
{
lean_object* v_tail_2133_; lean_object* v_fst_2134_; lean_object* v_snd_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2155_; 
v_tail_2133_ = lean_ctor_get(v_as_x27_2127_, 1);
v_fst_2134_ = lean_ctor_get(v_b_2128_, 0);
v_snd_2135_ = lean_ctor_get(v_b_2128_, 1);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_b_2128_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2137_ = v_b_2128_;
v_isShared_2138_ = v_isSharedCheck_2155_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_snd_2135_);
lean_inc(v_fst_2134_);
lean_dec(v_b_2128_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2155_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
lean_inc_ref(v_filterFn_2126_);
lean_inc(v_head_2131_);
v___x_2139_ = lean_apply_1(v_filterFn_2126_, v_head_2131_);
v___x_2140_ = lean_unbox(v___x_2139_);
switch(v___x_2140_)
{
case 0:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
lean_inc(v_head_2131_);
v___x_2141_ = l_Lean_MessageLog_add(v_head_2131_, v_fst_2134_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2141_);
v___x_2143_ = v___x_2137_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_snd_2135_);
v___x_2143_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
v_as_x27_2127_ = v_tail_2133_;
v_b_2128_ = v___x_2143_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2147_; 
if (v_isShared_2138_ == 0)
{
v___x_2147_ = v___x_2137_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_fst_2134_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_snd_2135_);
v___x_2147_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
v_as_x27_2127_ = v_tail_2133_;
v_b_2128_ = v___x_2147_;
goto _start;
}
}
default: 
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
lean_inc(v_head_2131_);
v___x_2150_ = l_Lean_MessageLog_add(v_head_2131_, v_snd_2135_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 1, v___x_2150_);
v___x_2152_ = v___x_2137_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_fst_2134_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
v_as_x27_2127_ = v_tail_2133_;
v_b_2128_ = v___x_2152_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2156_; lean_object* v_fst_2157_; lean_object* v_snd_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2166_; 
v_tail_2156_ = lean_ctor_get(v_as_x27_2127_, 1);
v_fst_2157_ = lean_ctor_get(v_b_2128_, 0);
v_snd_2158_ = lean_ctor_get(v_b_2128_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_b_2128_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2160_ = v_b_2128_;
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_snd_2158_);
lean_inc(v_fst_2157_);
lean_dec(v_b_2128_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_fst_2157_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_snd_2158_);
v___x_2163_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
v_as_x27_2127_ = v_tail_2156_;
v_b_2128_ = v___x_2163_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2167_, lean_object* v_as_x27_2168_, lean_object* v_b_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2167_, v_as_x27_2168_, v_b_2169_);
lean_dec(v_as_x27_2168_);
return v_res_2171_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v___y_2172_, uint8_t v_suppressElabErrors_2173_, lean_object* v_x_2174_){
_start:
{
if (lean_obj_tag(v_x_2174_) == 1)
{
lean_object* v_pre_2175_; 
v_pre_2175_ = lean_ctor_get(v_x_2174_, 0);
if (lean_obj_tag(v_pre_2175_) == 0)
{
lean_object* v_str_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v_str_2176_ = lean_ctor_get(v_x_2174_, 1);
v___x_2177_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2178_ = lean_string_dec_eq(v_str_2176_, v___x_2177_);
if (v___x_2178_ == 0)
{
return v___y_2172_;
}
else
{
return v_suppressElabErrors_2173_;
}
}
else
{
return v___y_2172_;
}
}
else
{
return v___y_2172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v___y_2179_, lean_object* v_suppressElabErrors_2180_, lean_object* v_x_2181_){
_start:
{
uint8_t v___y_29960__boxed_2182_; uint8_t v_suppressElabErrors_boxed_2183_; uint8_t v_res_2184_; lean_object* v_r_2185_; 
v___y_29960__boxed_2182_ = lean_unbox(v___y_2179_);
v_suppressElabErrors_boxed_2183_ = lean_unbox(v_suppressElabErrors_2180_);
v_res_2184_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v___y_29960__boxed_2182_, v_suppressElabErrors_boxed_2183_, v_x_2181_);
lean_dec(v_x_2181_);
v_r_2185_ = lean_box(v_res_2184_);
return v_r_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2186_, lean_object* v_msgData_2187_, uint8_t v_severity_2188_, uint8_t v_isSilent_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___y_2194_; lean_object* v___y_2195_; uint8_t v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; uint8_t v___y_2200_; lean_object* v___y_2201_; uint8_t v___y_2258_; uint8_t v___y_2259_; lean_object* v___y_2260_; uint8_t v___y_2261_; lean_object* v___y_2262_; uint8_t v___y_2286_; uint8_t v___y_2287_; lean_object* v___y_2288_; uint8_t v___y_2289_; lean_object* v___y_2290_; uint8_t v___y_2294_; uint8_t v___y_2295_; uint8_t v___y_2296_; uint8_t v___x_2311_; uint8_t v___y_2313_; uint8_t v___y_2314_; uint8_t v___y_2315_; uint8_t v___y_2317_; uint8_t v___x_2329_; 
v___x_2311_ = 2;
v___x_2329_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2188_, v___x_2311_);
if (v___x_2329_ == 0)
{
v___y_2317_ = v___x_2329_;
goto v___jp_2316_;
}
else
{
uint8_t v___x_2330_; 
lean_inc_ref(v_msgData_2187_);
v___x_2330_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2187_);
v___y_2317_ = v___x_2330_;
goto v___jp_2316_;
}
v___jp_2193_:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_Elab_Command_getScope___redArg(v___y_2201_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = l_Lean_Elab_Command_getScope___redArg(v___y_2201_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2240_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2240_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2240_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v_currNamespace_2210_; lean_object* v_openDecls_2211_; lean_object* v_env_2212_; lean_object* v_messages_2213_; lean_object* v_scopes_2214_; lean_object* v_usedQuotCtxts_2215_; lean_object* v_nextMacroScope_2216_; lean_object* v_maxRecDepth_2217_; lean_object* v_ngen_2218_; lean_object* v_auxDeclNGen_2219_; lean_object* v_infoState_2220_; lean_object* v_traceState_2221_; lean_object* v_snapshotTasks_2222_; lean_object* v_prevLinterStates_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2239_; 
v___x_2209_ = lean_st_ref_take(v___y_2201_);
v_currNamespace_2210_ = lean_ctor_get(v_a_2203_, 2);
lean_inc(v_currNamespace_2210_);
lean_dec(v_a_2203_);
v_openDecls_2211_ = lean_ctor_get(v_a_2205_, 3);
lean_inc(v_openDecls_2211_);
lean_dec(v_a_2205_);
v_env_2212_ = lean_ctor_get(v___x_2209_, 0);
v_messages_2213_ = lean_ctor_get(v___x_2209_, 1);
v_scopes_2214_ = lean_ctor_get(v___x_2209_, 2);
v_usedQuotCtxts_2215_ = lean_ctor_get(v___x_2209_, 3);
v_nextMacroScope_2216_ = lean_ctor_get(v___x_2209_, 4);
v_maxRecDepth_2217_ = lean_ctor_get(v___x_2209_, 5);
v_ngen_2218_ = lean_ctor_get(v___x_2209_, 6);
v_auxDeclNGen_2219_ = lean_ctor_get(v___x_2209_, 7);
v_infoState_2220_ = lean_ctor_get(v___x_2209_, 8);
v_traceState_2221_ = lean_ctor_get(v___x_2209_, 9);
v_snapshotTasks_2222_ = lean_ctor_get(v___x_2209_, 10);
v_prevLinterStates_2223_ = lean_ctor_get(v___x_2209_, 11);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2225_ = v___x_2209_;
v_isShared_2226_ = v_isSharedCheck_2239_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_prevLinterStates_2223_);
lean_inc(v_snapshotTasks_2222_);
lean_inc(v_traceState_2221_);
lean_inc(v_infoState_2220_);
lean_inc(v_auxDeclNGen_2219_);
lean_inc(v_ngen_2218_);
lean_inc(v_maxRecDepth_2217_);
lean_inc(v_nextMacroScope_2216_);
lean_inc(v_usedQuotCtxts_2215_);
lean_inc(v_scopes_2214_);
lean_inc(v_messages_2213_);
lean_inc(v_env_2212_);
lean_dec(v___x_2209_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2239_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2227_, 0, v_currNamespace_2210_);
lean_ctor_set(v___x_2227_, 1, v_openDecls_2211_);
v___x_2228_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v___y_2199_);
lean_inc_ref(v___y_2197_);
lean_inc_ref(v___y_2195_);
v___x_2229_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2229_, 0, v___y_2195_);
lean_ctor_set(v___x_2229_, 1, v___y_2194_);
lean_ctor_set(v___x_2229_, 2, v___y_2198_);
lean_ctor_set(v___x_2229_, 3, v___y_2197_);
lean_ctor_set(v___x_2229_, 4, v___x_2228_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*5, v___y_2200_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*5 + 1, v___y_2196_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*5 + 2, v_isSilent_2189_);
v___x_2230_ = l_Lean_MessageLog_add(v___x_2229_, v_messages_2213_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 1, v___x_2230_);
v___x_2232_ = v___x_2225_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_env_2212_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_scopes_2214_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_usedQuotCtxts_2215_);
lean_ctor_set(v_reuseFailAlloc_2238_, 4, v_nextMacroScope_2216_);
lean_ctor_set(v_reuseFailAlloc_2238_, 5, v_maxRecDepth_2217_);
lean_ctor_set(v_reuseFailAlloc_2238_, 6, v_ngen_2218_);
lean_ctor_set(v_reuseFailAlloc_2238_, 7, v_auxDeclNGen_2219_);
lean_ctor_set(v_reuseFailAlloc_2238_, 8, v_infoState_2220_);
lean_ctor_set(v_reuseFailAlloc_2238_, 9, v_traceState_2221_);
lean_ctor_set(v_reuseFailAlloc_2238_, 10, v_snapshotTasks_2222_);
lean_ctor_set(v_reuseFailAlloc_2238_, 11, v_prevLinterStates_2223_);
v___x_2232_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2233_ = lean_st_ref_put(v___y_2201_, v___x_2232_);
v___x_2234_ = lean_box(0);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2234_);
v___x_2236_ = v___x_2207_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_a_2203_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2194_);
v_a_2241_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2204_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2204_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2194_);
v_a_2249_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2202_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2202_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
v___jp_2257_:
{
lean_object* v_fileName_2263_; lean_object* v_fileMap_2264_; uint8_t v_suppressElabErrors_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2284_; 
v_fileName_2263_ = lean_ctor_get(v___y_2190_, 0);
v_fileMap_2264_ = lean_ctor_get(v___y_2190_, 1);
v_suppressElabErrors_2265_ = lean_ctor_get_uint8(v___y_2190_, sizeof(void*)*10);
v___x_2266_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2187_);
v___x_2267_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2266_, v___y_2191_);
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2270_ = v___x_2267_;
v_isShared_2271_ = v_isSharedCheck_2284_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2267_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2284_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_inc_ref_n(v_fileMap_2264_, 2);
v___x_2272_ = l_Lean_FileMap_toPosition(v_fileMap_2264_, v___y_2260_);
lean_dec(v___y_2260_);
v___x_2273_ = l_Lean_FileMap_toPosition(v_fileMap_2264_, v___y_2262_);
lean_dec(v___y_2262_);
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
v___x_2275_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
if (v_suppressElabErrors_2265_ == 0)
{
lean_del_object(v___x_2270_);
v___y_2194_ = v___x_2272_;
v___y_2195_ = v_fileName_2263_;
v___y_2196_ = v___y_2259_;
v___y_2197_ = v___x_2275_;
v___y_2198_ = v___x_2274_;
v___y_2199_ = v_a_2268_;
v___y_2200_ = v___y_2261_;
v___y_2201_ = v___y_2191_;
goto v___jp_2193_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___f_2278_; uint8_t v___x_2279_; 
v___x_2276_ = lean_box(v___y_2258_);
v___x_2277_ = lean_box(v_suppressElabErrors_2265_);
v___f_2278_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2278_, 0, v___x_2276_);
lean_closure_set(v___f_2278_, 1, v___x_2277_);
lean_inc(v_a_2268_);
v___x_2279_ = l_Lean_MessageData_hasTag(v___f_2278_, v_a_2268_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
lean_dec_ref_known(v___x_2274_, 1);
lean_dec_ref(v___x_2272_);
lean_dec(v_a_2268_);
v___x_2280_ = lean_box(0);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2280_);
v___x_2282_ = v___x_2270_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
else
{
lean_del_object(v___x_2270_);
v___y_2194_ = v___x_2272_;
v___y_2195_ = v_fileName_2263_;
v___y_2196_ = v___y_2259_;
v___y_2197_ = v___x_2275_;
v___y_2198_ = v___x_2274_;
v___y_2199_ = v_a_2268_;
v___y_2200_ = v___y_2261_;
v___y_2201_ = v___y_2191_;
goto v___jp_2193_;
}
}
}
}
v___jp_2285_:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_Syntax_getTailPos_x3f(v___y_2288_, v___y_2289_);
lean_dec(v___y_2288_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_inc(v___y_2290_);
v___y_2258_ = v___y_2286_;
v___y_2259_ = v___y_2287_;
v___y_2260_ = v___y_2290_;
v___y_2261_ = v___y_2289_;
v___y_2262_ = v___y_2290_;
goto v___jp_2257_;
}
else
{
lean_object* v_val_2292_; 
v_val_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_val_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v___y_2258_ = v___y_2286_;
v___y_2259_ = v___y_2287_;
v___y_2260_ = v___y_2290_;
v___y_2261_ = v___y_2289_;
v___y_2262_ = v_val_2292_;
goto v___jp_2257_;
}
}
v___jp_2293_:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Elab_Command_getRef___redArg(v___y_2190_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v_ref_2299_; lean_object* v___x_2300_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v_ref_2299_ = l_Lean_replaceRef(v_ref_2186_, v_a_2298_);
lean_dec(v_a_2298_);
v___x_2300_ = l_Lean_Syntax_getPos_x3f(v_ref_2299_, v___y_2295_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_unsigned_to_nat(0u);
v___y_2286_ = v___y_2294_;
v___y_2287_ = v___y_2296_;
v___y_2288_ = v_ref_2299_;
v___y_2289_ = v___y_2295_;
v___y_2290_ = v___x_2301_;
goto v___jp_2285_;
}
else
{
lean_object* v_val_2302_; 
v_val_2302_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_val_2302_);
lean_dec_ref_known(v___x_2300_, 1);
v___y_2286_ = v___y_2294_;
v___y_2287_ = v___y_2296_;
v___y_2288_ = v_ref_2299_;
v___y_2289_ = v___y_2295_;
v___y_2290_ = v_val_2302_;
goto v___jp_2285_;
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref(v_msgData_2187_);
v_a_2303_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2297_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2297_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
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
v___jp_2312_:
{
if (v___y_2315_ == 0)
{
v___y_2294_ = v___y_2313_;
v___y_2295_ = v___y_2314_;
v___y_2296_ = v_severity_2188_;
goto v___jp_2293_;
}
else
{
v___y_2294_ = v___y_2313_;
v___y_2295_ = v___y_2314_;
v___y_2296_ = v___x_2311_;
goto v___jp_2293_;
}
}
v___jp_2316_:
{
if (v___y_2317_ == 0)
{
lean_object* v___x_2318_; lean_object* v_scopes_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v_opts_2322_; uint8_t v___x_2323_; uint8_t v___x_2324_; 
v___x_2318_ = lean_st_ref_get(v___y_2191_);
v_scopes_2319_ = lean_ctor_get(v___x_2318_, 2);
lean_inc(v_scopes_2319_);
lean_dec(v___x_2318_);
v___x_2320_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2321_ = l_List_head_x21___redArg(v___x_2320_, v_scopes_2319_);
lean_dec(v_scopes_2319_);
v_opts_2322_ = lean_ctor_get(v___x_2321_, 1);
lean_inc_ref(v_opts_2322_);
lean_dec(v___x_2321_);
v___x_2323_ = 1;
v___x_2324_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2188_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_dec_ref(v_opts_2322_);
v___y_2313_ = v___y_2317_;
v___y_2314_ = v___y_2317_;
v___y_2315_ = v___x_2324_;
goto v___jp_2312_;
}
else
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = l_Lean_warningAsError;
v___x_2326_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2322_, v___x_2325_);
lean_dec_ref(v_opts_2322_);
v___y_2313_ = v___y_2317_;
v___y_2314_ = v___y_2317_;
v___y_2315_ = v___x_2326_;
goto v___jp_2312_;
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_dec_ref(v_msgData_2187_);
v___x_2327_ = lean_box(0);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
return v___x_2328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2331_, lean_object* v_msgData_2332_, lean_object* v_severity_2333_, lean_object* v_isSilent_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
uint8_t v_severity_boxed_2338_; uint8_t v_isSilent_boxed_2339_; lean_object* v_res_2340_; 
v_severity_boxed_2338_ = lean_unbox(v_severity_2333_);
v_isSilent_boxed_2339_ = lean_unbox(v_isSilent_2334_);
v_res_2340_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2331_, v_msgData_2332_, v_severity_boxed_2338_, v_isSilent_boxed_2339_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v_ref_2331_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2341_, lean_object* v_msgData_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
uint8_t v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; 
v___x_2346_ = 2;
v___x_2347_ = 0;
v___x_2348_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2341_, v_msgData_2342_, v___x_2346_, v___x_2347_, v___y_2343_, v___y_2344_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2349_, lean_object* v_msgData_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2349_, v_msgData_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v_ref_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; lean_object* v_infoState_2359_; uint8_t v_enabled_2360_; 
v___x_2358_ = lean_st_ref_get(v___y_2356_);
v_infoState_2359_ = lean_ctor_get(v___x_2358_, 8);
lean_inc_ref(v_infoState_2359_);
lean_dec(v___x_2358_);
v_enabled_2360_ = lean_ctor_get_uint8(v_infoState_2359_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2359_);
if (v_enabled_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec_ref(v_t_2355_);
v___x_2361_ = lean_box(0);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
return v___x_2362_;
}
else
{
lean_object* v___x_2363_; lean_object* v_infoState_2364_; lean_object* v_env_2365_; lean_object* v_messages_2366_; lean_object* v_scopes_2367_; lean_object* v_usedQuotCtxts_2368_; lean_object* v_nextMacroScope_2369_; lean_object* v_maxRecDepth_2370_; lean_object* v_ngen_2371_; lean_object* v_auxDeclNGen_2372_; lean_object* v_traceState_2373_; lean_object* v_snapshotTasks_2374_; lean_object* v_prevLinterStates_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2397_; 
v___x_2363_ = lean_st_ref_take(v___y_2356_);
v_infoState_2364_ = lean_ctor_get(v___x_2363_, 8);
v_env_2365_ = lean_ctor_get(v___x_2363_, 0);
v_messages_2366_ = lean_ctor_get(v___x_2363_, 1);
v_scopes_2367_ = lean_ctor_get(v___x_2363_, 2);
v_usedQuotCtxts_2368_ = lean_ctor_get(v___x_2363_, 3);
v_nextMacroScope_2369_ = lean_ctor_get(v___x_2363_, 4);
v_maxRecDepth_2370_ = lean_ctor_get(v___x_2363_, 5);
v_ngen_2371_ = lean_ctor_get(v___x_2363_, 6);
v_auxDeclNGen_2372_ = lean_ctor_get(v___x_2363_, 7);
v_traceState_2373_ = lean_ctor_get(v___x_2363_, 9);
v_snapshotTasks_2374_ = lean_ctor_get(v___x_2363_, 10);
v_prevLinterStates_2375_ = lean_ctor_get(v___x_2363_, 11);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2377_ = v___x_2363_;
v_isShared_2378_ = v_isSharedCheck_2397_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_prevLinterStates_2375_);
lean_inc(v_snapshotTasks_2374_);
lean_inc(v_traceState_2373_);
lean_inc(v_infoState_2364_);
lean_inc(v_auxDeclNGen_2372_);
lean_inc(v_ngen_2371_);
lean_inc(v_maxRecDepth_2370_);
lean_inc(v_nextMacroScope_2369_);
lean_inc(v_usedQuotCtxts_2368_);
lean_inc(v_scopes_2367_);
lean_inc(v_messages_2366_);
lean_inc(v_env_2365_);
lean_dec(v___x_2363_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2397_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
uint8_t v_enabled_2379_; lean_object* v_assignment_2380_; lean_object* v_lazyAssignment_2381_; lean_object* v_trees_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2396_; 
v_enabled_2379_ = lean_ctor_get_uint8(v_infoState_2364_, sizeof(void*)*3);
v_assignment_2380_ = lean_ctor_get(v_infoState_2364_, 0);
v_lazyAssignment_2381_ = lean_ctor_get(v_infoState_2364_, 1);
v_trees_2382_ = lean_ctor_get(v_infoState_2364_, 2);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_infoState_2364_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2384_ = v_infoState_2364_;
v_isShared_2385_ = v_isSharedCheck_2396_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_trees_2382_);
lean_inc(v_lazyAssignment_2381_);
lean_inc(v_assignment_2380_);
lean_dec(v_infoState_2364_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2396_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = l_Lean_PersistentArray_push___redArg(v_trees_2382_, v_t_2355_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 2, v___x_2386_);
v___x_2388_ = v___x_2384_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_assignment_2380_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_lazyAssignment_2381_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v___x_2386_);
lean_ctor_set_uint8(v_reuseFailAlloc_2395_, sizeof(void*)*3, v_enabled_2379_);
v___x_2388_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 8, v___x_2388_);
v___x_2390_ = v___x_2377_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_env_2365_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_messages_2366_);
lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_scopes_2367_);
lean_ctor_set(v_reuseFailAlloc_2394_, 3, v_usedQuotCtxts_2368_);
lean_ctor_set(v_reuseFailAlloc_2394_, 4, v_nextMacroScope_2369_);
lean_ctor_set(v_reuseFailAlloc_2394_, 5, v_maxRecDepth_2370_);
lean_ctor_set(v_reuseFailAlloc_2394_, 6, v_ngen_2371_);
lean_ctor_set(v_reuseFailAlloc_2394_, 7, v_auxDeclNGen_2372_);
lean_ctor_set(v_reuseFailAlloc_2394_, 8, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2394_, 9, v_traceState_2373_);
lean_ctor_set(v_reuseFailAlloc_2394_, 10, v_snapshotTasks_2374_);
lean_ctor_set(v_reuseFailAlloc_2394_, 11, v_prevLinterStates_2375_);
v___x_2390_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_st_ref_put(v___y_2356_, v___x_2390_);
v___x_2392_ = lean_box(0);
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
return v___x_2393_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2398_, v___y_2399_);
lean_dec(v___y_2399_);
return v_res_2401_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = lean_unsigned_to_nat(32u);
v___x_2403_ = lean_mk_empty_array_with_capacity(v___x_2402_);
v___x_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
return v___x_2404_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2405_ = ((size_t)5ULL);
v___x_2406_ = lean_unsigned_to_nat(0u);
v___x_2407_ = lean_unsigned_to_nat(32u);
v___x_2408_ = lean_mk_empty_array_with_capacity(v___x_2407_);
v___x_2409_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2410_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
lean_ctor_set(v___x_2410_, 1, v___x_2408_);
lean_ctor_set(v___x_2410_, 2, v___x_2406_);
lean_ctor_set(v___x_2410_, 3, v___x_2406_);
lean_ctor_set_usize(v___x_2410_, 4, v___x_2405_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v_infoState_2416_; uint8_t v_enabled_2417_; 
v___x_2415_ = lean_st_ref_get(v___y_2413_);
v_infoState_2416_ = lean_ctor_get(v___x_2415_, 8);
lean_inc_ref(v_infoState_2416_);
lean_dec(v___x_2415_);
v_enabled_2417_ = lean_ctor_get_uint8(v_infoState_2416_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2416_);
if (v_enabled_2417_ == 0)
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec_ref(v_t_2411_);
v___x_2418_ = lean_box(0);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
else
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_t_2411_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2421_, v___y_2413_);
return v___x_2422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2428_, lean_object* v___x_2429_, lean_object* v___x_2430_, lean_object* v_a_2431_, lean_object* v_b_2432_){
_start:
{
lean_object* v_it_2434_; lean_object* v_startInclusive_2435_; lean_object* v_endExclusive_2436_; 
if (lean_obj_tag(v_a_2431_) == 0)
{
lean_object* v_currPos_2441_; lean_object* v_searcher_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2471_; 
v_currPos_2441_ = lean_ctor_get(v_a_2431_, 0);
v_searcher_2442_ = lean_ctor_get(v_a_2431_, 1);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_a_2431_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2444_ = v_a_2431_;
v_isShared_2445_ = v_isSharedCheck_2471_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_searcher_2442_);
lean_inc(v_currPos_2441_);
lean_dec(v_a_2431_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2471_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v_str_2446_; lean_object* v_startInclusive_2447_; lean_object* v_endExclusive_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v_str_2446_ = lean_ctor_get(v___x_2429_, 0);
v_startInclusive_2447_ = lean_ctor_get(v___x_2429_, 1);
v_endExclusive_2448_ = lean_ctor_get(v___x_2429_, 2);
v___x_2449_ = lean_nat_sub(v_endExclusive_2448_, v_startInclusive_2447_);
v___x_2450_ = lean_nat_dec_eq(v_searcher_2442_, v___x_2449_);
lean_dec(v___x_2449_);
if (v___x_2450_ == 0)
{
uint32_t v___x_2451_; lean_object* v___x_2452_; uint32_t v___x_2453_; uint8_t v___x_2454_; 
v___x_2451_ = 10;
v___x_2452_ = lean_nat_add(v_startInclusive_2447_, v_searcher_2442_);
v___x_2453_ = lean_string_utf8_get_fast(v_str_2446_, v___x_2452_);
v___x_2454_ = lean_uint32_dec_eq(v___x_2453_, v___x_2451_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2458_; 
lean_dec(v_searcher_2442_);
v___x_2455_ = lean_string_utf8_next_fast(v_str_2446_, v___x_2452_);
lean_dec(v___x_2452_);
v___x_2456_ = lean_nat_sub(v___x_2455_, v_startInclusive_2447_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 1, v___x_2456_);
v___x_2458_ = v___x_2444_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_currPos_2441_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
v_a_2431_ = v___x_2458_;
goto _start;
}
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v_slice_2464_; lean_object* v_nextIt_2466_; 
v___x_2461_ = lean_string_utf8_next_fast(v_str_2446_, v___x_2452_);
v___x_2462_ = lean_nat_sub(v___x_2461_, v___x_2452_);
lean_dec(v___x_2452_);
v___x_2463_ = lean_nat_add(v_searcher_2442_, v___x_2462_);
lean_dec(v___x_2462_);
v_slice_2464_ = l_String_Slice_subslice_x21(v___x_2429_, v_currPos_2441_, v_searcher_2442_);
lean_inc(v___x_2463_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 1, v___x_2463_);
lean_ctor_set(v___x_2444_, 0, v___x_2463_);
v_nextIt_2466_ = v___x_2444_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2463_);
v_nextIt_2466_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v_startInclusive_2467_; lean_object* v_endExclusive_2468_; 
v_startInclusive_2467_ = lean_ctor_get(v_slice_2464_, 0);
lean_inc(v_startInclusive_2467_);
v_endExclusive_2468_ = lean_ctor_get(v_slice_2464_, 1);
lean_inc(v_endExclusive_2468_);
lean_dec_ref(v_slice_2464_);
v_it_2434_ = v_nextIt_2466_;
v_startInclusive_2435_ = v_startInclusive_2467_;
v_endExclusive_2436_ = v_endExclusive_2468_;
goto v___jp_2433_;
}
}
}
else
{
lean_object* v___x_2470_; 
lean_del_object(v___x_2444_);
lean_dec(v_searcher_2442_);
v___x_2470_ = lean_box(1);
lean_inc(v___x_2430_);
v_it_2434_ = v___x_2470_;
v_startInclusive_2435_ = v_currPos_2441_;
v_endExclusive_2436_ = v___x_2430_;
goto v___jp_2433_;
}
}
}
else
{
lean_dec(v___x_2430_);
lean_dec_ref(v___x_2428_);
return v_b_2432_;
}
v___jp_2433_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
lean_inc_ref(v___x_2428_);
v___x_2437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2428_);
lean_ctor_set(v___x_2437_, 1, v_startInclusive_2435_);
lean_ctor_set(v___x_2437_, 2, v_endExclusive_2436_);
v___x_2438_ = l_String_Slice_toString(v___x_2437_);
lean_dec_ref_known(v___x_2437_, 3);
v___x_2439_ = lean_array_push(v_b_2432_, v___x_2438_);
v_a_2431_ = v_it_2434_;
v_b_2432_ = v___x_2439_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2472_, lean_object* v___x_2473_, lean_object* v___x_2474_, lean_object* v_a_2475_, lean_object* v_b_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2472_, v___x_2473_, v___x_2474_, v_a_2475_, v_b_2476_);
lean_dec_ref(v___x_2473_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2478_, lean_object* v___x_2479_, lean_object* v___x_2480_, lean_object* v_a_2481_, lean_object* v_b_2482_){
_start:
{
lean_object* v_it_2484_; lean_object* v_startInclusive_2485_; lean_object* v_endExclusive_2486_; 
if (lean_obj_tag(v_a_2481_) == 0)
{
lean_object* v_currPos_2491_; lean_object* v_searcher_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2521_; 
v_currPos_2491_ = lean_ctor_get(v_a_2481_, 0);
v_searcher_2492_ = lean_ctor_get(v_a_2481_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_a_2481_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2494_ = v_a_2481_;
v_isShared_2495_ = v_isSharedCheck_2521_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_searcher_2492_);
lean_inc(v_currPos_2491_);
lean_dec(v_a_2481_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2521_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_str_2496_; lean_object* v_startInclusive_2497_; lean_object* v_endExclusive_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v_str_2496_ = lean_ctor_get(v___x_2479_, 0);
v_startInclusive_2497_ = lean_ctor_get(v___x_2479_, 1);
v_endExclusive_2498_ = lean_ctor_get(v___x_2479_, 2);
v___x_2499_ = lean_nat_sub(v_endExclusive_2498_, v_startInclusive_2497_);
v___x_2500_ = lean_nat_dec_eq(v_searcher_2492_, v___x_2499_);
lean_dec(v___x_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; uint32_t v___x_2502_; uint32_t v___x_2503_; uint8_t v___x_2504_; 
v___x_2501_ = lean_nat_add(v_startInclusive_2497_, v_searcher_2492_);
v___x_2502_ = lean_string_utf8_get_fast(v_str_2496_, v___x_2501_);
v___x_2503_ = 10;
v___x_2504_ = lean_uint32_dec_eq(v___x_2502_, v___x_2503_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
lean_dec(v_searcher_2492_);
v___x_2505_ = lean_string_utf8_next_fast(v_str_2496_, v___x_2501_);
lean_dec(v___x_2501_);
v___x_2506_ = lean_nat_sub(v___x_2505_, v_startInclusive_2497_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 1, v___x_2506_);
v___x_2508_ = v___x_2494_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_currPos_2491_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; 
v___x_2509_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2478_, v___x_2479_, v___x_2480_, v___x_2508_, v_b_2482_);
return v___x_2509_;
}
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v_slice_2514_; lean_object* v_nextIt_2516_; 
v___x_2511_ = lean_string_utf8_next_fast(v_str_2496_, v___x_2501_);
v___x_2512_ = lean_nat_sub(v___x_2511_, v___x_2501_);
lean_dec(v___x_2501_);
v___x_2513_ = lean_nat_add(v_searcher_2492_, v___x_2512_);
lean_dec(v___x_2512_);
v_slice_2514_ = l_String_Slice_subslice_x21(v___x_2479_, v_currPos_2491_, v_searcher_2492_);
lean_inc(v___x_2513_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 1, v___x_2513_);
lean_ctor_set(v___x_2494_, 0, v___x_2513_);
v_nextIt_2516_ = v___x_2494_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v___x_2513_);
v_nextIt_2516_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v_startInclusive_2517_; lean_object* v_endExclusive_2518_; 
v_startInclusive_2517_ = lean_ctor_get(v_slice_2514_, 0);
lean_inc(v_startInclusive_2517_);
v_endExclusive_2518_ = lean_ctor_get(v_slice_2514_, 1);
lean_inc(v_endExclusive_2518_);
lean_dec_ref(v_slice_2514_);
v_it_2484_ = v_nextIt_2516_;
v_startInclusive_2485_ = v_startInclusive_2517_;
v_endExclusive_2486_ = v_endExclusive_2518_;
goto v___jp_2483_;
}
}
}
else
{
lean_object* v___x_2520_; 
lean_del_object(v___x_2494_);
lean_dec(v_searcher_2492_);
v___x_2520_ = lean_box(1);
lean_inc(v___x_2480_);
v_it_2484_ = v___x_2520_;
v_startInclusive_2485_ = v_currPos_2491_;
v_endExclusive_2486_ = v___x_2480_;
goto v___jp_2483_;
}
}
}
else
{
lean_dec(v___x_2480_);
lean_dec_ref(v___x_2478_);
return v_b_2482_;
}
v___jp_2483_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
lean_inc_ref(v___x_2478_);
v___x_2487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2478_);
lean_ctor_set(v___x_2487_, 1, v_startInclusive_2485_);
lean_ctor_set(v___x_2487_, 2, v_endExclusive_2486_);
v___x_2488_ = l_String_Slice_toString(v___x_2487_);
lean_dec_ref_known(v___x_2487_, 3);
v___x_2489_ = lean_array_push(v_b_2482_, v___x_2488_);
v___x_2490_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2478_, v___x_2479_, v___x_2480_, v_it_2484_, v___x_2489_);
return v___x_2490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2522_, lean_object* v___x_2523_, lean_object* v___x_2524_, lean_object* v_a_2525_, lean_object* v_b_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2522_, v___x_2523_, v___x_2524_, v_a_2525_, v_b_2526_);
lean_dec_ref(v___x_2523_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(lean_object* v_b_2528_, lean_object* v_acc_2529_, lean_object* v_i_2530_){
_start:
{
lean_object* v_keyArray_2535_; lean_object* v_valueArray_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v_keyArray_2535_ = lean_ctor_get(v_b_2528_, 1);
v_valueArray_2536_ = lean_ctor_get(v_b_2528_, 2);
v___x_2537_ = lean_array_get_size(v_keyArray_2535_);
v___x_2538_ = lean_nat_dec_lt(v_i_2530_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_dec(v_i_2530_);
lean_inc(v_acc_2529_);
return v_acc_2529_;
}
else
{
lean_object* v___x_2539_; uint8_t v_isSome_2540_; 
v___x_2539_ = lean_array_fget_borrowed(v_keyArray_2535_, v_i_2530_);
v_isSome_2540_ = lean_noption_is_some(v___x_2539_);
if (v_isSome_2540_ == 0)
{
goto v___jp_2531_;
}
else
{
lean_object* v___x_2541_; uint8_t v_isSome_2542_; 
v___x_2541_ = lean_array_fget_borrowed(v_valueArray_2536_, v_i_2530_);
v_isSome_2542_ = lean_noption_is_some(v___x_2541_);
if (v_isSome_2542_ == 0)
{
goto v___jp_2531_;
}
else
{
lean_object* v_val_2543_; lean_object* v_val_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
lean_inc(v___x_2539_);
v_val_2543_ = lean_noption_get(v___x_2539_);
lean_inc(v___x_2541_);
v_val_2544_ = lean_noption_get(v___x_2541_);
v___x_2545_ = lean_unsigned_to_nat(1u);
v___x_2546_ = lean_nat_add(v_i_2530_, v___x_2545_);
lean_dec(v_i_2530_);
v___x_2547_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(v_b_2528_, v_acc_2529_, v___x_2546_);
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v_val_2543_);
lean_ctor_set(v___x_2548_, 1, v_val_2544_);
v___x_2549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
lean_ctor_set(v___x_2549_, 1, v___x_2547_);
return v___x_2549_;
}
}
}
v___jp_2531_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2533_ = lean_nat_add(v_i_2530_, v___x_2532_);
lean_dec(v_i_2530_);
v_i_2530_ = v___x_2533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___boxed(lean_object* v_b_2550_, lean_object* v_acc_2551_, lean_object* v_i_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(v_b_2550_, v_acc_2551_, v_i_2552_);
lean_dec(v_acc_2551_);
lean_dec_ref(v_b_2550_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(lean_object* v_left_2554_, lean_object* v_right_2555_, lean_object* v_pref_2556_){
_start:
{
lean_object* v_start_2557_; lean_object* v_stop_2558_; lean_object* v_i_2559_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v_start_2557_ = lean_ctor_get(v_left_2554_, 1);
v_stop_2558_ = lean_ctor_get(v_left_2554_, 2);
v_i_2559_ = lean_array_get_size(v_pref_2556_);
v___x_2565_ = lean_nat_sub(v_stop_2558_, v_start_2557_);
v___x_2566_ = lean_nat_dec_lt(v_i_2559_, v___x_2565_);
lean_dec(v___x_2565_);
if (v___x_2566_ == 0)
{
goto v___jp_2560_;
}
else
{
lean_object* v_start_2567_; lean_object* v_stop_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v_start_2567_ = lean_ctor_get(v_right_2555_, 1);
v_stop_2568_ = lean_ctor_get(v_right_2555_, 2);
v___x_2569_ = lean_nat_sub(v_stop_2568_, v_start_2567_);
v___x_2570_ = lean_nat_dec_lt(v_i_2559_, v___x_2569_);
lean_dec(v___x_2569_);
if (v___x_2570_ == 0)
{
goto v___jp_2560_;
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2571_ = l_Subarray_get___redArg(v_left_2554_, v_i_2559_);
v___x_2572_ = l_Subarray_get___redArg(v_right_2555_, v_i_2559_);
v___x_2573_ = lean_string_dec_eq(v___x_2571_, v___x_2572_);
lean_dec(v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec(v___x_2571_);
v___x_2574_ = l_Subarray_drop___redArg(v_left_2554_, v_i_2559_);
v___x_2575_ = l_Subarray_drop___redArg(v_right_2555_, v_i_2559_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v_pref_2556_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
return v___x_2577_;
}
else
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_array_push(v_pref_2556_, v___x_2571_);
v_pref_2556_ = v___x_2578_;
goto _start;
}
}
}
v___jp_2560_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2561_ = l_Subarray_drop___redArg(v_left_2554_, v_i_2559_);
v___x_2562_ = l_Subarray_drop___redArg(v_right_2555_, v_i_2559_);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v_pref_2556_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
return v___x_2564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(lean_object* v_left_2582_, lean_object* v_right_2583_){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_2585_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(v_left_2582_, v_right_2583_, v___x_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36___redArg(lean_object* v_m_2586_, lean_object* v_query_2587_, lean_object* v_x_2588_, lean_object* v_x_2589_, lean_object* v_x_2590_){
_start:
{
lean_object* v_zero_2591_; uint8_t v_isZero_2592_; 
v_zero_2591_ = lean_unsigned_to_nat(0u);
v_isZero_2592_ = lean_nat_dec_eq(v_x_2589_, v_zero_2591_);
if (v_isZero_2592_ == 1)
{
lean_dec(v_x_2590_);
lean_dec(v_x_2589_);
if (lean_obj_tag(v_x_2588_) == 0)
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_box(2);
return v___x_2593_;
}
else
{
lean_object* v_val_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
v_val_2594_ = lean_ctor_get(v_x_2588_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_x_2588_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v_x_2588_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_val_2594_);
lean_dec(v_x_2588_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_val_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v_keyArray_2602_; lean_object* v_valueArray_2603_; lean_object* v___x_2604_; uint8_t v_isSome_2605_; 
v_keyArray_2602_ = lean_ctor_get(v_m_2586_, 1);
v_valueArray_2603_ = lean_ctor_get(v_m_2586_, 2);
v___x_2604_ = lean_array_fget_borrowed(v_keyArray_2602_, v_x_2590_);
v_isSome_2605_ = lean_noption_is_some(v___x_2604_);
if (v_isSome_2605_ == 0)
{
lean_dec(v_x_2589_);
if (lean_obj_tag(v_x_2588_) == 0)
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2606_, 0, v_x_2590_);
return v___x_2606_;
}
else
{
lean_object* v_val_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_x_2590_);
v_val_2607_ = lean_ctor_get(v_x_2588_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_x_2588_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v_x_2588_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_val_2607_);
lean_dec(v_x_2588_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_val_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_object* v_one_2615_; lean_object* v_n_2616_; lean_object* v___y_2618_; 
v_one_2615_ = lean_unsigned_to_nat(1u);
v_n_2616_ = lean_nat_sub(v_x_2589_, v_one_2615_);
lean_dec(v_x_2589_);
if (v_isSome_2605_ == 0)
{
goto v___jp_2624_;
}
else
{
lean_object* v___x_2626_; uint8_t v_isSome_2627_; 
v___x_2626_ = lean_array_fget_borrowed(v_valueArray_2603_, v_x_2590_);
v_isSome_2627_ = lean_noption_is_some(v___x_2626_);
if (v_isSome_2627_ == 0)
{
goto v___jp_2624_;
}
else
{
lean_object* v_val_2628_; uint8_t v___x_2629_; 
lean_inc(v___x_2604_);
v_val_2628_ = lean_noption_get(v___x_2604_);
v___x_2629_ = lean_string_dec_eq(v_val_2628_, v_query_2587_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
lean_dec(v_val_2628_);
v___x_2630_ = lean_array_get_size(v_keyArray_2602_);
v___x_2631_ = lean_nat_add(v_x_2590_, v_one_2615_);
lean_dec(v_x_2590_);
v___x_2632_ = lean_nat_dec_lt(v___x_2631_, v___x_2630_);
if (v___x_2632_ == 0)
{
lean_dec(v___x_2631_);
v_x_2589_ = v_n_2616_;
v_x_2590_ = v_zero_2591_;
goto _start;
}
else
{
v_x_2589_ = v_n_2616_;
v_x_2590_ = v___x_2631_;
goto _start;
}
}
else
{
lean_object* v_val_2635_; lean_object* v___x_2636_; 
lean_dec(v_n_2616_);
lean_dec(v_x_2588_);
lean_inc(v___x_2626_);
v_val_2635_ = lean_noption_get(v___x_2626_);
v___x_2636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2636_, 0, v_x_2590_);
lean_ctor_set(v___x_2636_, 1, v_val_2628_);
lean_ctor_set(v___x_2636_, 2, v_val_2635_);
return v___x_2636_;
}
}
}
v___jp_2617_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2619_ = lean_array_get_size(v_keyArray_2602_);
v___x_2620_ = lean_nat_add(v_x_2590_, v_one_2615_);
lean_dec(v_x_2590_);
v___x_2621_ = lean_nat_dec_lt(v___x_2620_, v___x_2619_);
if (v___x_2621_ == 0)
{
lean_dec(v___x_2620_);
v_x_2588_ = v___y_2618_;
v_x_2589_ = v_n_2616_;
v_x_2590_ = v_zero_2591_;
goto _start;
}
else
{
v_x_2588_ = v___y_2618_;
v_x_2589_ = v_n_2616_;
v_x_2590_ = v___x_2620_;
goto _start;
}
}
v___jp_2624_:
{
if (lean_obj_tag(v_x_2588_) == 0)
{
lean_object* v___x_2625_; 
lean_inc(v_x_2590_);
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_x_2590_);
v___y_2618_ = v___x_2625_;
goto v___jp_2617_;
}
else
{
v___y_2618_ = v_x_2588_;
goto v___jp_2617_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36___redArg___boxed(lean_object* v_m_2637_, lean_object* v_query_2638_, lean_object* v_x_2639_, lean_object* v_x_2640_, lean_object* v_x_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36___redArg(v_m_2637_, v_query_2638_, v_x_2639_, v_x_2640_, v_x_2641_);
lean_dec_ref(v_query_2638_);
lean_dec_ref(v_m_2637_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(lean_object* v_m_2643_, lean_object* v_query_2644_){
_start:
{
lean_object* v_keyArray_2645_; lean_object* v___x_2646_; uint64_t v___x_2647_; uint64_t v___x_2648_; uint64_t v___x_2649_; uint64_t v_fold_2650_; uint64_t v___x_2651_; uint64_t v___x_2652_; uint64_t v___x_2653_; size_t v___x_2654_; size_t v___x_2655_; size_t v___x_2656_; size_t v___x_2657_; size_t v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v_keyArray_2645_ = lean_ctor_get(v_m_2643_, 1);
v___x_2646_ = lean_array_get_size(v_keyArray_2645_);
v___x_2647_ = lean_string_hash(v_query_2644_);
v___x_2648_ = 32ULL;
v___x_2649_ = lean_uint64_shift_right(v___x_2647_, v___x_2648_);
v_fold_2650_ = lean_uint64_xor(v___x_2647_, v___x_2649_);
v___x_2651_ = 16ULL;
v___x_2652_ = lean_uint64_shift_right(v_fold_2650_, v___x_2651_);
v___x_2653_ = lean_uint64_xor(v_fold_2650_, v___x_2652_);
v___x_2654_ = lean_uint64_to_usize(v___x_2653_);
v___x_2655_ = lean_usize_of_nat(v___x_2646_);
v___x_2656_ = ((size_t)1ULL);
v___x_2657_ = lean_usize_sub(v___x_2655_, v___x_2656_);
v___x_2658_ = lean_usize_land(v___x_2654_, v___x_2657_);
v___x_2659_ = lean_usize_to_nat(v___x_2658_);
v___x_2660_ = lean_box(0);
v___x_2661_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36___redArg(v_m_2643_, v_query_2644_, v___x_2660_, v___x_2646_, v___x_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg___boxed(lean_object* v_m_2662_, lean_object* v_query_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v_m_2662_, v_query_2663_);
lean_dec_ref(v_query_2663_);
lean_dec_ref(v_m_2662_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34___redArg(lean_object* v_m_2665_, lean_object* v_query_2666_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v_m_2665_, v_query_2666_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_index_2668_; lean_object* v_key_2669_; lean_object* v_value_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v_index_2668_ = lean_ctor_get(v___x_2667_, 0);
v_key_2669_ = lean_ctor_get(v___x_2667_, 1);
v_value_2670_ = lean_ctor_get(v___x_2667_, 2);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2667_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_value_2670_);
lean_inc(v_key_2669_);
lean_inc(v_index_2668_);
lean_dec(v___x_2667_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_index_2668_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_key_2669_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v_value_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v___x_2678_; 
lean_dec(v___x_2667_);
v___x_2678_ = lean_box(1);
return v___x_2678_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34___redArg___boxed(lean_object* v_m_2679_, lean_object* v_query_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34___redArg(v_m_2679_, v_query_2680_);
lean_dec_ref(v_query_2680_);
lean_dec_ref(v_m_2679_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22___redArg(lean_object* v_m_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34___redArg(v_m_2682_, v_a_2683_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_value_2685_; lean_object* v___x_2686_; 
v_value_2685_ = lean_ctor_get(v___x_2684_, 2);
lean_inc(v_value_2685_);
lean_dec_ref_known(v___x_2684_, 3);
v___x_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2686_, 0, v_value_2685_);
return v___x_2686_;
}
else
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_box(0);
return v___x_2687_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22___redArg___boxed(lean_object* v_m_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22___redArg(v_m_2688_, v_a_2689_);
lean_dec_ref(v_a_2689_);
lean_dec_ref(v_m_2688_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44___redArg(lean_object* v_b_2691_, lean_object* v_acc_2692_, lean_object* v_i_2693_){
_start:
{
lean_object* v___y_2695_; lean_object* v_keyArray_2703_; lean_object* v_valueArray_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v_keyArray_2703_ = lean_ctor_get(v_b_2691_, 1);
v_valueArray_2704_ = lean_ctor_get(v_b_2691_, 2);
v___x_2705_ = lean_array_get_size(v_keyArray_2703_);
v___x_2706_ = lean_nat_dec_lt(v_i_2693_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_dec(v_i_2693_);
return v_acc_2692_;
}
else
{
lean_object* v___x_2707_; uint8_t v_isSome_2708_; 
v___x_2707_ = lean_array_fget_borrowed(v_keyArray_2703_, v_i_2693_);
v_isSome_2708_ = lean_noption_is_some(v___x_2707_);
if (v_isSome_2708_ == 0)
{
goto v___jp_2699_;
}
else
{
lean_object* v___x_2709_; uint8_t v_isSome_2710_; 
v___x_2709_ = lean_array_fget_borrowed(v_valueArray_2704_, v_i_2693_);
v_isSome_2710_ = lean_noption_is_some(v___x_2709_);
if (v_isSome_2710_ == 0)
{
goto v___jp_2699_;
}
else
{
lean_object* v_val_2711_; lean_object* v_val_2712_; lean_object* v_i_2714_; lean_object* v___x_2719_; 
lean_inc(v___x_2707_);
v_val_2711_ = lean_noption_get(v___x_2707_);
lean_inc(v___x_2709_);
v_val_2712_ = lean_noption_get(v___x_2709_);
v___x_2719_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v_acc_2692_, v_val_2711_);
switch(lean_obj_tag(v___x_2719_))
{
case 0:
{
lean_object* v_index_2720_; lean_object* v_size_2721_; lean_object* v___x_2722_; 
v_index_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_index_2720_);
lean_dec_ref_known(v___x_2719_, 3);
v_size_2721_ = lean_ctor_get(v_acc_2692_, 0);
lean_inc(v_size_2721_);
v___x_2722_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2692_, v_size_2721_, v_index_2720_, v_val_2711_, v_val_2712_);
lean_dec(v_index_2720_);
v___y_2695_ = v___x_2722_;
goto v___jp_2694_;
}
case 1:
{
lean_object* v_index_2723_; 
v_index_2723_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_index_2723_);
lean_dec_ref_known(v___x_2719_, 1);
v_i_2714_ = v_index_2723_;
goto v___jp_2713_;
}
default: 
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2692_, v___x_2724_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_index_2726_; 
v_index_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_index_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v_i_2714_ = v_index_2726_;
goto v___jp_2713_;
}
else
{
lean_dec(v_val_2712_);
lean_dec(v_val_2711_);
v___y_2695_ = v_acc_2692_;
goto v___jp_2694_;
}
}
}
v___jp_2713_:
{
lean_object* v_size_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_size_2715_ = lean_ctor_get(v_acc_2692_, 0);
v___x_2716_ = lean_unsigned_to_nat(1u);
v___x_2717_ = lean_nat_add(v_size_2715_, v___x_2716_);
v___x_2718_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2692_, v___x_2717_, v_i_2714_, v_val_2711_, v_val_2712_);
lean_dec(v_i_2714_);
v___y_2695_ = v___x_2718_;
goto v___jp_2694_;
}
}
}
}
v___jp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_add(v_i_2693_, v___x_2696_);
lean_dec(v_i_2693_);
v_acc_2692_ = v___y_2695_;
v_i_2693_ = v___x_2697_;
goto _start;
}
v___jp_2699_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_unsigned_to_nat(1u);
v___x_2701_ = lean_nat_add(v_i_2693_, v___x_2700_);
lean_dec(v_i_2693_);
v_i_2693_ = v___x_2701_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44___redArg___boxed(lean_object* v_b_2727_, lean_object* v_acc_2728_, lean_object* v_i_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44___redArg(v_b_2727_, v_acc_2728_, v_i_2729_);
lean_dec_ref(v_b_2727_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38___redArg(lean_object* v_init_2731_, lean_object* v_b_2732_){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_unsigned_to_nat(0u);
v___x_2734_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44___redArg(v_b_2732_, v_init_2731_, v___x_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38___redArg___boxed(lean_object* v_init_2735_, lean_object* v_b_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38___redArg(v_init_2735_, v_b_2736_);
lean_dec_ref(v_b_2736_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(lean_object* v_m_2738_){
_start:
{
lean_object* v_keyArray_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v_cellCount_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v_target_2746_; lean_object* v___x_2747_; 
v_keyArray_2739_ = lean_ctor_get(v_m_2738_, 1);
v___x_2740_ = lean_array_get_size(v_keyArray_2739_);
v___x_2741_ = lean_unsigned_to_nat(2u);
v_cellCount_2742_ = lean_nat_mul(v___x_2740_, v___x_2741_);
v___x_2743_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2742_);
v___x_2744_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2742_);
v___x_2745_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2742_);
v_target_2746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2746_, 0, v___x_2743_);
lean_ctor_set(v_target_2746_, 1, v___x_2744_);
lean_ctor_set(v_target_2746_, 2, v___x_2745_);
v___x_2747_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38___redArg(v_target_2746_, v_m_2738_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg___boxed(lean_object* v_m_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_m_2748_);
lean_dec_ref(v_m_2748_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(lean_object* v_histogram_2750_, lean_object* v_index_2751_, lean_object* v_val_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22___redArg(v_histogram_2750_, v_val_2752_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___y_2760_; lean_object* v_i_2761_; lean_object* v___y_2766_; lean_object* v___y_2775_; lean_object* v_i_2776_; lean_object* v___x_2789_; 
v___x_2754_ = lean_unsigned_to_nat(1u);
v___x_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_index_2751_);
v___x_2756_ = lean_unsigned_to_nat(0u);
v___x_2757_ = lean_box(0);
v___x_2758_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2754_);
lean_ctor_set(v___x_2758_, 1, v___x_2755_);
lean_ctor_set(v___x_2758_, 2, v___x_2756_);
lean_ctor_set(v___x_2758_, 3, v___x_2757_);
v___x_2789_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v_histogram_2750_, v_val_2752_);
switch(lean_obj_tag(v___x_2789_))
{
case 0:
{
lean_object* v_index_2790_; lean_object* v_size_2791_; lean_object* v___x_2792_; 
v_index_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_index_2790_);
lean_dec_ref_known(v___x_2789_, 3);
v_size_2791_ = lean_ctor_get(v_histogram_2750_, 0);
lean_inc(v_size_2791_);
v___x_2792_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2750_, v_size_2791_, v_index_2790_, v_val_2752_, v___x_2758_);
lean_dec(v_index_2790_);
return v___x_2792_;
}
case 1:
{
lean_object* v_index_2793_; lean_object* v_size_2794_; lean_object* v_keyArray_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v_index_2793_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_index_2793_);
lean_dec_ref_known(v___x_2789_, 1);
v_size_2794_ = lean_ctor_get(v_histogram_2750_, 0);
v_keyArray_2795_ = lean_ctor_get(v_histogram_2750_, 1);
v___x_2796_ = lean_nat_add(v_size_2794_, v___x_2754_);
v___x_2797_ = lean_array_get_size(v_keyArray_2795_);
v___x_2798_ = lean_nat_dec_lt(v___x_2796_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_dec(v___x_2796_);
lean_dec(v_index_2793_);
goto v___jp_2780_;
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2799_ = lean_unsigned_to_nat(4u);
v___x_2800_ = lean_nat_mul(v___x_2796_, v___x_2799_);
v___x_2801_ = lean_unsigned_to_nat(3u);
v___x_2802_ = lean_nat_mul(v___x_2797_, v___x_2801_);
v___x_2803_ = lean_nat_dec_le(v___x_2800_, v___x_2802_);
lean_dec(v___x_2802_);
lean_dec(v___x_2800_);
if (v___x_2803_ == 0)
{
lean_dec(v___x_2796_);
lean_dec(v_index_2793_);
goto v___jp_2780_;
}
else
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2750_, v___x_2796_, v_index_2793_, v_val_2752_, v___x_2758_);
lean_dec(v_index_2793_);
return v___x_2804_;
}
}
}
default: 
{
lean_object* v_size_2805_; lean_object* v_keyArray_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v_size_2805_ = lean_ctor_get(v_histogram_2750_, 0);
v_keyArray_2806_ = lean_ctor_get(v_histogram_2750_, 1);
v___x_2807_ = lean_nat_add(v_size_2805_, v___x_2754_);
v___x_2808_ = lean_array_get_size(v_keyArray_2806_);
v___x_2809_ = lean_nat_dec_lt(v___x_2807_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_dec(v___x_2807_);
v___x_2810_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2750_);
lean_dec_ref(v_histogram_2750_);
v___y_2766_ = v___x_2810_;
goto v___jp_2765_;
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; 
v___x_2811_ = lean_unsigned_to_nat(4u);
v___x_2812_ = lean_nat_mul(v___x_2807_, v___x_2811_);
lean_dec(v___x_2807_);
v___x_2813_ = lean_unsigned_to_nat(3u);
v___x_2814_ = lean_nat_mul(v___x_2808_, v___x_2813_);
v___x_2815_ = lean_nat_dec_le(v___x_2812_, v___x_2814_);
lean_dec(v___x_2814_);
lean_dec(v___x_2812_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2750_);
lean_dec_ref(v_histogram_2750_);
v___y_2766_ = v___x_2816_;
goto v___jp_2765_;
}
else
{
v___y_2766_ = v_histogram_2750_;
goto v___jp_2765_;
}
}
}
}
v___jp_2759_:
{
lean_object* v_size_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v_size_2762_ = lean_ctor_get(v___y_2760_, 0);
v___x_2763_ = lean_nat_add(v_size_2762_, v___x_2754_);
v___x_2764_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2760_, v___x_2763_, v_i_2761_, v_val_2752_, v___x_2758_);
lean_dec(v_i_2761_);
return v___x_2764_;
}
v___jp_2765_:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v___y_2766_, v_val_2752_);
switch(lean_obj_tag(v___x_2767_))
{
case 0:
{
lean_object* v_index_2768_; lean_object* v_size_2769_; lean_object* v___x_2770_; 
v_index_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_index_2768_);
lean_dec_ref_known(v___x_2767_, 3);
v_size_2769_ = lean_ctor_get(v___y_2766_, 0);
lean_inc(v_size_2769_);
v___x_2770_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2766_, v_size_2769_, v_index_2768_, v_val_2752_, v___x_2758_);
lean_dec(v_index_2768_);
return v___x_2770_;
}
case 1:
{
lean_object* v_index_2771_; 
v_index_2771_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_index_2771_);
lean_dec_ref_known(v___x_2767_, 1);
v___y_2760_ = v___y_2766_;
v_i_2761_ = v_index_2771_;
goto v___jp_2759_;
}
default: 
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2766_, v___x_2756_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_index_2773_; 
v_index_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_index_2773_);
lean_dec_ref_known(v___x_2772_, 1);
v___y_2760_ = v___y_2766_;
v_i_2761_ = v_index_2773_;
goto v___jp_2759_;
}
else
{
lean_dec_ref_known(v___x_2758_, 4);
lean_dec_ref(v_val_2752_);
return v___y_2766_;
}
}
}
}
v___jp_2774_:
{
lean_object* v_size_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v_size_2777_ = lean_ctor_get(v___y_2775_, 0);
v___x_2778_ = lean_nat_add(v_size_2777_, v___x_2754_);
v___x_2779_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2775_, v___x_2778_, v_i_2776_, v_val_2752_, v___x_2758_);
lean_dec(v_i_2776_);
return v___x_2779_;
}
v___jp_2780_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2750_);
lean_dec_ref(v_histogram_2750_);
v___x_2782_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v___x_2781_, v_val_2752_);
switch(lean_obj_tag(v___x_2782_))
{
case 0:
{
lean_object* v_index_2783_; lean_object* v_size_2784_; lean_object* v___x_2785_; 
v_index_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_index_2783_);
lean_dec_ref_known(v___x_2782_, 3);
v_size_2784_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_size_2784_);
v___x_2785_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2781_, v_size_2784_, v_index_2783_, v_val_2752_, v___x_2758_);
lean_dec(v_index_2783_);
return v___x_2785_;
}
case 1:
{
lean_object* v_index_2786_; 
v_index_2786_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_index_2786_);
lean_dec_ref_known(v___x_2782_, 1);
v___y_2775_ = v___x_2781_;
v_i_2776_ = v_index_2786_;
goto v___jp_2774_;
}
default: 
{
lean_object* v___x_2787_; 
v___x_2787_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2781_, v___x_2756_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_index_2788_; 
v_index_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_index_2788_);
lean_dec_ref_known(v___x_2787_, 1);
v___y_2775_ = v___x_2781_;
v_i_2776_ = v_index_2788_;
goto v___jp_2774_;
}
else
{
lean_dec_ref_known(v___x_2758_, 4);
lean_dec_ref(v_val_2752_);
return v___x_2781_;
}
}
}
}
}
else
{
lean_object* v_val_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2897_; 
v_val_2817_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2819_ = v___x_2753_;
v_isShared_2820_ = v_isSharedCheck_2897_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_val_2817_);
lean_dec(v___x_2753_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2897_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v_leftCount_2821_; lean_object* v_rightCount_2822_; lean_object* v_rightIndex_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2895_; 
v_leftCount_2821_ = lean_ctor_get(v_val_2817_, 0);
v_rightCount_2822_ = lean_ctor_get(v_val_2817_, 2);
v_rightIndex_2823_ = lean_ctor_get(v_val_2817_, 3);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_val_2817_);
if (v_isSharedCheck_2895_ == 0)
{
lean_object* v_unused_2896_; 
v_unused_2896_ = lean_ctor_get(v_val_2817_, 1);
lean_dec(v_unused_2896_);
v___x_2825_ = v_val_2817_;
v_isShared_2826_ = v_isSharedCheck_2895_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_rightIndex_2823_);
lean_inc(v_rightCount_2822_);
lean_inc(v_leftCount_2821_);
lean_dec(v_val_2817_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2895_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2827_ = lean_unsigned_to_nat(1u);
v___x_2828_ = lean_nat_add(v_leftCount_2821_, v___x_2827_);
lean_dec(v_leftCount_2821_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v_index_2751_);
v___x_2830_ = v___x_2819_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_index_2751_);
v___x_2830_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2832_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 1, v___x_2830_);
lean_ctor_set(v___x_2825_, 0, v___x_2828_);
v___x_2832_ = v___x_2825_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2828_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2893_, 2, v_rightCount_2822_);
lean_ctor_set(v_reuseFailAlloc_2893_, 3, v_rightIndex_2823_);
v___x_2832_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___y_2834_; lean_object* v_i_2835_; lean_object* v___y_2840_; lean_object* v___y_2850_; lean_object* v_i_2851_; lean_object* v___x_2865_; 
v___x_2865_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v_histogram_2750_, v_val_2752_);
switch(lean_obj_tag(v___x_2865_))
{
case 0:
{
lean_object* v_index_2866_; lean_object* v_size_2867_; lean_object* v___x_2868_; 
v_index_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_index_2866_);
lean_dec_ref_known(v___x_2865_, 3);
v_size_2867_ = lean_ctor_get(v_histogram_2750_, 0);
lean_inc(v_size_2867_);
v___x_2868_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2750_, v_size_2867_, v_index_2866_, v_val_2752_, v___x_2832_);
lean_dec(v_index_2866_);
return v___x_2868_;
}
case 1:
{
lean_object* v_index_2869_; lean_object* v_size_2870_; lean_object* v_keyArray_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v_index_2869_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_index_2869_);
lean_dec_ref_known(v___x_2865_, 1);
v_size_2870_ = lean_ctor_get(v_histogram_2750_, 0);
v_keyArray_2871_ = lean_ctor_get(v_histogram_2750_, 1);
v___x_2872_ = lean_nat_add(v_size_2870_, v___x_2827_);
v___x_2873_ = lean_array_get_size(v_keyArray_2871_);
v___x_2874_ = lean_nat_dec_lt(v___x_2872_, v___x_2873_);
if (v___x_2874_ == 0)
{
lean_dec(v___x_2872_);
lean_dec(v_index_2869_);
goto v___jp_2855_;
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2875_ = lean_unsigned_to_nat(4u);
v___x_2876_ = lean_nat_mul(v___x_2872_, v___x_2875_);
v___x_2877_ = lean_unsigned_to_nat(3u);
v___x_2878_ = lean_nat_mul(v___x_2873_, v___x_2877_);
v___x_2879_ = lean_nat_dec_le(v___x_2876_, v___x_2878_);
lean_dec(v___x_2878_);
lean_dec(v___x_2876_);
if (v___x_2879_ == 0)
{
lean_dec(v___x_2872_);
lean_dec(v_index_2869_);
goto v___jp_2855_;
}
else
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2750_, v___x_2872_, v_index_2869_, v_val_2752_, v___x_2832_);
lean_dec(v_index_2869_);
return v___x_2880_;
}
}
}
default: 
{
lean_object* v_size_2881_; lean_object* v_keyArray_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v_size_2881_ = lean_ctor_get(v_histogram_2750_, 0);
v_keyArray_2882_ = lean_ctor_get(v_histogram_2750_, 1);
v___x_2883_ = lean_nat_add(v_size_2881_, v___x_2827_);
v___x_2884_ = lean_array_get_size(v_keyArray_2882_);
v___x_2885_ = lean_nat_dec_lt(v___x_2883_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; 
lean_dec(v___x_2883_);
v___x_2886_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2750_);
lean_dec_ref(v_histogram_2750_);
v___y_2840_ = v___x_2886_;
goto v___jp_2839_;
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2887_ = lean_unsigned_to_nat(4u);
v___x_2888_ = lean_nat_mul(v___x_2883_, v___x_2887_);
lean_dec(v___x_2883_);
v___x_2889_ = lean_unsigned_to_nat(3u);
v___x_2890_ = lean_nat_mul(v___x_2884_, v___x_2889_);
v___x_2891_ = lean_nat_dec_le(v___x_2888_, v___x_2890_);
lean_dec(v___x_2890_);
lean_dec(v___x_2888_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2750_);
lean_dec_ref(v_histogram_2750_);
v___y_2840_ = v___x_2892_;
goto v___jp_2839_;
}
else
{
v___y_2840_ = v_histogram_2750_;
goto v___jp_2839_;
}
}
}
}
v___jp_2833_:
{
lean_object* v_size_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_size_2836_ = lean_ctor_get(v___y_2834_, 0);
v___x_2837_ = lean_nat_add(v_size_2836_, v___x_2827_);
v___x_2838_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2834_, v___x_2837_, v_i_2835_, v_val_2752_, v___x_2832_);
lean_dec(v_i_2835_);
return v___x_2838_;
}
v___jp_2839_:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v___y_2840_, v_val_2752_);
switch(lean_obj_tag(v___x_2841_))
{
case 0:
{
lean_object* v_index_2842_; lean_object* v_size_2843_; lean_object* v___x_2844_; 
v_index_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_index_2842_);
lean_dec_ref_known(v___x_2841_, 3);
v_size_2843_ = lean_ctor_get(v___y_2840_, 0);
lean_inc(v_size_2843_);
v___x_2844_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2840_, v_size_2843_, v_index_2842_, v_val_2752_, v___x_2832_);
lean_dec(v_index_2842_);
return v___x_2844_;
}
case 1:
{
lean_object* v_index_2845_; 
v_index_2845_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_index_2845_);
lean_dec_ref_known(v___x_2841_, 1);
v___y_2834_ = v___y_2840_;
v_i_2835_ = v_index_2845_;
goto v___jp_2833_;
}
default: 
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = lean_unsigned_to_nat(0u);
v___x_2847_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2840_, v___x_2846_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_index_2848_; 
v_index_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_index_2848_);
lean_dec_ref_known(v___x_2847_, 1);
v___y_2834_ = v___y_2840_;
v_i_2835_ = v_index_2848_;
goto v___jp_2833_;
}
else
{
lean_dec_ref(v___x_2832_);
lean_dec_ref(v_val_2752_);
return v___y_2840_;
}
}
}
}
v___jp_2849_:
{
lean_object* v_size_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_size_2852_ = lean_ctor_get(v___y_2850_, 0);
v___x_2853_ = lean_nat_add(v_size_2852_, v___x_2827_);
v___x_2854_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2850_, v___x_2853_, v_i_2851_, v_val_2752_, v___x_2832_);
lean_dec(v_i_2851_);
return v___x_2854_;
}
v___jp_2855_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2750_);
lean_dec_ref(v_histogram_2750_);
v___x_2857_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v___x_2856_, v_val_2752_);
switch(lean_obj_tag(v___x_2857_))
{
case 0:
{
lean_object* v_index_2858_; lean_object* v_size_2859_; lean_object* v___x_2860_; 
v_index_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_index_2858_);
lean_dec_ref_known(v___x_2857_, 3);
v_size_2859_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_size_2859_);
v___x_2860_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2856_, v_size_2859_, v_index_2858_, v_val_2752_, v___x_2832_);
lean_dec(v_index_2858_);
return v___x_2860_;
}
case 1:
{
lean_object* v_index_2861_; 
v_index_2861_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_index_2861_);
lean_dec_ref_known(v___x_2857_, 1);
v___y_2850_ = v___x_2856_;
v_i_2851_ = v_index_2861_;
goto v___jp_2849_;
}
default: 
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2862_ = lean_unsigned_to_nat(0u);
v___x_2863_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2856_, v___x_2862_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_index_2864_; 
v_index_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_index_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v___y_2850_ = v___x_2856_;
v_i_2851_ = v_index_2864_;
goto v___jp_2849_;
}
else
{
lean_dec_ref(v___x_2832_);
lean_dec_ref(v_val_2752_);
return v___x_2856_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(lean_object* v_upperBound_2898_, lean_object* v_fst_2899_, lean_object* v___x_2900_, lean_object* v_fst_2901_, lean_object* v_a_2902_, lean_object* v_b_2903_){
_start:
{
uint8_t v___x_2904_; 
v___x_2904_ = lean_nat_dec_lt(v_a_2902_, v_upperBound_2898_);
if (v___x_2904_ == 0)
{
lean_dec(v_a_2902_);
return v_b_2903_;
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2905_ = l_Subarray_get___redArg(v_fst_2901_, v_a_2902_);
lean_inc(v_a_2902_);
v___x_2906_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_b_2903_, v_a_2902_, v___x_2905_);
v___x_2907_ = lean_unsigned_to_nat(1u);
v___x_2908_ = lean_nat_add(v_a_2902_, v___x_2907_);
lean_dec(v_a_2902_);
v_a_2902_ = v___x_2908_;
v_b_2903_ = v___x_2906_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg___boxed(lean_object* v_upperBound_2910_, lean_object* v_fst_2911_, lean_object* v___x_2912_, lean_object* v_fst_2913_, lean_object* v_a_2914_, lean_object* v_b_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_upperBound_2910_, v_fst_2911_, v___x_2912_, v_fst_2913_, v_a_2914_, v_b_2915_);
lean_dec_ref(v_fst_2913_);
lean_dec(v___x_2912_);
lean_dec_ref(v_fst_2911_);
lean_dec(v_upperBound_2910_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(lean_object* v_a_2917_, lean_object* v_b_2918_){
_start:
{
lean_object* v_array_2919_; lean_object* v_start_2920_; lean_object* v_stop_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2934_; 
v_array_2919_ = lean_ctor_get(v_a_2917_, 0);
v_start_2920_ = lean_ctor_get(v_a_2917_, 1);
v_stop_2921_ = lean_ctor_get(v_a_2917_, 2);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_a_2917_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2923_ = v_a_2917_;
v_isShared_2924_ = v_isSharedCheck_2934_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_stop_2921_);
lean_inc(v_start_2920_);
lean_inc(v_array_2919_);
lean_dec(v_a_2917_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2934_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
uint8_t v___x_2925_; 
v___x_2925_ = lean_nat_dec_lt(v_start_2920_, v_stop_2921_);
if (v___x_2925_ == 0)
{
lean_del_object(v___x_2923_);
lean_dec(v_stop_2921_);
lean_dec(v_start_2920_);
lean_dec_ref(v_array_2919_);
return v_b_2918_;
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = lean_nat_add(v_start_2920_, v___x_2926_);
lean_inc_ref(v_array_2919_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v___x_2927_);
v___x_2929_ = v___x_2923_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_array_2919_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v_stop_2921_);
v___x_2929_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = lean_array_fget(v_array_2919_, v_start_2920_);
lean_dec(v_start_2920_);
lean_dec_ref(v_array_2919_);
v___x_2931_ = lean_array_push(v_b_2918_, v___x_2930_);
v_a_2917_ = v___x_2929_;
v_b_2918_ = v___x_2931_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(lean_object* v_left_2935_, lean_object* v_right_2936_, lean_object* v_i_2937_){
_start:
{
lean_object* v_start_2938_; lean_object* v_stop_2939_; lean_object* v___x_2940_; uint8_t v___x_2954_; 
v_start_2938_ = lean_ctor_get(v_left_2935_, 1);
v_stop_2939_ = lean_ctor_get(v_left_2935_, 2);
v___x_2940_ = lean_nat_sub(v_stop_2939_, v_start_2938_);
v___x_2954_ = lean_nat_dec_lt(v_i_2937_, v___x_2940_);
if (v___x_2954_ == 0)
{
goto v___jp_2941_;
}
else
{
lean_object* v_start_2955_; lean_object* v_stop_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v_start_2955_ = lean_ctor_get(v_right_2936_, 1);
v_stop_2956_ = lean_ctor_get(v_right_2936_, 2);
v___x_2957_ = lean_nat_sub(v_stop_2956_, v_start_2955_);
v___x_2958_ = lean_nat_dec_lt(v_i_2937_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_dec(v___x_2957_);
goto v___jp_2941_;
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2959_ = lean_nat_sub(v___x_2940_, v_i_2937_);
lean_dec(v___x_2940_);
v___x_2960_ = lean_unsigned_to_nat(1u);
v___x_2961_ = lean_nat_sub(v___x_2959_, v___x_2960_);
v___x_2962_ = l_Subarray_get___redArg(v_left_2935_, v___x_2961_);
lean_dec(v___x_2961_);
v___x_2963_ = lean_nat_sub(v___x_2957_, v_i_2937_);
lean_dec(v___x_2957_);
v___x_2964_ = lean_nat_sub(v___x_2963_, v___x_2960_);
v___x_2965_ = l_Subarray_get___redArg(v_right_2936_, v___x_2964_);
lean_dec(v___x_2964_);
v___x_2966_ = lean_string_dec_eq(v___x_2962_, v___x_2965_);
lean_dec(v___x_2965_);
lean_dec(v___x_2962_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_dec(v_i_2937_);
lean_inc_ref(v_left_2935_);
v___x_2967_ = l_Subarray_take___redArg(v_left_2935_, v___x_2959_);
v___x_2968_ = l_Subarray_take___redArg(v_right_2936_, v___x_2963_);
lean_dec(v___x_2963_);
v___x_2969_ = l_Subarray_drop___redArg(v_left_2935_, v___x_2959_);
lean_dec(v___x_2959_);
v___x_2970_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_2971_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_2969_, v___x_2970_);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2968_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2967_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
return v___x_2973_;
}
else
{
lean_object* v___x_2974_; 
lean_dec(v___x_2963_);
lean_dec(v___x_2959_);
v___x_2974_ = lean_nat_add(v_i_2937_, v___x_2960_);
lean_dec(v_i_2937_);
v_i_2937_ = v___x_2974_;
goto _start;
}
}
}
v___jp_2941_:
{
lean_object* v_start_2942_; lean_object* v_stop_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_start_2942_ = lean_ctor_get(v_right_2936_, 1);
v_stop_2943_ = lean_ctor_get(v_right_2936_, 2);
v___x_2944_ = lean_nat_sub(v___x_2940_, v_i_2937_);
lean_dec(v___x_2940_);
lean_inc_ref(v_left_2935_);
v___x_2945_ = l_Subarray_take___redArg(v_left_2935_, v___x_2944_);
v___x_2946_ = lean_nat_sub(v_stop_2943_, v_start_2942_);
v___x_2947_ = lean_nat_sub(v___x_2946_, v_i_2937_);
lean_dec(v_i_2937_);
lean_dec(v___x_2946_);
v___x_2948_ = l_Subarray_take___redArg(v_right_2936_, v___x_2947_);
lean_dec(v___x_2947_);
v___x_2949_ = l_Subarray_drop___redArg(v_left_2935_, v___x_2944_);
lean_dec(v___x_2944_);
v___x_2950_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_2951_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_2949_, v___x_2950_);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2948_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2945_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(lean_object* v_left_2976_, lean_object* v_right_2977_){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_unsigned_to_nat(0u);
v___x_2979_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(v_left_2976_, v_right_2977_, v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___redArg(lean_object* v_histogram_2980_, lean_object* v_index_2981_, lean_object* v_val_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22___redArg(v_histogram_2980_, v_val_2982_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___y_2990_; lean_object* v_i_2991_; lean_object* v___y_2996_; lean_object* v___y_3005_; lean_object* v_i_3006_; lean_object* v___x_3019_; 
v___x_2984_ = lean_unsigned_to_nat(0u);
v___x_2985_ = lean_box(0);
v___x_2986_ = lean_unsigned_to_nat(1u);
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_index_2981_);
v___x_2988_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2984_);
lean_ctor_set(v___x_2988_, 1, v___x_2985_);
lean_ctor_set(v___x_2988_, 2, v___x_2986_);
lean_ctor_set(v___x_2988_, 3, v___x_2987_);
v___x_3019_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v_histogram_2980_, v_val_2982_);
switch(lean_obj_tag(v___x_3019_))
{
case 0:
{
lean_object* v_index_3020_; lean_object* v_size_3021_; lean_object* v___x_3022_; 
v_index_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_index_3020_);
lean_dec_ref_known(v___x_3019_, 3);
v_size_3021_ = lean_ctor_get(v_histogram_2980_, 0);
lean_inc(v_size_3021_);
v___x_3022_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2980_, v_size_3021_, v_index_3020_, v_val_2982_, v___x_2988_);
lean_dec(v_index_3020_);
return v___x_3022_;
}
case 1:
{
lean_object* v_index_3023_; lean_object* v_size_3024_; lean_object* v_keyArray_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v_index_3023_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_index_3023_);
lean_dec_ref_known(v___x_3019_, 1);
v_size_3024_ = lean_ctor_get(v_histogram_2980_, 0);
v_keyArray_3025_ = lean_ctor_get(v_histogram_2980_, 1);
v___x_3026_ = lean_nat_add(v_size_3024_, v___x_2986_);
v___x_3027_ = lean_array_get_size(v_keyArray_3025_);
v___x_3028_ = lean_nat_dec_lt(v___x_3026_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_dec(v___x_3026_);
lean_dec(v_index_3023_);
goto v___jp_3010_;
}
else
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; 
v___x_3029_ = lean_unsigned_to_nat(4u);
v___x_3030_ = lean_nat_mul(v___x_3026_, v___x_3029_);
v___x_3031_ = lean_unsigned_to_nat(3u);
v___x_3032_ = lean_nat_mul(v___x_3027_, v___x_3031_);
v___x_3033_ = lean_nat_dec_le(v___x_3030_, v___x_3032_);
lean_dec(v___x_3032_);
lean_dec(v___x_3030_);
if (v___x_3033_ == 0)
{
lean_dec(v___x_3026_);
lean_dec(v_index_3023_);
goto v___jp_3010_;
}
else
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2980_, v___x_3026_, v_index_3023_, v_val_2982_, v___x_2988_);
lean_dec(v_index_3023_);
return v___x_3034_;
}
}
}
default: 
{
lean_object* v_size_3035_; lean_object* v_keyArray_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; uint8_t v___x_3039_; 
v_size_3035_ = lean_ctor_get(v_histogram_2980_, 0);
v_keyArray_3036_ = lean_ctor_get(v_histogram_2980_, 1);
v___x_3037_ = lean_nat_add(v_size_3035_, v___x_2986_);
v___x_3038_ = lean_array_get_size(v_keyArray_3036_);
v___x_3039_ = lean_nat_dec_lt(v___x_3037_, v___x_3038_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; 
lean_dec(v___x_3037_);
v___x_3040_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2980_);
lean_dec_ref(v_histogram_2980_);
v___y_2996_ = v___x_3040_;
goto v___jp_2995_;
}
else
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3041_ = lean_unsigned_to_nat(4u);
v___x_3042_ = lean_nat_mul(v___x_3037_, v___x_3041_);
lean_dec(v___x_3037_);
v___x_3043_ = lean_unsigned_to_nat(3u);
v___x_3044_ = lean_nat_mul(v___x_3038_, v___x_3043_);
v___x_3045_ = lean_nat_dec_le(v___x_3042_, v___x_3044_);
lean_dec(v___x_3044_);
lean_dec(v___x_3042_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2980_);
lean_dec_ref(v_histogram_2980_);
v___y_2996_ = v___x_3046_;
goto v___jp_2995_;
}
else
{
v___y_2996_ = v_histogram_2980_;
goto v___jp_2995_;
}
}
}
}
v___jp_2989_:
{
lean_object* v_size_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v_size_2992_ = lean_ctor_get(v___y_2990_, 0);
v___x_2993_ = lean_nat_add(v_size_2992_, v___x_2986_);
v___x_2994_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2990_, v___x_2993_, v_i_2991_, v_val_2982_, v___x_2988_);
lean_dec(v_i_2991_);
return v___x_2994_;
}
v___jp_2995_:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v___y_2996_, v_val_2982_);
switch(lean_obj_tag(v___x_2997_))
{
case 0:
{
lean_object* v_index_2998_; lean_object* v_size_2999_; lean_object* v___x_3000_; 
v_index_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_index_2998_);
lean_dec_ref_known(v___x_2997_, 3);
v_size_2999_ = lean_ctor_get(v___y_2996_, 0);
lean_inc(v_size_2999_);
v___x_3000_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2996_, v_size_2999_, v_index_2998_, v_val_2982_, v___x_2988_);
lean_dec(v_index_2998_);
return v___x_3000_;
}
case 1:
{
lean_object* v_index_3001_; 
v_index_3001_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_index_3001_);
lean_dec_ref_known(v___x_2997_, 1);
v___y_2990_ = v___y_2996_;
v_i_2991_ = v_index_3001_;
goto v___jp_2989_;
}
default: 
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2996_, v___x_2984_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_index_3003_; 
v_index_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_index_3003_);
lean_dec_ref_known(v___x_3002_, 1);
v___y_2990_ = v___y_2996_;
v_i_2991_ = v_index_3003_;
goto v___jp_2989_;
}
else
{
lean_dec_ref_known(v___x_2988_, 4);
lean_dec_ref(v_val_2982_);
return v___y_2996_;
}
}
}
}
v___jp_3004_:
{
lean_object* v_size_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_size_3007_ = lean_ctor_get(v___y_3005_, 0);
v___x_3008_ = lean_nat_add(v_size_3007_, v___x_2986_);
v___x_3009_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3005_, v___x_3008_, v_i_3006_, v_val_2982_, v___x_2988_);
lean_dec(v_i_3006_);
return v___x_3009_;
}
v___jp_3010_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2980_);
lean_dec_ref(v_histogram_2980_);
v___x_3012_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v___x_3011_, v_val_2982_);
switch(lean_obj_tag(v___x_3012_))
{
case 0:
{
lean_object* v_index_3013_; lean_object* v_size_3014_; lean_object* v___x_3015_; 
v_index_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_index_3013_);
lean_dec_ref_known(v___x_3012_, 3);
v_size_3014_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_size_3014_);
v___x_3015_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3011_, v_size_3014_, v_index_3013_, v_val_2982_, v___x_2988_);
lean_dec(v_index_3013_);
return v___x_3015_;
}
case 1:
{
lean_object* v_index_3016_; 
v_index_3016_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_index_3016_);
lean_dec_ref_known(v___x_3012_, 1);
v___y_3005_ = v___x_3011_;
v_i_3006_ = v_index_3016_;
goto v___jp_3004_;
}
default: 
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3011_, v___x_2984_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_index_3018_; 
v_index_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_index_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___y_3005_ = v___x_3011_;
v_i_3006_ = v_index_3018_;
goto v___jp_3004_;
}
else
{
lean_dec_ref_known(v___x_2988_, 4);
lean_dec_ref(v_val_2982_);
return v___x_3011_;
}
}
}
}
}
else
{
lean_object* v_val_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3127_; 
v_val_3047_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3049_ = v___x_2983_;
v_isShared_3050_ = v_isSharedCheck_3127_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_val_3047_);
lean_dec(v___x_2983_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3127_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_leftCount_3051_; lean_object* v_leftIndex_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3124_; 
v_leftCount_3051_ = lean_ctor_get(v_val_3047_, 0);
v_leftIndex_3052_ = lean_ctor_get(v_val_3047_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_val_3047_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; lean_object* v_unused_3126_; 
v_unused_3125_ = lean_ctor_get(v_val_3047_, 3);
lean_dec(v_unused_3125_);
v_unused_3126_ = lean_ctor_get(v_val_3047_, 2);
lean_dec(v_unused_3126_);
v___x_3054_ = v_val_3047_;
v_isShared_3055_ = v_isSharedCheck_3124_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_leftIndex_3052_);
lean_inc(v_leftCount_3051_);
lean_dec(v_val_3047_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3124_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
v___x_3056_ = lean_unsigned_to_nat(1u);
v___x_3057_ = lean_nat_add(v_leftCount_3051_, v___x_3056_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v_index_2981_);
v___x_3059_ = v___x_3049_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_index_2981_);
v___x_3059_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3061_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 3, v___x_3059_);
lean_ctor_set(v___x_3054_, 2, v___x_3057_);
v___x_3061_ = v___x_3054_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_leftCount_3051_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_leftIndex_3052_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___y_3063_; lean_object* v_i_3064_; lean_object* v___y_3069_; lean_object* v___y_3079_; lean_object* v_i_3080_; lean_object* v___x_3094_; 
v___x_3094_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v_histogram_2980_, v_val_2982_);
switch(lean_obj_tag(v___x_3094_))
{
case 0:
{
lean_object* v_index_3095_; lean_object* v_size_3096_; lean_object* v___x_3097_; 
v_index_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_index_3095_);
lean_dec_ref_known(v___x_3094_, 3);
v_size_3096_ = lean_ctor_get(v_histogram_2980_, 0);
lean_inc(v_size_3096_);
v___x_3097_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2980_, v_size_3096_, v_index_3095_, v_val_2982_, v___x_3061_);
lean_dec(v_index_3095_);
return v___x_3097_;
}
case 1:
{
lean_object* v_index_3098_; lean_object* v_size_3099_; lean_object* v_keyArray_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v_index_3098_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_index_3098_);
lean_dec_ref_known(v___x_3094_, 1);
v_size_3099_ = lean_ctor_get(v_histogram_2980_, 0);
v_keyArray_3100_ = lean_ctor_get(v_histogram_2980_, 1);
v___x_3101_ = lean_nat_add(v_size_3099_, v___x_3056_);
v___x_3102_ = lean_array_get_size(v_keyArray_3100_);
v___x_3103_ = lean_nat_dec_lt(v___x_3101_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_dec(v___x_3101_);
lean_dec(v_index_3098_);
goto v___jp_3084_;
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3104_ = lean_unsigned_to_nat(4u);
v___x_3105_ = lean_nat_mul(v___x_3101_, v___x_3104_);
v___x_3106_ = lean_unsigned_to_nat(3u);
v___x_3107_ = lean_nat_mul(v___x_3102_, v___x_3106_);
v___x_3108_ = lean_nat_dec_le(v___x_3105_, v___x_3107_);
lean_dec(v___x_3107_);
lean_dec(v___x_3105_);
if (v___x_3108_ == 0)
{
lean_dec(v___x_3101_);
lean_dec(v_index_3098_);
goto v___jp_3084_;
}
else
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2980_, v___x_3101_, v_index_3098_, v_val_2982_, v___x_3061_);
lean_dec(v_index_3098_);
return v___x_3109_;
}
}
}
default: 
{
lean_object* v_size_3110_; lean_object* v_keyArray_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v_size_3110_ = lean_ctor_get(v_histogram_2980_, 0);
v_keyArray_3111_ = lean_ctor_get(v_histogram_2980_, 1);
v___x_3112_ = lean_nat_add(v_size_3110_, v___x_3056_);
v___x_3113_ = lean_array_get_size(v_keyArray_3111_);
v___x_3114_ = lean_nat_dec_lt(v___x_3112_, v___x_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; 
lean_dec(v___x_3112_);
v___x_3115_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2980_);
lean_dec_ref(v_histogram_2980_);
v___y_3069_ = v___x_3115_;
goto v___jp_3068_;
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3116_ = lean_unsigned_to_nat(4u);
v___x_3117_ = lean_nat_mul(v___x_3112_, v___x_3116_);
lean_dec(v___x_3112_);
v___x_3118_ = lean_unsigned_to_nat(3u);
v___x_3119_ = lean_nat_mul(v___x_3113_, v___x_3118_);
v___x_3120_ = lean_nat_dec_le(v___x_3117_, v___x_3119_);
lean_dec(v___x_3119_);
lean_dec(v___x_3117_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2980_);
lean_dec_ref(v_histogram_2980_);
v___y_3069_ = v___x_3121_;
goto v___jp_3068_;
}
else
{
v___y_3069_ = v_histogram_2980_;
goto v___jp_3068_;
}
}
}
}
v___jp_3062_:
{
lean_object* v_size_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v_size_3065_ = lean_ctor_get(v___y_3063_, 0);
v___x_3066_ = lean_nat_add(v_size_3065_, v___x_3056_);
v___x_3067_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3063_, v___x_3066_, v_i_3064_, v_val_2982_, v___x_3061_);
lean_dec(v_i_3064_);
return v___x_3067_;
}
v___jp_3068_:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v___y_3069_, v_val_2982_);
switch(lean_obj_tag(v___x_3070_))
{
case 0:
{
lean_object* v_index_3071_; lean_object* v_size_3072_; lean_object* v___x_3073_; 
v_index_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_index_3071_);
lean_dec_ref_known(v___x_3070_, 3);
v_size_3072_ = lean_ctor_get(v___y_3069_, 0);
lean_inc(v_size_3072_);
v___x_3073_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3069_, v_size_3072_, v_index_3071_, v_val_2982_, v___x_3061_);
lean_dec(v_index_3071_);
return v___x_3073_;
}
case 1:
{
lean_object* v_index_3074_; 
v_index_3074_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_index_3074_);
lean_dec_ref_known(v___x_3070_, 1);
v___y_3063_ = v___y_3069_;
v_i_3064_ = v_index_3074_;
goto v___jp_3062_;
}
default: 
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3069_, v___x_3075_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_index_3077_; 
v_index_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_index_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___y_3063_ = v___y_3069_;
v_i_3064_ = v_index_3077_;
goto v___jp_3062_;
}
else
{
lean_dec_ref(v___x_3061_);
lean_dec_ref(v_val_2982_);
return v___y_3069_;
}
}
}
}
v___jp_3078_:
{
lean_object* v_size_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_size_3081_ = lean_ctor_get(v___y_3079_, 0);
v___x_3082_ = lean_nat_add(v_size_3081_, v___x_3056_);
v___x_3083_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3079_, v___x_3082_, v_i_3080_, v_val_2982_, v___x_3061_);
lean_dec(v_i_3080_);
return v___x_3083_;
}
v___jp_3084_:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_histogram_2980_);
lean_dec_ref(v_histogram_2980_);
v___x_3086_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v___x_3085_, v_val_2982_);
switch(lean_obj_tag(v___x_3086_))
{
case 0:
{
lean_object* v_index_3087_; lean_object* v_size_3088_; lean_object* v___x_3089_; 
v_index_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_index_3087_);
lean_dec_ref_known(v___x_3086_, 3);
v_size_3088_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_size_3088_);
v___x_3089_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3085_, v_size_3088_, v_index_3087_, v_val_2982_, v___x_3061_);
lean_dec(v_index_3087_);
return v___x_3089_;
}
case 1:
{
lean_object* v_index_3090_; 
v_index_3090_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_index_3090_);
lean_dec_ref_known(v___x_3086_, 1);
v___y_3079_ = v___x_3085_;
v_i_3080_ = v_index_3090_;
goto v___jp_3078_;
}
default: 
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_unsigned_to_nat(0u);
v___x_3092_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3085_, v___x_3091_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_index_3093_; 
v_index_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_index_3093_);
lean_dec_ref_known(v___x_3092_, 1);
v___y_3079_ = v___x_3085_;
v_i_3080_ = v_index_3093_;
goto v___jp_3078_;
}
else
{
lean_dec_ref(v___x_3061_);
lean_dec_ref(v_val_2982_);
return v___x_3085_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(lean_object* v_upperBound_3128_, lean_object* v___x_3129_, lean_object* v_fst_3130_, lean_object* v___x_3131_, lean_object* v_a_3132_, lean_object* v_b_3133_){
_start:
{
uint8_t v___x_3134_; 
v___x_3134_ = lean_nat_dec_lt(v_a_3132_, v_upperBound_3128_);
if (v___x_3134_ == 0)
{
lean_dec(v_a_3132_);
return v_b_3133_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3135_ = l_Subarray_get___redArg(v_fst_3130_, v_a_3132_);
lean_inc(v_a_3132_);
v___x_3136_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___redArg(v_b_3133_, v_a_3132_, v___x_3135_);
v___x_3137_ = lean_unsigned_to_nat(1u);
v___x_3138_ = lean_nat_add(v_a_3132_, v___x_3137_);
lean_dec(v_a_3132_);
v_a_3132_ = v___x_3138_;
v_b_3133_ = v___x_3136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg___boxed(lean_object* v_upperBound_3140_, lean_object* v___x_3141_, lean_object* v_fst_3142_, lean_object* v___x_3143_, lean_object* v_a_3144_, lean_object* v_b_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_upperBound_3140_, v___x_3141_, v_fst_3142_, v___x_3143_, v_a_3144_, v_b_3145_);
lean_dec(v___x_3143_);
lean_dec_ref(v_fst_3142_);
lean_dec(v___x_3141_);
lean_dec(v_upperBound_3140_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___redArg(lean_object* v_as_x27_3147_, lean_object* v_b_3148_){
_start:
{
if (lean_obj_tag(v_as_x27_3147_) == 0)
{
return v_b_3148_;
}
else
{
lean_object* v_head_3149_; lean_object* v_snd_3150_; lean_object* v_leftIndex_3151_; 
v_head_3149_ = lean_ctor_get(v_as_x27_3147_, 0);
v_snd_3150_ = lean_ctor_get(v_head_3149_, 1);
v_leftIndex_3151_ = lean_ctor_get(v_snd_3150_, 1);
if (lean_obj_tag(v_leftIndex_3151_) == 1)
{
lean_object* v_rightIndex_3152_; 
v_rightIndex_3152_ = lean_ctor_get(v_snd_3150_, 3);
if (lean_obj_tag(v_rightIndex_3152_) == 1)
{
if (lean_obj_tag(v_b_3148_) == 0)
{
lean_object* v_tail_3153_; lean_object* v_fst_3154_; lean_object* v_leftCount_3155_; lean_object* v_rightCount_3156_; lean_object* v_val_3157_; lean_object* v_val_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_tail_3153_ = lean_ctor_get(v_as_x27_3147_, 1);
v_fst_3154_ = lean_ctor_get(v_head_3149_, 0);
v_leftCount_3155_ = lean_ctor_get(v_snd_3150_, 0);
v_rightCount_3156_ = lean_ctor_get(v_snd_3150_, 2);
v_val_3157_ = lean_ctor_get(v_leftIndex_3151_, 0);
v_val_3158_ = lean_ctor_get(v_rightIndex_3152_, 0);
v___x_3159_ = lean_nat_add(v_leftCount_3155_, v_rightCount_3156_);
lean_inc(v_val_3158_);
lean_inc(v_val_3157_);
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v_val_3157_);
lean_ctor_set(v___x_3160_, 1, v_val_3158_);
lean_inc(v_fst_3154_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v_fst_3154_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3159_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
v_as_x27_3147_ = v_tail_3153_;
v_b_3148_ = v___x_3163_;
goto _start;
}
else
{
lean_object* v_val_3165_; lean_object* v_tail_3166_; lean_object* v_fst_3167_; lean_object* v_leftCount_3168_; lean_object* v_rightCount_3169_; lean_object* v_val_3170_; lean_object* v_val_3171_; lean_object* v_fst_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3193_; 
v_val_3165_ = lean_ctor_get(v_b_3148_, 0);
lean_inc(v_val_3165_);
v_tail_3166_ = lean_ctor_get(v_as_x27_3147_, 1);
v_fst_3167_ = lean_ctor_get(v_head_3149_, 0);
v_leftCount_3168_ = lean_ctor_get(v_snd_3150_, 0);
v_rightCount_3169_ = lean_ctor_get(v_snd_3150_, 2);
v_val_3170_ = lean_ctor_get(v_leftIndex_3151_, 0);
v_val_3171_ = lean_ctor_get(v_rightIndex_3152_, 0);
v_fst_3172_ = lean_ctor_get(v_val_3165_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_val_3165_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; 
v_unused_3194_ = lean_ctor_get(v_val_3165_, 1);
lean_dec(v_unused_3194_);
v___x_3174_ = v_val_3165_;
v_isShared_3175_ = v_isSharedCheck_3193_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_fst_3172_);
lean_dec(v_val_3165_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3193_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3176_ = lean_nat_add(v_leftCount_3168_, v_rightCount_3169_);
v___x_3177_ = lean_nat_dec_lt(v___x_3176_, v_fst_3172_);
lean_dec(v_fst_3172_);
if (v___x_3177_ == 0)
{
lean_dec(v___x_3176_);
lean_del_object(v___x_3174_);
v_as_x27_3147_ = v_tail_3166_;
goto _start;
}
else
{
lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3191_; 
v_isSharedCheck_3191_ = !lean_is_exclusive(v_b_3148_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; 
v_unused_3192_ = lean_ctor_get(v_b_3148_, 0);
lean_dec(v_unused_3192_);
v___x_3180_ = v_b_3148_;
v_isShared_3181_ = v_isSharedCheck_3191_;
goto v_resetjp_3179_;
}
else
{
lean_dec(v_b_3148_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3191_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
lean_inc(v_val_3171_);
lean_inc(v_val_3170_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 1, v_val_3171_);
lean_ctor_set(v___x_3174_, 0, v_val_3170_);
v___x_3183_ = v___x_3174_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_val_3170_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_val_3171_);
v___x_3183_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
lean_inc(v_fst_3167_);
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v_fst_3167_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3176_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3185_);
v___x_3187_ = v___x_3180_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
v_as_x27_3147_ = v_tail_3166_;
v_b_3148_ = v___x_3187_;
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
lean_object* v_tail_3195_; 
v_tail_3195_ = lean_ctor_get(v_as_x27_3147_, 1);
v_as_x27_3147_ = v_tail_3195_;
goto _start;
}
}
else
{
lean_object* v_tail_3197_; 
v_tail_3197_ = lean_ctor_get(v_as_x27_3147_, 1);
v_as_x27_3147_ = v_tail_3197_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___redArg___boxed(lean_object* v_as_x27_3199_, lean_object* v_b_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___redArg(v_as_x27_3199_, v_b_3200_);
lean_dec(v_as_x27_3199_);
return v_res_3201_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v_cellCount_3202_; lean_object* v___x_3203_; 
v_cellCount_3202_ = lean_unsigned_to_nat(16u);
v___x_3203_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3202_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v_cellCount_3204_; lean_object* v___x_3205_; 
v_cellCount_3204_ = lean_unsigned_to_nat(16u);
v___x_3205_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3204_);
return v___x_3205_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v_hist_3209_; 
v___x_3206_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1);
v___x_3207_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0);
v___x_3208_ = lean_unsigned_to_nat(0u);
v_hist_3209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_hist_3209_, 0, v___x_3208_);
lean_ctor_set(v_hist_3209_, 1, v___x_3207_);
lean_ctor_set(v_hist_3209_, 2, v___x_3206_);
return v_hist_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v_left_3210_, lean_object* v_right_3211_){
_start:
{
lean_object* v___x_3212_; lean_object* v_snd_3213_; lean_object* v_fst_3214_; lean_object* v_fst_3215_; lean_object* v_snd_3216_; lean_object* v___x_3217_; lean_object* v_snd_3218_; lean_object* v_fst_3219_; lean_object* v_fst_3220_; lean_object* v_snd_3221_; lean_object* v_start_3222_; lean_object* v_stop_3223_; lean_object* v___x_3224_; lean_object* v_hist_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v_start_3228_; lean_object* v_stop_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3212_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(v_left_3210_, v_right_3211_);
v_snd_3213_ = lean_ctor_get(v___x_3212_, 1);
lean_inc(v_snd_3213_);
v_fst_3214_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_fst_3214_);
lean_dec_ref(v___x_3212_);
v_fst_3215_ = lean_ctor_get(v_snd_3213_, 0);
lean_inc(v_fst_3215_);
v_snd_3216_ = lean_ctor_get(v_snd_3213_, 1);
lean_inc(v_snd_3216_);
lean_dec(v_snd_3213_);
v___x_3217_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(v_fst_3215_, v_snd_3216_);
v_snd_3218_ = lean_ctor_get(v___x_3217_, 1);
lean_inc(v_snd_3218_);
v_fst_3219_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_fst_3219_);
lean_dec_ref(v___x_3217_);
v_fst_3220_ = lean_ctor_get(v_snd_3218_, 0);
lean_inc(v_fst_3220_);
v_snd_3221_ = lean_ctor_get(v_snd_3218_, 1);
lean_inc(v_snd_3221_);
lean_dec(v_snd_3218_);
v_start_3222_ = lean_ctor_get(v_fst_3219_, 1);
v_stop_3223_ = lean_ctor_get(v_fst_3219_, 2);
v___x_3224_ = lean_unsigned_to_nat(0u);
v_hist_3225_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__2, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__2_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__2);
v___x_3226_ = lean_nat_sub(v_stop_3223_, v_start_3222_);
v___x_3227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v___x_3226_, v_fst_3220_, v___x_3226_, v_fst_3219_, v___x_3224_, v_hist_3225_);
v_start_3228_ = lean_ctor_get(v_fst_3220_, 1);
v_stop_3229_ = lean_ctor_get(v_fst_3220_, 2);
v___x_3230_ = lean_nat_sub(v_stop_3229_, v_start_3228_);
v___x_3231_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v___x_3230_, v___x_3230_, v_fst_3220_, v___x_3226_, v___x_3224_, v___x_3227_);
lean_dec(v___x_3226_);
lean_dec(v___x_3230_);
v___x_3232_ = lean_box(0);
v___x_3233_ = lean_box(0);
v___x_3234_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(v___x_3231_, v___x_3233_, v___x_3224_);
lean_dec_ref(v___x_3231_);
v___x_3235_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___redArg(v___x_3234_, v___x_3232_);
lean_dec(v___x_3234_);
if (lean_obj_tag(v___x_3235_) == 1)
{
lean_object* v_val_3236_; lean_object* v_snd_3237_; lean_object* v_snd_3238_; lean_object* v_fst_3239_; lean_object* v_fst_3240_; lean_object* v_snd_3241_; lean_object* v___x_3242_; lean_object* v_fst_3243_; lean_object* v_snd_3244_; lean_object* v___x_3245_; lean_object* v_fst_3246_; lean_object* v_snd_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_val_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_val_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v_snd_3237_ = lean_ctor_get(v_val_3236_, 1);
lean_inc(v_snd_3237_);
lean_dec(v_val_3236_);
v_snd_3238_ = lean_ctor_get(v_snd_3237_, 1);
lean_inc(v_snd_3238_);
v_fst_3239_ = lean_ctor_get(v_snd_3237_, 0);
lean_inc(v_fst_3239_);
lean_dec(v_snd_3237_);
v_fst_3240_ = lean_ctor_get(v_snd_3238_, 0);
lean_inc(v_fst_3240_);
v_snd_3241_ = lean_ctor_get(v_snd_3238_, 1);
lean_inc(v_snd_3241_);
lean_dec(v_snd_3238_);
v___x_3242_ = l_Subarray_split___redArg(v_fst_3219_, v_fst_3240_);
lean_dec(v_fst_3240_);
v_fst_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_fst_3243_);
v_snd_3244_ = lean_ctor_get(v___x_3242_, 1);
lean_inc(v_snd_3244_);
lean_dec_ref(v___x_3242_);
v___x_3245_ = l_Subarray_split___redArg(v_fst_3220_, v_snd_3241_);
lean_dec(v_snd_3241_);
v_fst_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_fst_3246_);
v_snd_3247_ = lean_ctor_get(v___x_3245_, 1);
lean_inc(v_snd_3247_);
lean_dec_ref(v___x_3245_);
v___x_3248_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v_fst_3243_, v_fst_3246_);
v___x_3249_ = l_Array_append___redArg(v_fst_3214_, v___x_3248_);
lean_dec_ref(v___x_3248_);
v___x_3250_ = lean_unsigned_to_nat(1u);
v___x_3251_ = lean_mk_empty_array_with_capacity(v___x_3250_);
v___x_3252_ = lean_array_push(v___x_3251_, v_fst_3239_);
v___x_3253_ = l_Array_append___redArg(v___x_3249_, v___x_3252_);
lean_dec_ref(v___x_3252_);
v___x_3254_ = l_Subarray_drop___redArg(v_snd_3244_, v___x_3250_);
v___x_3255_ = l_Subarray_drop___redArg(v_snd_3247_, v___x_3250_);
v___x_3256_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3254_, v___x_3255_);
v___x_3257_ = l_Array_append___redArg(v___x_3253_, v___x_3256_);
lean_dec_ref(v___x_3256_);
v___x_3258_ = l_Array_append___redArg(v___x_3257_, v_snd_3221_);
lean_dec(v_snd_3221_);
return v___x_3258_;
}
else
{
lean_object* v___x_3259_; 
lean_dec(v___x_3235_);
lean_dec(v_fst_3220_);
lean_dec(v_fst_3219_);
v___x_3259_ = l_Array_append___redArg(v_fst_3214_, v_snd_3221_);
lean_dec(v_snd_3221_);
return v___x_3259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v_original_3260_, lean_object* v___x_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v_fst_3264_; lean_object* v_snd_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3290_; 
v_fst_3264_ = lean_ctor_get(v_a_3263_, 0);
v_snd_3265_ = lean_ctor_get(v_a_3263_, 1);
v_isSharedCheck_3290_ = !lean_is_exclusive(v_a_3263_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3267_ = v_a_3263_;
v_isShared_3268_ = v_isSharedCheck_3290_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_snd_3265_);
lean_inc(v_fst_3264_);
lean_dec(v_a_3263_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3290_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; uint8_t v___y_3271_; uint8_t v___x_3286_; 
v___x_3269_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_3286_ = lean_nat_dec_lt(v_snd_3265_, v___x_3261_);
if (v___x_3286_ == 0)
{
v___y_3271_ = v___x_3286_;
goto v___jp_3270_;
}
else
{
lean_object* v___x_3287_; uint8_t v___x_3288_; 
v___x_3287_ = lean_array_get_borrowed(v___x_3269_, v_original_3260_, v_snd_3265_);
v___x_3288_ = lean_string_dec_eq(v___x_3287_, v_a_3262_);
if (v___x_3288_ == 0)
{
v___y_3271_ = v___x_3286_;
goto v___jp_3270_;
}
else
{
lean_object* v___x_3289_; 
lean_del_object(v___x_3267_);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v_fst_3264_);
lean_ctor_set(v___x_3289_, 1, v_snd_3265_);
return v___x_3289_;
}
}
v___jp_3270_:
{
if (v___y_3271_ == 0)
{
lean_object* v___x_3273_; 
if (v_isShared_3268_ == 0)
{
v___x_3273_ = v___x_3267_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_fst_3264_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_snd_3265_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
else
{
uint8_t v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
v___x_3275_ = 1;
v___x_3276_ = lean_array_get_borrowed(v___x_3269_, v_original_3260_, v_snd_3265_);
v___x_3277_ = lean_box(v___x_3275_);
lean_inc(v___x_3276_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 1, v___x_3276_);
lean_ctor_set(v___x_3267_, 0, v___x_3277_);
v___x_3279_ = v___x_3267_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3277_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v___x_3276_);
v___x_3279_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3280_ = lean_array_push(v_fst_3264_, v___x_3279_);
v___x_3281_ = lean_unsigned_to_nat(1u);
v___x_3282_ = lean_nat_add(v_snd_3265_, v___x_3281_);
lean_dec(v_snd_3265_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3280_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v_a_3263_ = v___x_3283_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v_original_3291_, lean_object* v___x_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_3291_, v___x_3292_, v_a_3293_, v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v___x_3292_);
lean_dec_ref(v_original_3291_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(lean_object* v_edited_3296_, lean_object* v___x_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v_fst_3300_; lean_object* v_snd_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3326_; 
v_fst_3300_ = lean_ctor_get(v_a_3299_, 0);
v_snd_3301_ = lean_ctor_get(v_a_3299_, 1);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_a_3299_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3303_ = v_a_3299_;
v_isShared_3304_ = v_isSharedCheck_3326_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_snd_3301_);
lean_inc(v_fst_3300_);
lean_dec(v_a_3299_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3326_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; uint8_t v___y_3307_; uint8_t v___x_3322_; 
v___x_3305_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_3322_ = lean_nat_dec_lt(v_snd_3301_, v___x_3297_);
if (v___x_3322_ == 0)
{
v___y_3307_ = v___x_3322_;
goto v___jp_3306_;
}
else
{
lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3323_ = lean_array_get_borrowed(v___x_3305_, v_edited_3296_, v_snd_3301_);
v___x_3324_ = lean_string_dec_eq(v___x_3323_, v_a_3298_);
if (v___x_3324_ == 0)
{
v___y_3307_ = v___x_3322_;
goto v___jp_3306_;
}
else
{
lean_object* v___x_3325_; 
lean_del_object(v___x_3303_);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v_fst_3300_);
lean_ctor_set(v___x_3325_, 1, v_snd_3301_);
return v___x_3325_;
}
}
v___jp_3306_:
{
if (v___y_3307_ == 0)
{
lean_object* v___x_3309_; 
if (v_isShared_3304_ == 0)
{
v___x_3309_ = v___x_3303_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_fst_3300_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_snd_3301_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
else
{
uint8_t v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3311_ = 0;
v___x_3312_ = lean_array_get_borrowed(v___x_3305_, v_edited_3296_, v_snd_3301_);
v___x_3313_ = lean_box(v___x_3311_);
lean_inc(v___x_3312_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 1, v___x_3312_);
lean_ctor_set(v___x_3303_, 0, v___x_3313_);
v___x_3315_ = v___x_3303_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v___x_3312_);
v___x_3315_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3316_ = lean_array_push(v_fst_3300_, v___x_3315_);
v___x_3317_ = lean_unsigned_to_nat(1u);
v___x_3318_ = lean_nat_add(v_snd_3301_, v___x_3317_);
lean_dec(v_snd_3301_);
v___x_3319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3316_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v_a_3299_ = v___x_3319_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg___boxed(lean_object* v_edited_3327_, lean_object* v___x_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_3327_, v___x_3328_, v_a_3329_, v_a_3330_);
lean_dec_ref(v_a_3329_);
lean_dec(v___x_3328_);
lean_dec_ref(v_edited_3327_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__23(lean_object* v_original_3332_, lean_object* v___x_3333_, lean_object* v_edited_3334_, lean_object* v___x_3335_, lean_object* v_as_3336_, size_t v_sz_3337_, size_t v_i_3338_, lean_object* v_b_3339_){
_start:
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_usize_dec_lt(v_i_3338_, v_sz_3337_);
if (v___x_3340_ == 0)
{
return v_b_3339_;
}
else
{
lean_object* v_snd_3341_; lean_object* v_fst_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3389_; 
v_snd_3341_ = lean_ctor_get(v_b_3339_, 1);
v_fst_3342_ = lean_ctor_get(v_b_3339_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_b_3339_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3344_ = v_b_3339_;
v_isShared_3345_ = v_isSharedCheck_3389_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_snd_3341_);
lean_inc(v_fst_3342_);
lean_dec(v_b_3339_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3389_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v_fst_3346_; lean_object* v_snd_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3388_; 
v_fst_3346_ = lean_ctor_get(v_snd_3341_, 0);
v_snd_3347_ = lean_ctor_get(v_snd_3341_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_snd_3341_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3349_ = v_snd_3341_;
v_isShared_3350_ = v_isSharedCheck_3388_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_snd_3347_);
lean_inc(v_fst_3346_);
lean_dec(v_snd_3341_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3388_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v_a_3351_; lean_object* v___x_3353_; 
v_a_3351_ = lean_array_uget_borrowed(v_as_3336_, v_i_3338_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v_fst_3346_);
lean_ctor_set(v___x_3349_, 0, v_fst_3342_);
v___x_3353_ = v___x_3349_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_fst_3342_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_fst_3346_);
v___x_3353_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___x_3354_; lean_object* v_fst_3355_; lean_object* v_snd_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3386_; 
v___x_3354_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_3332_, v___x_3333_, v_a_3351_, v___x_3353_);
v_fst_3355_ = lean_ctor_get(v___x_3354_, 0);
v_snd_3356_ = lean_ctor_get(v___x_3354_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3358_ = v___x_3354_;
v_isShared_3359_ = v_isSharedCheck_3386_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_snd_3356_);
lean_inc(v_fst_3355_);
lean_dec(v___x_3354_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3386_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 1, v_snd_3347_);
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_fst_3355_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_snd_3347_);
v___x_3361_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3362_; lean_object* v_fst_3363_; lean_object* v_snd_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3384_; 
v___x_3362_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_3334_, v___x_3335_, v_a_3351_, v___x_3361_);
v_fst_3363_ = lean_ctor_get(v___x_3362_, 0);
v_snd_3364_ = lean_ctor_get(v___x_3362_, 1);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3366_ = v___x_3362_;
v_isShared_3367_ = v_isSharedCheck_3384_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_snd_3364_);
lean_inc(v_fst_3363_);
lean_dec(v___x_3362_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3384_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
uint8_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3368_ = 2;
v___x_3369_ = lean_box(v___x_3368_);
lean_inc(v_a_3351_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 1, v_a_3351_);
lean_ctor_set(v___x_3366_, 0, v___x_3369_);
v___x_3371_ = v___x_3366_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_a_3351_);
v___x_3371_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3372_ = lean_array_push(v_fst_3363_, v___x_3371_);
v___x_3373_ = lean_unsigned_to_nat(1u);
v___x_3374_ = lean_nat_add(v_snd_3356_, v___x_3373_);
lean_dec(v_snd_3356_);
v___x_3375_ = lean_nat_add(v_snd_3364_, v___x_3373_);
lean_dec(v_snd_3364_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 1, v___x_3375_);
lean_ctor_set(v___x_3344_, 0, v___x_3374_);
v___x_3377_ = v___x_3344_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3374_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3378_; size_t v___x_3379_; size_t v___x_3380_; 
v___x_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3372_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = ((size_t)1ULL);
v___x_3380_ = lean_usize_add(v_i_3338_, v___x_3379_);
v_i_3338_ = v___x_3380_;
v_b_3339_ = v___x_3378_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__23___boxed(lean_object* v_original_3390_, lean_object* v___x_3391_, lean_object* v_edited_3392_, lean_object* v___x_3393_, lean_object* v_as_3394_, lean_object* v_sz_3395_, lean_object* v_i_3396_, lean_object* v_b_3397_){
_start:
{
size_t v_sz_boxed_3398_; size_t v_i_boxed_3399_; lean_object* v_res_3400_; 
v_sz_boxed_3398_ = lean_unbox_usize(v_sz_3395_);
lean_dec(v_sz_3395_);
v_i_boxed_3399_ = lean_unbox_usize(v_i_3396_);
lean_dec(v_i_3396_);
v_res_3400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__23(v_original_3390_, v___x_3391_, v_edited_3392_, v___x_3393_, v_as_3394_, v_sz_boxed_3398_, v_i_boxed_3399_, v_b_3397_);
lean_dec_ref(v_as_3394_);
lean_dec(v___x_3393_);
lean_dec_ref(v_edited_3392_);
lean_dec(v___x_3391_);
lean_dec_ref(v_original_3390_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v_edited_3401_, lean_object* v___x_3402_, lean_object* v_original_3403_, lean_object* v___x_3404_, lean_object* v_as_3405_, size_t v_sz_3406_, size_t v_i_3407_, lean_object* v_b_3408_){
_start:
{
uint8_t v___x_3409_; 
v___x_3409_ = lean_usize_dec_lt(v_i_3407_, v_sz_3406_);
if (v___x_3409_ == 0)
{
return v_b_3408_;
}
else
{
lean_object* v_snd_3410_; lean_object* v_fst_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3458_; 
v_snd_3410_ = lean_ctor_get(v_b_3408_, 1);
v_fst_3411_ = lean_ctor_get(v_b_3408_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_b_3408_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3413_ = v_b_3408_;
v_isShared_3414_ = v_isSharedCheck_3458_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_snd_3410_);
lean_inc(v_fst_3411_);
lean_dec(v_b_3408_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3458_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v_fst_3415_; lean_object* v_snd_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3457_; 
v_fst_3415_ = lean_ctor_get(v_snd_3410_, 0);
v_snd_3416_ = lean_ctor_get(v_snd_3410_, 1);
v_isSharedCheck_3457_ = !lean_is_exclusive(v_snd_3410_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3418_ = v_snd_3410_;
v_isShared_3419_ = v_isSharedCheck_3457_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_snd_3416_);
lean_inc(v_fst_3415_);
lean_dec(v_snd_3410_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3457_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v_a_3420_; lean_object* v___x_3422_; 
v_a_3420_ = lean_array_uget_borrowed(v_as_3405_, v_i_3407_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 1, v_fst_3415_);
lean_ctor_set(v___x_3418_, 0, v_fst_3411_);
v___x_3422_ = v___x_3418_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_fst_3411_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_fst_3415_);
v___x_3422_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; lean_object* v_fst_3424_; lean_object* v_snd_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3455_; 
v___x_3423_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_3403_, v___x_3404_, v_a_3420_, v___x_3422_);
v_fst_3424_ = lean_ctor_get(v___x_3423_, 0);
v_snd_3425_ = lean_ctor_get(v___x_3423_, 1);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3427_ = v___x_3423_;
v_isShared_3428_ = v_isSharedCheck_3455_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_snd_3425_);
lean_inc(v_fst_3424_);
lean_dec(v___x_3423_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3455_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 1, v_snd_3416_);
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_fst_3424_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_snd_3416_);
v___x_3430_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
lean_object* v___x_3431_; lean_object* v_fst_3432_; lean_object* v_snd_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3453_; 
v___x_3431_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_3401_, v___x_3402_, v_a_3420_, v___x_3430_);
v_fst_3432_ = lean_ctor_get(v___x_3431_, 0);
v_snd_3433_ = lean_ctor_get(v___x_3431_, 1);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3435_ = v___x_3431_;
v_isShared_3436_ = v_isSharedCheck_3453_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_snd_3433_);
lean_inc(v_fst_3432_);
lean_dec(v___x_3431_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3453_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
uint8_t v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3437_ = 2;
v___x_3438_ = lean_box(v___x_3437_);
lean_inc(v_a_3420_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v_a_3420_);
lean_ctor_set(v___x_3435_, 0, v___x_3438_);
v___x_3440_ = v___x_3435_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_a_3420_);
v___x_3440_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3446_; 
v___x_3441_ = lean_array_push(v_fst_3432_, v___x_3440_);
v___x_3442_ = lean_unsigned_to_nat(1u);
v___x_3443_ = lean_nat_add(v_snd_3425_, v___x_3442_);
lean_dec(v_snd_3425_);
v___x_3444_ = lean_nat_add(v_snd_3433_, v___x_3442_);
lean_dec(v_snd_3433_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 1, v___x_3444_);
lean_ctor_set(v___x_3413_, 0, v___x_3443_);
v___x_3446_ = v___x_3413_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; size_t v___x_3448_; size_t v___x_3449_; lean_object* v___x_3450_; 
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3441_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = ((size_t)1ULL);
v___x_3449_ = lean_usize_add(v_i_3407_, v___x_3448_);
v___x_3450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__23(v_original_3403_, v___x_3404_, v_edited_3401_, v___x_3402_, v_as_3405_, v_sz_3406_, v___x_3449_, v___x_3447_);
return v___x_3450_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v_edited_3459_, lean_object* v___x_3460_, lean_object* v_original_3461_, lean_object* v___x_3462_, lean_object* v_as_3463_, lean_object* v_sz_3464_, lean_object* v_i_3465_, lean_object* v_b_3466_){
_start:
{
size_t v_sz_boxed_3467_; size_t v_i_boxed_3468_; lean_object* v_res_3469_; 
v_sz_boxed_3467_ = lean_unbox_usize(v_sz_3464_);
lean_dec(v_sz_3464_);
v_i_boxed_3468_ = lean_unbox_usize(v_i_3465_);
lean_dec(v_i_3465_);
v_res_3469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_3459_, v___x_3460_, v_original_3461_, v___x_3462_, v_as_3463_, v_sz_boxed_3467_, v_i_boxed_3468_, v_b_3466_);
lean_dec_ref(v_as_3463_);
lean_dec(v___x_3462_);
lean_dec_ref(v_original_3461_);
lean_dec(v___x_3460_);
lean_dec_ref(v_edited_3459_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_3470_, lean_object* v_original_3471_, lean_object* v_a_3472_){
_start:
{
lean_object* v_fst_3473_; lean_object* v_snd_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3493_; 
v_fst_3473_ = lean_ctor_get(v_a_3472_, 0);
v_snd_3474_ = lean_ctor_get(v_a_3472_, 1);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_a_3472_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3476_ = v_a_3472_;
v_isShared_3477_ = v_isSharedCheck_3493_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_snd_3474_);
lean_inc(v_fst_3473_);
lean_dec(v_a_3472_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3493_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
uint8_t v___x_3478_; 
v___x_3478_ = lean_nat_dec_lt(v_snd_3474_, v___x_3470_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3480_; 
if (v_isShared_3477_ == 0)
{
v___x_3480_ = v___x_3476_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_fst_3473_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_snd_3474_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
else
{
uint8_t v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3482_ = 1;
v___x_3483_ = lean_array_fget_borrowed(v_original_3471_, v_snd_3474_);
v___x_3484_ = lean_box(v___x_3482_);
lean_inc(v___x_3483_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 1, v___x_3483_);
lean_ctor_set(v___x_3476_, 0, v___x_3484_);
v___x_3486_ = v___x_3476_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v___x_3483_);
v___x_3486_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3487_ = lean_array_push(v_fst_3473_, v___x_3486_);
v___x_3488_ = lean_unsigned_to_nat(1u);
v___x_3489_ = lean_nat_add(v_snd_3474_, v___x_3488_);
lean_dec(v_snd_3474_);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3487_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
v_a_3472_ = v___x_3490_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_3494_, lean_object* v_original_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3494_, v_original_3495_, v_a_3496_);
lean_dec_ref(v_original_3495_);
lean_dec(v___x_3494_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_3498_, size_t v_i_3499_, lean_object* v_bs_3500_){
_start:
{
uint8_t v___x_3501_; 
v___x_3501_ = lean_usize_dec_lt(v_i_3499_, v_sz_3498_);
if (v___x_3501_ == 0)
{
return v_bs_3500_;
}
else
{
lean_object* v_v_3502_; lean_object* v___x_3503_; lean_object* v_bs_x27_3504_; uint8_t v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; size_t v___x_3508_; size_t v___x_3509_; lean_object* v___x_3510_; 
v_v_3502_ = lean_array_uget(v_bs_3500_, v_i_3499_);
v___x_3503_ = lean_unsigned_to_nat(0u);
v_bs_x27_3504_ = lean_array_uset(v_bs_3500_, v_i_3499_, v___x_3503_);
v___x_3505_ = 0;
v___x_3506_ = lean_box(v___x_3505_);
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
lean_ctor_set(v___x_3507_, 1, v_v_3502_);
v___x_3508_ = ((size_t)1ULL);
v___x_3509_ = lean_usize_add(v_i_3499_, v___x_3508_);
v___x_3510_ = lean_array_uset(v_bs_x27_3504_, v_i_3499_, v___x_3507_);
v_i_3499_ = v___x_3509_;
v_bs_3500_ = v___x_3510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_3512_, lean_object* v_i_3513_, lean_object* v_bs_3514_){
_start:
{
size_t v_sz_boxed_3515_; size_t v_i_boxed_3516_; lean_object* v_res_3517_; 
v_sz_boxed_3515_ = lean_unbox_usize(v_sz_3512_);
lean_dec(v_sz_3512_);
v_i_boxed_3516_ = lean_unbox_usize(v_i_3513_);
lean_dec(v_i_3513_);
v_res_3517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_3515_, v_i_boxed_3516_, v_bs_3514_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_3518_, lean_object* v_edited_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_fst_3521_; lean_object* v_snd_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3541_; 
v_fst_3521_ = lean_ctor_get(v_a_3520_, 0);
v_snd_3522_ = lean_ctor_get(v_a_3520_, 1);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_a_3520_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3524_ = v_a_3520_;
v_isShared_3525_ = v_isSharedCheck_3541_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_snd_3522_);
lean_inc(v_fst_3521_);
lean_dec(v_a_3520_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3541_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
uint8_t v___x_3526_; 
v___x_3526_ = lean_nat_dec_lt(v_snd_3522_, v___x_3518_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3528_; 
if (v_isShared_3525_ == 0)
{
v___x_3528_ = v___x_3524_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_fst_3521_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_snd_3522_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
else
{
uint8_t v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3530_ = 0;
v___x_3531_ = lean_array_fget_borrowed(v_edited_3519_, v_snd_3522_);
v___x_3532_ = lean_box(v___x_3530_);
lean_inc(v___x_3531_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v___x_3531_);
lean_ctor_set(v___x_3524_, 0, v___x_3532_);
v___x_3534_ = v___x_3524_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v___x_3531_);
v___x_3534_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3535_ = lean_array_push(v_fst_3521_, v___x_3534_);
v___x_3536_ = lean_unsigned_to_nat(1u);
v___x_3537_ = lean_nat_add(v_snd_3522_, v___x_3536_);
lean_dec(v_snd_3522_);
v___x_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3535_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v_a_3520_ = v___x_3538_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_3542_, lean_object* v_edited_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3542_, v_edited_3543_, v_a_3544_);
lean_dec_ref(v_edited_3543_);
lean_dec(v___x_3542_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3546_, size_t v_i_3547_, lean_object* v_bs_3548_){
_start:
{
uint8_t v___x_3549_; 
v___x_3549_ = lean_usize_dec_lt(v_i_3547_, v_sz_3546_);
if (v___x_3549_ == 0)
{
return v_bs_3548_;
}
else
{
lean_object* v_v_3550_; lean_object* v___x_3551_; lean_object* v_bs_x27_3552_; uint8_t v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; size_t v___x_3556_; size_t v___x_3557_; lean_object* v___x_3558_; 
v_v_3550_ = lean_array_uget(v_bs_3548_, v_i_3547_);
v___x_3551_ = lean_unsigned_to_nat(0u);
v_bs_x27_3552_ = lean_array_uset(v_bs_3548_, v_i_3547_, v___x_3551_);
v___x_3553_ = 1;
v___x_3554_ = lean_box(v___x_3553_);
v___x_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v_v_3550_);
v___x_3556_ = ((size_t)1ULL);
v___x_3557_ = lean_usize_add(v_i_3547_, v___x_3556_);
v___x_3558_ = lean_array_uset(v_bs_x27_3552_, v_i_3547_, v___x_3555_);
v_i_3547_ = v___x_3557_;
v_bs_3548_ = v___x_3558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3560_, lean_object* v_i_3561_, lean_object* v_bs_3562_){
_start:
{
size_t v_sz_boxed_3563_; size_t v_i_boxed_3564_; lean_object* v_res_3565_; 
v_sz_boxed_3563_ = lean_unbox_usize(v_sz_3560_);
lean_dec(v_sz_3560_);
v_i_boxed_3564_ = lean_unbox_usize(v_i_3561_);
lean_dec(v_i_3561_);
v_res_3565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3563_, v_i_boxed_3564_, v_bs_3562_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3573_, lean_object* v_edited_3574_){
_start:
{
lean_object* v_i_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v_i_3575_ = lean_unsigned_to_nat(0u);
v___x_3576_ = lean_array_get_size(v_original_3573_);
v___x_3577_ = lean_nat_dec_lt(v_i_3575_, v___x_3576_);
if (v___x_3577_ == 0)
{
size_t v_sz_3578_; size_t v___x_3579_; lean_object* v___x_3580_; 
lean_dec_ref(v_original_3573_);
v_sz_3578_ = lean_array_size(v_edited_3574_);
v___x_3579_ = ((size_t)0ULL);
v___x_3580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3578_, v___x_3579_, v_edited_3574_);
return v___x_3580_;
}
else
{
lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3581_ = lean_array_get_size(v_edited_3574_);
v___x_3582_ = lean_nat_dec_lt(v_i_3575_, v___x_3581_);
if (v___x_3582_ == 0)
{
size_t v_sz_3583_; size_t v___x_3584_; lean_object* v___x_3585_; 
lean_dec_ref(v_edited_3574_);
v_sz_3583_ = lean_array_size(v_original_3573_);
v___x_3584_ = ((size_t)0ULL);
v___x_3585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3583_, v___x_3584_, v_original_3573_);
return v___x_3585_;
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v_ds_3588_; lean_object* v___x_3589_; size_t v_sz_3590_; size_t v___x_3591_; lean_object* v___x_3592_; lean_object* v_snd_3593_; lean_object* v_fst_3594_; lean_object* v_fst_3595_; lean_object* v_snd_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3615_; 
lean_inc_ref(v_original_3573_);
v___x_3586_ = l_Array_toSubarray___redArg(v_original_3573_, v_i_3575_, v___x_3576_);
lean_inc_ref(v_edited_3574_);
v___x_3587_ = l_Array_toSubarray___redArg(v_edited_3574_, v_i_3575_, v___x_3581_);
v_ds_3588_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3586_, v___x_3587_);
v___x_3589_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3590_ = lean_array_size(v_ds_3588_);
v___x_3591_ = ((size_t)0ULL);
v___x_3592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_3574_, v___x_3581_, v_original_3573_, v___x_3576_, v_ds_3588_, v_sz_3590_, v___x_3591_, v___x_3589_);
lean_dec_ref(v_ds_3588_);
v_snd_3593_ = lean_ctor_get(v___x_3592_, 1);
lean_inc(v_snd_3593_);
v_fst_3594_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_fst_3594_);
lean_dec_ref(v___x_3592_);
v_fst_3595_ = lean_ctor_get(v_snd_3593_, 0);
v_snd_3596_ = lean_ctor_get(v_snd_3593_, 1);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_snd_3593_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3598_ = v_snd_3593_;
v_isShared_3599_ = v_isSharedCheck_3615_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_snd_3596_);
lean_inc(v_fst_3595_);
lean_dec(v_snd_3593_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3615_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 1, v_fst_3595_);
lean_ctor_set(v___x_3598_, 0, v_fst_3594_);
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_fst_3594_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_fst_3595_);
v___x_3601_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3602_; lean_object* v_fst_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3612_; 
v___x_3602_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3576_, v_original_3573_, v___x_3601_);
lean_dec_ref(v_original_3573_);
v_fst_3603_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; 
v_unused_3613_ = lean_ctor_get(v___x_3602_, 1);
lean_dec(v_unused_3613_);
v___x_3605_ = v___x_3602_;
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_fst_3603_);
lean_dec(v___x_3602_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 1, v_snd_3596_);
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_fst_3603_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_snd_3596_);
v___x_3608_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; lean_object* v_fst_3610_; 
v___x_3609_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3581_, v_edited_3574_, v___x_3608_);
lean_dec_ref(v_edited_3574_);
v_fst_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_fst_3610_);
lean_dec_ref(v___x_3609_);
return v_fst_3610_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_3616_, lean_object* v_a_3617_, uint8_t v_b_3618_){
_start:
{
uint8_t v___x_3619_; 
v___x_3619_ = 0;
switch(lean_obj_tag(v_a_3617_))
{
case 0:
{
uint8_t v___x_3620_; 
lean_dec_ref_known(v_a_3617_, 1);
v___x_3620_ = 1;
return v___x_3620_;
}
case 1:
{
lean_object* v_pos_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3634_; 
v_pos_3621_ = lean_ctor_get(v_a_3617_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_a_3617_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3623_ = v_a_3617_;
v_isShared_3624_ = v_isSharedCheck_3634_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_pos_3621_);
lean_dec(v_a_3617_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3634_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v_str_3625_; lean_object* v_startInclusive_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3631_; 
v_str_3625_ = lean_ctor_get(v_s_3616_, 0);
v_startInclusive_3626_ = lean_ctor_get(v_s_3616_, 1);
v___x_3627_ = lean_nat_add(v_startInclusive_3626_, v_pos_3621_);
lean_dec(v_pos_3621_);
v___x_3628_ = lean_string_utf8_next_fast(v_str_3625_, v___x_3627_);
lean_dec(v___x_3627_);
v___x_3629_ = lean_nat_sub(v___x_3628_, v_startInclusive_3626_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set_tag(v___x_3623_, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3629_);
v___x_3631_ = v___x_3623_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3629_);
v___x_3631_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
v_a_3617_ = v___x_3631_;
v_b_3618_ = v___x_3619_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_3635_; lean_object* v_table_3636_; lean_object* v_stackPos_3637_; lean_object* v_needlePos_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3691_; 
v_needle_3635_ = lean_ctor_get(v_a_3617_, 0);
v_table_3636_ = lean_ctor_get(v_a_3617_, 1);
v_stackPos_3637_ = lean_ctor_get(v_a_3617_, 2);
v_needlePos_3638_ = lean_ctor_get(v_a_3617_, 3);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_a_3617_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3640_ = v_a_3617_;
v_isShared_3641_ = v_isSharedCheck_3691_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_needlePos_3638_);
lean_inc(v_stackPos_3637_);
lean_inc(v_table_3636_);
lean_inc(v_needle_3635_);
lean_dec(v_a_3617_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3691_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v_str_3642_; lean_object* v_startInclusive_3643_; lean_object* v_endExclusive_3644_; lean_object* v_str_3645_; lean_object* v_startInclusive_3646_; lean_object* v_endExclusive_3647_; lean_object* v_basePos_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; 
v_str_3642_ = lean_ctor_get(v_needle_3635_, 0);
v_startInclusive_3643_ = lean_ctor_get(v_needle_3635_, 1);
v_endExclusive_3644_ = lean_ctor_get(v_needle_3635_, 2);
v_str_3645_ = lean_ctor_get(v_s_3616_, 0);
v_startInclusive_3646_ = lean_ctor_get(v_s_3616_, 1);
v_endExclusive_3647_ = lean_ctor_get(v_s_3616_, 2);
v_basePos_3648_ = lean_nat_sub(v_stackPos_3637_, v_needlePos_3638_);
v___x_3649_ = lean_nat_sub(v_endExclusive_3644_, v_startInclusive_3643_);
v___x_3650_ = lean_nat_add(v_basePos_3648_, v___x_3649_);
v___x_3651_ = lean_nat_sub(v_endExclusive_3647_, v_startInclusive_3646_);
v___x_3652_ = lean_nat_dec_le(v___x_3650_, v___x_3651_);
lean_dec(v___x_3650_);
if (v___x_3652_ == 0)
{
uint8_t v___x_3653_; 
lean_dec(v___x_3649_);
lean_del_object(v___x_3640_);
lean_dec(v_needlePos_3638_);
lean_dec(v_stackPos_3637_);
lean_dec_ref(v_table_3636_);
lean_dec_ref(v_needle_3635_);
v___x_3653_ = lean_nat_dec_lt(v_basePos_3648_, v___x_3651_);
lean_dec(v___x_3651_);
lean_dec(v_basePos_3648_);
if (v___x_3653_ == 0)
{
return v_b_3618_;
}
else
{
lean_object* v___x_3654_; 
v___x_3654_ = lean_box(3);
v_a_3617_ = v___x_3654_;
v_b_3618_ = v___x_3619_;
goto _start;
}
}
else
{
lean_object* v___x_3656_; uint8_t v_stackByte_3657_; lean_object* v___x_3658_; uint8_t v_patByte_3659_; uint8_t v___x_3660_; 
lean_dec(v___x_3651_);
lean_dec(v_basePos_3648_);
v___x_3656_ = lean_nat_add(v_startInclusive_3646_, v_stackPos_3637_);
v_stackByte_3657_ = lean_string_get_byte_fast(v_str_3645_, v___x_3656_);
v___x_3658_ = lean_nat_add(v_startInclusive_3643_, v_needlePos_3638_);
v_patByte_3659_ = lean_string_get_byte_fast(v_str_3642_, v___x_3658_);
v___x_3660_ = lean_uint8_dec_eq(v_stackByte_3657_, v_patByte_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; uint8_t v___x_3662_; 
lean_dec(v___x_3649_);
v___x_3661_ = lean_unsigned_to_nat(0u);
v___x_3662_ = lean_nat_dec_eq(v_needlePos_3638_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v_newNeedlePos_3665_; uint8_t v___x_3666_; 
v___x_3663_ = lean_unsigned_to_nat(1u);
v___x_3664_ = lean_nat_sub(v_needlePos_3638_, v___x_3663_);
lean_dec(v_needlePos_3638_);
v_newNeedlePos_3665_ = lean_array_fget_borrowed(v_table_3636_, v___x_3664_);
lean_dec(v___x_3664_);
v___x_3666_ = lean_nat_dec_eq(v_newNeedlePos_3665_, v___x_3661_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3668_; 
lean_inc(v_newNeedlePos_3665_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 3, v_newNeedlePos_3665_);
v___x_3668_ = v___x_3640_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_needle_3635_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_table_3636_);
lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_stackPos_3637_);
lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_newNeedlePos_3665_);
v___x_3668_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
v_a_3617_ = v___x_3668_;
v_b_3618_ = v___x_3619_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_3671_; lean_object* v___x_3673_; 
v_nextStackPos_3671_ = l_String_Slice_posGE___redArg(v_s_3616_, v_stackPos_3637_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 3, v___x_3661_);
lean_ctor_set(v___x_3640_, 2, v_nextStackPos_3671_);
v___x_3673_ = v___x_3640_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_needle_3635_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_table_3636_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_nextStackPos_3671_);
lean_ctor_set(v_reuseFailAlloc_3675_, 3, v___x_3661_);
v___x_3673_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
v_a_3617_ = v___x_3673_;
v_b_3618_ = v___x_3619_;
goto _start;
}
}
}
else
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v_nextStackPos_3678_; lean_object* v___x_3680_; 
lean_dec(v_needlePos_3638_);
v___x_3676_ = lean_unsigned_to_nat(1u);
v___x_3677_ = lean_nat_add(v_stackPos_3637_, v___x_3676_);
lean_dec(v_stackPos_3637_);
v_nextStackPos_3678_ = l_String_Slice_posGE___redArg(v_s_3616_, v___x_3677_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 3, v___x_3661_);
lean_ctor_set(v___x_3640_, 2, v_nextStackPos_3678_);
v___x_3680_ = v___x_3640_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_needle_3635_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_table_3636_);
lean_ctor_set(v_reuseFailAlloc_3682_, 2, v_nextStackPos_3678_);
lean_ctor_set(v_reuseFailAlloc_3682_, 3, v___x_3661_);
v___x_3680_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
v_a_3617_ = v___x_3680_;
v_b_3618_ = v___x_3619_;
goto _start;
}
}
}
else
{
lean_object* v___x_3683_; lean_object* v_nextNeedlePos_3684_; uint8_t v___x_3685_; 
v___x_3683_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_3684_ = lean_nat_add(v_needlePos_3638_, v___x_3683_);
lean_dec(v_needlePos_3638_);
v___x_3685_ = lean_nat_dec_eq(v_nextNeedlePos_3684_, v___x_3649_);
lean_dec(v___x_3649_);
if (v___x_3685_ == 0)
{
lean_object* v_nextStackPos_3686_; lean_object* v___x_3688_; 
v_nextStackPos_3686_ = lean_nat_add(v_stackPos_3637_, v___x_3683_);
lean_dec(v_stackPos_3637_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 3, v_nextNeedlePos_3684_);
lean_ctor_set(v___x_3640_, 2, v_nextStackPos_3686_);
v___x_3688_ = v___x_3640_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_needle_3635_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_table_3636_);
lean_ctor_set(v_reuseFailAlloc_3690_, 2, v_nextStackPos_3686_);
lean_ctor_set(v_reuseFailAlloc_3690_, 3, v_nextNeedlePos_3684_);
v___x_3688_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
v_a_3617_ = v___x_3688_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_3684_);
lean_del_object(v___x_3640_);
lean_dec(v_stackPos_3637_);
lean_dec_ref(v_table_3636_);
lean_dec_ref(v_needle_3635_);
return v___x_3685_;
}
}
}
}
}
default: 
{
return v_b_3618_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_3692_, lean_object* v_a_3693_, lean_object* v_b_3694_){
_start:
{
uint8_t v_b_boxed_3695_; uint8_t v_res_3696_; lean_object* v_r_3697_; 
v_b_boxed_3695_ = lean_unbox(v_b_3694_);
v_res_3696_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3692_, v_a_3693_, v_b_boxed_3695_);
lean_dec_ref(v_s_3692_);
v_r_3697_ = lean_box(v_res_3696_);
return v_r_3697_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_3698_, lean_object* v_s_3699_){
_start:
{
lean_object* v___y_3701_; lean_object* v___x_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v___x_3704_ = lean_unsigned_to_nat(0u);
v___x_3705_ = lean_string_utf8_byte_size(v___x_3698_);
v___x_3706_ = lean_nat_dec_eq(v___x_3705_, v___x_3704_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3698_);
lean_ctor_set(v___x_3707_, 1, v___x_3704_);
lean_ctor_set(v___x_3707_, 2, v___x_3705_);
v___x_3708_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_3707_);
v___x_3709_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
lean_ctor_set(v___x_3709_, 2, v___x_3704_);
lean_ctor_set(v___x_3709_, 3, v___x_3704_);
v___y_3701_ = v___x_3709_;
goto v___jp_3700_;
}
else
{
lean_object* v___x_3710_; 
lean_dec_ref(v___x_3698_);
v___x_3710_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_3701_ = v___x_3710_;
goto v___jp_3700_;
}
v___jp_3700_:
{
uint8_t v___x_3702_; uint8_t v___x_3703_; 
v___x_3702_ = 0;
v___x_3703_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3699_, v___y_3701_, v___x_3702_);
return v___x_3703_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_3711_, lean_object* v_s_3712_){
_start:
{
uint8_t v_res_3713_; lean_object* v_r_3714_; 
v_res_3713_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3711_, v_s_3712_);
lean_dec_ref(v_s_3712_);
v_r_3714_ = lean_box(v_res_3713_);
return v_r_3714_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3715_, lean_object* v_x_3716_, lean_object* v_x_3717_){
_start:
{
if (lean_obj_tag(v_x_3716_) == 0)
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = l_List_reverse___redArg(v_x_3717_);
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
return v___x_3720_;
}
else
{
lean_object* v_head_3721_; lean_object* v_tail_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3731_; 
v_head_3721_ = lean_ctor_get(v_x_3716_, 0);
v_tail_3722_ = lean_ctor_get(v_x_3716_, 1);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_x_3716_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3724_ = v_x_3716_;
v_isShared_3725_ = v_isSharedCheck_3731_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_tail_3722_);
lean_inc(v_head_3721_);
lean_dec(v_x_3716_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3731_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3726_; lean_object* v___x_3728_; 
v___x_3726_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3721_, v___y_3715_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 1, v_x_3717_);
lean_ctor_set(v___x_3724_, 0, v___x_3726_);
v___x_3728_ = v___x_3724_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_x_3717_);
v___x_3728_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
v_x_3716_ = v_tail_3722_;
v_x_3717_ = v___x_3728_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3732_, lean_object* v_x_3733_, lean_object* v_x_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3732_, v_x_3733_, v_x_3734_);
lean_dec(v___y_3732_);
return v_res_3736_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1(void){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0));
v___x_3739_ = l_Lean_stringToMessageData(v___x_3738_);
return v___x_3739_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = l_Lean_MessageLog_empty;
v___x_3742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_){
_start:
{
lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; uint8_t v___y_3798_; lean_object* v___y_3862_; lean_object* v___y_3863_; uint8_t v___y_3864_; lean_object* v___y_3865_; uint8_t v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; uint8_t v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v_dc_x3f_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
v___x_4003_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
lean_inc(v_x_3753_);
v___x_4004_ = l_Lean_Syntax_isOfKind(v_x_3753_, v___x_4003_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; 
lean_dec(v_x_3753_);
v___x_4005_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4005_;
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v___x_4006_ = lean_unsigned_to_nat(0u);
v___x_4007_ = l_Lean_Syntax_getArg(v_x_3753_, v___x_4006_);
v___x_4008_ = l_Lean_Syntax_isNone(v___x_4007_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; uint8_t v___x_4010_; 
v___x_4009_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4007_);
v___x_4010_ = l_Lean_Syntax_matchesNull(v___x_4007_, v___x_4009_);
if (v___x_4010_ == 0)
{
lean_object* v___x_4011_; 
lean_dec(v___x_4007_);
lean_dec(v_x_3753_);
v___x_4011_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4011_;
}
else
{
lean_object* v_dc_x3f_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; 
v_dc_x3f_4012_ = l_Lean_Syntax_getArg(v___x_4007_, v___x_4006_);
lean_dec(v___x_4007_);
v___x_4013_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_4012_);
v___x_4014_ = l_Lean_Syntax_isOfKind(v_dc_x3f_4012_, v___x_4013_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; 
lean_dec(v_dc_x3f_4012_);
lean_dec(v_x_3753_);
v___x_4015_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4015_;
}
else
{
lean_object* v___x_4016_; 
v___x_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4016_, 0, v_dc_x3f_4012_);
v_dc_x3f_3984_ = v___x_4016_;
v___y_3985_ = v_a_3754_;
v___y_3986_ = v_a_3755_;
goto v___jp_3983_;
}
}
}
else
{
lean_object* v___x_4017_; 
lean_dec(v___x_4007_);
v___x_4017_ = lean_box(0);
v_dc_x3f_3984_ = v___x_4017_;
v___y_3985_ = v_a_3754_;
v___y_3986_ = v_a_3755_;
goto v___jp_3983_;
}
}
v___jp_3757_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3763_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1);
v___x_3764_ = l_Lean_stringToMessageData(v___y_3762_);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3760_, v___x_3765_, v___y_3759_, v___y_3761_);
lean_dec(v___y_3760_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3787_; 
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3787_ == 0)
{
lean_object* v_unused_3788_; 
v_unused_3788_ = lean_ctor_get(v___x_3766_, 0);
lean_dec(v_unused_3788_);
v___x_3768_ = v___x_3766_;
v_isShared_3769_ = v_isSharedCheck_3787_;
goto v_resetjp_3767_;
}
else
{
lean_dec(v___x_3766_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3787_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Lean_Elab_Command_getRef___redArg(v___y_3759_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3776_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref_known(v___x_3770_, 1);
v___x_3772_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
lean_ctor_set(v___x_3773_, 1, v___y_3758_);
v___x_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3774_, 0, v_a_3771_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set_tag(v___x_3768_, 10);
lean_ctor_set(v___x_3768_, 0, v___x_3774_);
v___x_3776_ = v___x_3768_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3776_, v___y_3759_, v___y_3761_);
return v___x_3777_;
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_del_object(v___x_3768_);
lean_dec_ref(v___y_3758_);
v_a_3779_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3770_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3770_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3758_);
return v___x_3766_;
}
}
v___jp_3789_:
{
if (v___y_3798_ == 0)
{
lean_object* v___x_3799_; lean_object* v_env_3800_; lean_object* v_scopes_3801_; lean_object* v_usedQuotCtxts_3802_; lean_object* v_nextMacroScope_3803_; lean_object* v_maxRecDepth_3804_; lean_object* v_ngen_3805_; lean_object* v_auxDeclNGen_3806_; lean_object* v_infoState_3807_; lean_object* v_traceState_3808_; lean_object* v_snapshotTasks_3809_; lean_object* v_prevLinterStates_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3836_; 
lean_dec(v___y_3796_);
v___x_3799_ = lean_st_ref_take(v___y_3797_);
v_env_3800_ = lean_ctor_get(v___x_3799_, 0);
v_scopes_3801_ = lean_ctor_get(v___x_3799_, 2);
v_usedQuotCtxts_3802_ = lean_ctor_get(v___x_3799_, 3);
v_nextMacroScope_3803_ = lean_ctor_get(v___x_3799_, 4);
v_maxRecDepth_3804_ = lean_ctor_get(v___x_3799_, 5);
v_ngen_3805_ = lean_ctor_get(v___x_3799_, 6);
v_auxDeclNGen_3806_ = lean_ctor_get(v___x_3799_, 7);
v_infoState_3807_ = lean_ctor_get(v___x_3799_, 8);
v_traceState_3808_ = lean_ctor_get(v___x_3799_, 9);
v_snapshotTasks_3809_ = lean_ctor_get(v___x_3799_, 10);
v_prevLinterStates_3810_ = lean_ctor_get(v___x_3799_, 11);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3836_ == 0)
{
lean_object* v_unused_3837_; 
v_unused_3837_ = lean_ctor_get(v___x_3799_, 1);
lean_dec(v_unused_3837_);
v___x_3812_ = v___x_3799_;
v_isShared_3813_ = v_isSharedCheck_3836_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_prevLinterStates_3810_);
lean_inc(v_snapshotTasks_3809_);
lean_inc(v_traceState_3808_);
lean_inc(v_infoState_3807_);
lean_inc(v_auxDeclNGen_3806_);
lean_inc(v_ngen_3805_);
lean_inc(v_maxRecDepth_3804_);
lean_inc(v_nextMacroScope_3803_);
lean_inc(v_usedQuotCtxts_3802_);
lean_inc(v_scopes_3801_);
lean_inc(v_env_3800_);
lean_dec(v___x_3799_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3836_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 1, v___y_3795_);
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_env_3800_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v___y_3795_);
lean_ctor_set(v_reuseFailAlloc_3835_, 2, v_scopes_3801_);
lean_ctor_set(v_reuseFailAlloc_3835_, 3, v_usedQuotCtxts_3802_);
lean_ctor_set(v_reuseFailAlloc_3835_, 4, v_nextMacroScope_3803_);
lean_ctor_set(v_reuseFailAlloc_3835_, 5, v_maxRecDepth_3804_);
lean_ctor_set(v_reuseFailAlloc_3835_, 6, v_ngen_3805_);
lean_ctor_set(v_reuseFailAlloc_3835_, 7, v_auxDeclNGen_3806_);
lean_ctor_set(v_reuseFailAlloc_3835_, 8, v_infoState_3807_);
lean_ctor_set(v_reuseFailAlloc_3835_, 9, v_traceState_3808_);
lean_ctor_set(v_reuseFailAlloc_3835_, 10, v_snapshotTasks_3809_);
lean_ctor_set(v_reuseFailAlloc_3835_, 11, v_prevLinterStates_3810_);
v___x_3815_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v_scopes_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v_opts_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v___x_3816_ = lean_st_ref_put(v___y_3797_, v___x_3815_);
v___x_3817_ = lean_st_ref_get(v___y_3797_);
v_scopes_3818_ = lean_ctor_get(v___x_3817_, 2);
lean_inc(v_scopes_3818_);
lean_dec(v___x_3817_);
v___x_3819_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3820_ = l_List_head_x21___redArg(v___x_3819_, v_scopes_3818_);
lean_dec(v_scopes_3818_);
v_opts_3821_ = lean_ctor_get(v___x_3820_, 1);
lean_inc_ref(v_opts_3821_);
lean_dec(v___x_3820_);
v___x_3822_ = l_Lean_guard__msgs_diff;
v___x_3823_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3821_, v___x_3822_);
lean_dec_ref(v_opts_3821_);
if (v___x_3823_ == 0)
{
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3792_);
lean_inc_ref(v___y_3790_);
v___y_3758_ = v___y_3790_;
v___y_3759_ = v___y_3791_;
v___y_3760_ = v___y_3793_;
v___y_3761_ = v___y_3797_;
v___y_3762_ = v___y_3790_;
goto v___jp_3757_;
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3824_ = lean_string_utf8_byte_size(v___y_3794_);
lean_inc(v___y_3792_);
lean_inc_ref(v___y_3794_);
v___x_3825_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3825_, 0, v___y_3794_);
lean_ctor_set(v___x_3825_, 1, v___y_3792_);
lean_ctor_set(v___x_3825_, 2, v___x_3824_);
v___x_3826_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3825_);
v___x_3827_ = lean_mk_empty_array_with_capacity(v___y_3792_);
lean_inc_ref(v___x_3827_);
v___x_3828_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3794_, v___x_3825_, v___x_3824_, v___x_3826_, v___x_3827_);
lean_dec_ref_known(v___x_3825_, 3);
v___x_3829_ = lean_string_utf8_byte_size(v___y_3790_);
lean_inc_ref_n(v___y_3790_, 2);
v___x_3830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3830_, 0, v___y_3790_);
lean_ctor_set(v___x_3830_, 1, v___y_3792_);
lean_ctor_set(v___x_3830_, 2, v___x_3829_);
v___x_3831_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3830_);
v___x_3832_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3790_, v___x_3830_, v___x_3829_, v___x_3831_, v___x_3827_);
lean_dec_ref_known(v___x_3830_, 3);
v___x_3833_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3828_, v___x_3832_);
v___x_3834_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3833_);
lean_dec_ref(v___x_3833_);
v___y_3758_ = v___y_3790_;
v___y_3759_ = v___y_3791_;
v___y_3760_ = v___y_3793_;
v___y_3761_ = v___y_3797_;
v___y_3762_ = v___x_3834_;
goto v___jp_3757_;
}
}
}
}
else
{
lean_object* v___x_3838_; lean_object* v_env_3839_; lean_object* v_scopes_3840_; lean_object* v_usedQuotCtxts_3841_; lean_object* v_nextMacroScope_3842_; lean_object* v_maxRecDepth_3843_; lean_object* v_ngen_3844_; lean_object* v_auxDeclNGen_3845_; lean_object* v_infoState_3846_; lean_object* v_traceState_3847_; lean_object* v_snapshotTasks_3848_; lean_object* v_prevLinterStates_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3859_; 
lean_dec_ref(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3790_);
v___x_3838_ = lean_st_ref_take(v___y_3797_);
v_env_3839_ = lean_ctor_get(v___x_3838_, 0);
v_scopes_3840_ = lean_ctor_get(v___x_3838_, 2);
v_usedQuotCtxts_3841_ = lean_ctor_get(v___x_3838_, 3);
v_nextMacroScope_3842_ = lean_ctor_get(v___x_3838_, 4);
v_maxRecDepth_3843_ = lean_ctor_get(v___x_3838_, 5);
v_ngen_3844_ = lean_ctor_get(v___x_3838_, 6);
v_auxDeclNGen_3845_ = lean_ctor_get(v___x_3838_, 7);
v_infoState_3846_ = lean_ctor_get(v___x_3838_, 8);
v_traceState_3847_ = lean_ctor_get(v___x_3838_, 9);
v_snapshotTasks_3848_ = lean_ctor_get(v___x_3838_, 10);
v_prevLinterStates_3849_ = lean_ctor_get(v___x_3838_, 11);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3859_ == 0)
{
lean_object* v_unused_3860_; 
v_unused_3860_ = lean_ctor_get(v___x_3838_, 1);
lean_dec(v_unused_3860_);
v___x_3851_ = v___x_3838_;
v_isShared_3852_ = v_isSharedCheck_3859_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_prevLinterStates_3849_);
lean_inc(v_snapshotTasks_3848_);
lean_inc(v_traceState_3847_);
lean_inc(v_infoState_3846_);
lean_inc(v_auxDeclNGen_3845_);
lean_inc(v_ngen_3844_);
lean_inc(v_maxRecDepth_3843_);
lean_inc(v_nextMacroScope_3842_);
lean_inc(v_usedQuotCtxts_3841_);
lean_inc(v_scopes_3840_);
lean_inc(v_env_3839_);
lean_dec(v___x_3838_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3859_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 1, v___y_3796_);
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_env_3839_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v___y_3796_);
lean_ctor_set(v_reuseFailAlloc_3858_, 2, v_scopes_3840_);
lean_ctor_set(v_reuseFailAlloc_3858_, 3, v_usedQuotCtxts_3841_);
lean_ctor_set(v_reuseFailAlloc_3858_, 4, v_nextMacroScope_3842_);
lean_ctor_set(v_reuseFailAlloc_3858_, 5, v_maxRecDepth_3843_);
lean_ctor_set(v_reuseFailAlloc_3858_, 6, v_ngen_3844_);
lean_ctor_set(v_reuseFailAlloc_3858_, 7, v_auxDeclNGen_3845_);
lean_ctor_set(v_reuseFailAlloc_3858_, 8, v_infoState_3846_);
lean_ctor_set(v_reuseFailAlloc_3858_, 9, v_traceState_3847_);
lean_ctor_set(v_reuseFailAlloc_3858_, 10, v_snapshotTasks_3848_);
lean_ctor_set(v_reuseFailAlloc_3858_, 11, v_prevLinterStates_3849_);
v___x_3854_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3855_ = lean_st_ref_put(v___y_3797_, v___x_3854_);
v___x_3856_ = lean_box(0);
v___x_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
return v___x_3857_;
}
}
}
}
v___jp_3861_:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v_a_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v_str_3884_; lean_object* v_startInclusive_3885_; lean_object* v_endExclusive_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3901_; 
v___x_3874_ = l_Lean_MessageLog_toList(v___y_3865_);
lean_dec(v___y_3865_);
v___x_3875_ = lean_box(0);
v___x_3876_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3873_, v___x_3874_, v___x_3875_);
lean_dec(v___y_3873_);
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref(v___x_3876_);
v___x_3878_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3866_, v_a_3877_);
v___x_3879_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3880_ = l_String_intercalate(v___x_3879_, v___x_3878_);
v___x_3881_ = lean_string_utf8_byte_size(v___x_3880_);
lean_inc(v___y_3863_);
v___x_3882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3880_);
lean_ctor_set(v___x_3882_, 1, v___y_3863_);
lean_ctor_set(v___x_3882_, 2, v___x_3881_);
v___x_3883_ = l_String_Slice_trimAscii(v___x_3882_);
v_str_3884_ = lean_ctor_get(v___x_3883_, 0);
v_startInclusive_3885_ = lean_ctor_get(v___x_3883_, 1);
v_endExclusive_3886_ = lean_ctor_get(v___x_3883_, 2);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3888_ = v___x_3883_;
v_isShared_3889_ = v_isSharedCheck_3901_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_endExclusive_3886_);
lean_inc(v_startInclusive_3885_);
lean_inc(v_str_3884_);
lean_dec(v___x_3883_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3901_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_string_utf8_extract_fast(v_str_3884_, v_startInclusive_3885_, v_endExclusive_3886_);
lean_dec(v_endExclusive_3886_);
lean_dec(v_startInclusive_3885_);
lean_dec_ref(v_str_3884_);
if (v___y_3870_ == 0)
{
lean_object* v___x_3891_; lean_object* v___x_3892_; uint8_t v___x_3893_; 
lean_del_object(v___x_3888_);
lean_inc_ref(v___y_3868_);
v___x_3891_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3864_, v___y_3868_);
lean_inc_ref(v___x_3890_);
v___x_3892_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3864_, v___x_3890_);
v___x_3893_ = lean_string_dec_eq(v___x_3891_, v___x_3892_);
lean_dec_ref(v___x_3892_);
lean_dec_ref(v___x_3891_);
v___y_3790_ = v___x_3890_;
v___y_3791_ = v___y_3862_;
v___y_3792_ = v___y_3863_;
v___y_3793_ = v___y_3867_;
v___y_3794_ = v___y_3868_;
v___y_3795_ = v___y_3869_;
v___y_3796_ = v___y_3871_;
v___y_3797_ = v___y_3872_;
v___y_3798_ = v___x_3893_;
goto v___jp_3789_;
}
else
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3898_; 
lean_inc_ref(v___x_3890_);
v___x_3894_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3864_, v___x_3890_);
lean_inc_ref(v___y_3868_);
v___x_3895_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3864_, v___y_3868_);
v___x_3896_ = lean_string_utf8_byte_size(v___x_3894_);
lean_inc(v___y_3863_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 2, v___x_3896_);
lean_ctor_set(v___x_3888_, 1, v___y_3863_);
lean_ctor_set(v___x_3888_, 0, v___x_3894_);
v___x_3898_ = v___x_3888_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v___y_3863_);
lean_ctor_set(v_reuseFailAlloc_3900_, 2, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
uint8_t v___x_3899_; 
v___x_3899_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3895_, v___x_3898_);
lean_dec_ref(v___x_3898_);
v___y_3790_ = v___x_3890_;
v___y_3791_ = v___y_3862_;
v___y_3792_ = v___y_3863_;
v___y_3793_ = v___y_3867_;
v___y_3794_ = v___y_3868_;
v___y_3795_ = v___y_3869_;
v___y_3796_ = v___y_3871_;
v___y_3797_ = v___y_3872_;
v___y_3798_ = v___x_3899_;
goto v___jp_3789_;
}
}
}
}
v___jp_3902_:
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3907_, v___y_3904_, v___y_3906_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v_filterFn_3911_; uint8_t v_whitespace_3912_; uint8_t v_ordering_3913_; uint8_t v_reportPositions_3914_; uint8_t v_substring_3915_; lean_object* v___x_3916_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v_filterFn_3911_ = lean_ctor_get(v_a_3910_, 0);
lean_inc_ref(v_filterFn_3911_);
v_whitespace_3912_ = lean_ctor_get_uint8(v_a_3910_, sizeof(void*)*1);
v_ordering_3913_ = lean_ctor_get_uint8(v_a_3910_, sizeof(void*)*1 + 1);
v_reportPositions_3914_ = lean_ctor_get_uint8(v_a_3910_, sizeof(void*)*1 + 2);
v_substring_3915_ = lean_ctor_get_uint8(v_a_3910_, sizeof(void*)*1 + 3);
lean_dec(v_a_3910_);
v___x_3916_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3903_, v___y_3904_, v___y_3906_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v_a_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v_str_3926_; lean_object* v_startInclusive_3927_; lean_object* v_endExclusive_3928_; lean_object* v_fst_3929_; lean_object* v_snd_3930_; lean_object* v_fileMap_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = l_Lean_MessageLog_toList(v_a_3917_);
v___x_3919_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3920_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3911_, v___x_3918_, v___x_3919_);
lean_dec(v___x_3918_);
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_a_3921_);
lean_dec_ref(v___x_3920_);
v___x_3922_ = lean_unsigned_to_nat(0u);
v___x_3923_ = lean_string_utf8_byte_size(v___y_3908_);
v___x_3924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3924_, 0, v___y_3908_);
lean_ctor_set(v___x_3924_, 1, v___x_3922_);
lean_ctor_set(v___x_3924_, 2, v___x_3923_);
v___x_3925_ = l_String_Slice_trimAscii(v___x_3924_);
v_str_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc_ref(v_str_3926_);
v_startInclusive_3927_ = lean_ctor_get(v___x_3925_, 1);
lean_inc(v_startInclusive_3927_);
v_endExclusive_3928_ = lean_ctor_get(v___x_3925_, 2);
lean_inc(v_endExclusive_3928_);
lean_dec_ref(v___x_3925_);
v_fst_3929_ = lean_ctor_get(v_a_3921_, 0);
lean_inc(v_fst_3929_);
v_snd_3930_ = lean_ctor_get(v_a_3921_, 1);
lean_inc(v_snd_3930_);
lean_dec(v_a_3921_);
v_fileMap_3931_ = lean_ctor_get(v___y_3904_, 1);
v___x_3932_ = lean_string_utf8_extract_fast(v_str_3926_, v_startInclusive_3927_, v_endExclusive_3928_);
lean_dec(v_endExclusive_3928_);
lean_dec(v_startInclusive_3927_);
lean_dec_ref(v_str_3926_);
v___x_3933_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3932_);
if (v_reportPositions_3914_ == 0)
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_box(0);
v___y_3862_ = v___y_3904_;
v___y_3863_ = v___x_3922_;
v___y_3864_ = v_whitespace_3912_;
v___y_3865_ = v_fst_3929_;
v___y_3866_ = v_ordering_3913_;
v___y_3867_ = v___y_3905_;
v___y_3868_ = v___x_3933_;
v___y_3869_ = v_a_3917_;
v___y_3870_ = v_substring_3915_;
v___y_3871_ = v_snd_3930_;
v___y_3872_ = v___y_3906_;
v___y_3873_ = v___x_3934_;
goto v___jp_3861_;
}
else
{
uint8_t v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = 0;
v___x_3936_ = l_Lean_Syntax_getPos_x3f(v___y_3905_, v___x_3935_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v___x_3937_; 
v___x_3937_ = lean_box(0);
v___y_3862_ = v___y_3904_;
v___y_3863_ = v___x_3922_;
v___y_3864_ = v_whitespace_3912_;
v___y_3865_ = v_fst_3929_;
v___y_3866_ = v_ordering_3913_;
v___y_3867_ = v___y_3905_;
v___y_3868_ = v___x_3933_;
v___y_3869_ = v_a_3917_;
v___y_3870_ = v_substring_3915_;
v___y_3871_ = v_snd_3930_;
v___y_3872_ = v___y_3906_;
v___y_3873_ = v___x_3937_;
goto v___jp_3861_;
}
else
{
lean_object* v_val_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3947_; 
v_val_3938_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3940_ = v___x_3936_;
v_isShared_3941_ = v_isSharedCheck_3947_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_val_3938_);
lean_dec(v___x_3936_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3947_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3942_; lean_object* v_line_3943_; lean_object* v___x_3945_; 
lean_inc_ref(v_fileMap_3931_);
v___x_3942_ = l_Lean_FileMap_toPosition(v_fileMap_3931_, v_val_3938_);
lean_dec(v_val_3938_);
v_line_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_line_3943_);
lean_dec_ref(v___x_3942_);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v_line_3943_);
v___x_3945_ = v___x_3940_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_line_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
v___y_3862_ = v___y_3904_;
v___y_3863_ = v___x_3922_;
v___y_3864_ = v_whitespace_3912_;
v___y_3865_ = v_fst_3929_;
v___y_3866_ = v_ordering_3913_;
v___y_3867_ = v___y_3905_;
v___y_3868_ = v___x_3933_;
v___y_3869_ = v_a_3917_;
v___y_3870_ = v_substring_3915_;
v___y_3871_ = v_snd_3930_;
v___y_3872_ = v___y_3906_;
v___y_3873_ = v___x_3945_;
goto v___jp_3861_;
}
}
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_dec_ref(v_filterFn_3911_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3905_);
v_a_3948_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3916_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3916_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3905_);
lean_dec(v___y_3903_);
v_a_3956_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3909_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3909_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
v___jp_3964_:
{
if (lean_obj_tag(v___y_3967_) == 0)
{
lean_object* v___x_3971_; 
v___x_3971_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_3903_ = v___y_3969_;
v___y_3904_ = v___y_3965_;
v___y_3905_ = v___y_3966_;
v___y_3906_ = v___y_3968_;
v___y_3907_ = v___y_3970_;
v___y_3908_ = v___x_3971_;
goto v___jp_3902_;
}
else
{
lean_object* v_val_3972_; lean_object* v___x_3973_; 
v_val_3972_ = lean_ctor_get(v___y_3967_, 0);
lean_inc(v_val_3972_);
lean_dec_ref_known(v___y_3967_, 1);
v___x_3973_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3972_, v___y_3965_, v___y_3968_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_a_3974_);
lean_dec_ref_known(v___x_3973_, 1);
v___y_3903_ = v___y_3969_;
v___y_3904_ = v___y_3965_;
v___y_3905_ = v___y_3966_;
v___y_3906_ = v___y_3968_;
v___y_3907_ = v___y_3970_;
v___y_3908_ = v_a_3974_;
goto v___jp_3902_;
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec(v___y_3966_);
v_a_3975_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3973_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3973_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
v___jp_3983_:
{
lean_object* v___x_3987_; lean_object* v_tk_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3987_ = lean_unsigned_to_nat(1u);
v_tk_3988_ = l_Lean_Syntax_getArg(v_x_3753_, v___x_3987_);
v___x_3989_ = lean_unsigned_to_nat(2u);
v___x_3990_ = l_Lean_Syntax_getArg(v_x_3753_, v___x_3989_);
v___x_3991_ = lean_unsigned_to_nat(4u);
v___x_3992_ = l_Lean_Syntax_getArg(v_x_3753_, v___x_3991_);
lean_dec(v_x_3753_);
v___x_3993_ = l_Lean_Syntax_getOptional_x3f(v___x_3990_);
lean_dec(v___x_3990_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v___x_3994_; 
v___x_3994_ = lean_box(0);
v___y_3965_ = v___y_3985_;
v___y_3966_ = v_tk_3988_;
v___y_3967_ = v_dc_x3f_3984_;
v___y_3968_ = v___y_3986_;
v___y_3969_ = v___x_3992_;
v___y_3970_ = v___x_3994_;
goto v___jp_3964_;
}
else
{
lean_object* v_val_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
v_val_3995_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3993_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_val_3995_);
lean_dec(v___x_3993_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_val_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
v___y_3965_ = v___y_3985_;
v___y_3966_ = v_tk_3988_;
v___y_3967_ = v_dc_x3f_3984_;
v___y_3968_ = v___y_3986_;
v___y_3969_ = v___x_3992_;
v___y_3970_ = v___x_4000_;
goto v___jp_3964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_4018_, v_a_4019_, v_a_4020_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_4023_, lean_object* v_as_4024_, lean_object* v_as_x27_4025_, lean_object* v_b_4026_, lean_object* v_a_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v___x_4031_; 
v___x_4031_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_4023_, v_as_x27_4025_, v_b_4026_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_4032_, lean_object* v_as_4033_, lean_object* v_as_x27_4034_, lean_object* v_b_4035_, lean_object* v_a_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_4032_, v_as_4033_, v_as_x27_4034_, v_b_4035_, v_a_4036_, v___y_4037_, v___y_4038_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v_as_x27_4034_);
lean_dec(v_as_4033_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_4041_, lean_object* v_x_4042_, lean_object* v_x_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_4041_, v_x_4042_, v_x_4043_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_4048_, lean_object* v_x_4049_, lean_object* v_x_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_4048_, v_x_4049_, v_x_4050_, v___y_4051_, v___y_4052_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4048_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_4055_, v___y_4057_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_4060_, v___y_4061_, v___y_4062_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_4065_, lean_object* v___x_4066_, lean_object* v___x_4067_, lean_object* v_inst_4068_, lean_object* v_R_4069_, lean_object* v_a_4070_, lean_object* v_b_4071_){
_start:
{
lean_object* v___x_4072_; 
v___x_4072_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_4065_, v___x_4066_, v___x_4067_, v_a_4070_, v_b_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_4073_, lean_object* v___x_4074_, lean_object* v___x_4075_, lean_object* v_inst_4076_, lean_object* v_R_4077_, lean_object* v_a_4078_, lean_object* v_b_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_4073_, v___x_4074_, v___x_4075_, v_inst_4076_, v_R_4077_, v_a_4078_, v_b_4079_);
lean_dec_ref(v___x_4074_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_4081_, v___y_4083_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_4091_, lean_object* v___x_4092_, lean_object* v___x_4093_, lean_object* v_inst_4094_, lean_object* v_R_4095_, lean_object* v_a_4096_, lean_object* v_b_4097_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_4091_, v___x_4092_, v___x_4093_, v_a_4096_, v_b_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_4099_, lean_object* v___x_4100_, lean_object* v___x_4101_, lean_object* v_inst_4102_, lean_object* v_R_4103_, lean_object* v_a_4104_, lean_object* v_b_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_4099_, v___x_4100_, v___x_4101_, v_inst_4102_, v_R_4103_, v_a_4104_, v_b_4105_);
lean_dec_ref(v___x_4100_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v_original_4107_, lean_object* v___x_4108_, lean_object* v_a_4109_, lean_object* v_inst_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v___x_4112_; 
v___x_4112_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_4107_, v___x_4108_, v_a_4109_, v_a_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v_original_4113_, lean_object* v___x_4114_, lean_object* v_a_4115_, lean_object* v_inst_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_original_4113_, v___x_4114_, v_a_4115_, v_inst_4116_, v_a_4117_);
lean_dec_ref(v_a_4115_);
lean_dec(v___x_4114_);
lean_dec_ref(v_original_4113_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_edited_4119_, lean_object* v___x_4120_, lean_object* v_a_4121_, lean_object* v_inst_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_4119_, v___x_4120_, v_a_4121_, v_a_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object* v_edited_4125_, lean_object* v___x_4126_, lean_object* v_a_4127_, lean_object* v_inst_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_edited_4125_, v___x_4126_, v_a_4127_, v_inst_4128_, v_a_4129_);
lean_dec_ref(v_a_4127_);
lean_dec(v___x_4126_);
lean_dec_ref(v_edited_4125_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_4131_, lean_object* v_original_4132_, lean_object* v_inst_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_4131_, v_original_4132_, v_a_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_4136_, lean_object* v_original_4137_, lean_object* v_inst_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_4136_, v_original_4137_, v_inst_4138_, v_a_4139_);
lean_dec_ref(v_original_4137_);
lean_dec(v___x_4136_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_4141_, lean_object* v_edited_4142_, lean_object* v_inst_4143_, lean_object* v_a_4144_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_4141_, v_edited_4142_, v_a_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_4146_, lean_object* v_edited_4147_, lean_object* v_inst_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_4146_, v_edited_4147_, v_inst_4148_, v_a_4149_);
lean_dec_ref(v_edited_4147_);
lean_dec(v___x_4146_);
return v_res_4150_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_4151_, lean_object* v_inst_4152_, lean_object* v_R_4153_, lean_object* v_a_4154_, uint8_t v_b_4155_, lean_object* v_c_4156_){
_start:
{
uint8_t v___x_4157_; 
v___x_4157_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4151_, v_a_4154_, v_b_4155_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_4158_, lean_object* v_inst_4159_, lean_object* v_R_4160_, lean_object* v_a_4161_, lean_object* v_b_4162_, lean_object* v_c_4163_){
_start:
{
uint8_t v_b_boxed_4164_; uint8_t v_res_4165_; lean_object* v_r_4166_; 
v_b_boxed_4164_ = lean_unbox(v_b_4162_);
v_res_4165_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_4158_, v_inst_4159_, v_R_4160_, v_a_4161_, v_b_boxed_4164_, v_c_4163_);
lean_dec_ref(v_s_4158_);
v_r_4166_ = lean_box(v_res_4165_);
return v_r_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_4167_, lean_object* v_ref_4168_, lean_object* v_msg_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_4168_, v_msg_4169_, v___y_4170_, v___y_4171_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_4174_, lean_object* v_ref_4175_, lean_object* v_msg_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_4174_, v_ref_4175_, v_msg_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v_ref_4175_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(lean_object* v_as_4181_, lean_object* v_as_x27_4182_, lean_object* v_b_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___redArg(v_as_x27_4182_, v_b_4183_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___boxed(lean_object* v_as_4186_, lean_object* v_as_x27_4187_, lean_object* v_b_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_as_4186_, v_as_x27_4187_, v_b_4188_, v_a_4189_);
lean_dec(v_as_x27_4187_);
lean_dec(v_as_4186_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(lean_object* v_lsize_4191_, lean_object* v_rsize_4192_, lean_object* v_histogram_4193_, lean_object* v_index_4194_, lean_object* v_val_4195_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___redArg(v_histogram_4193_, v_index_4194_, v_val_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___boxed(lean_object* v_lsize_4197_, lean_object* v_rsize_4198_, lean_object* v_histogram_4199_, lean_object* v_index_4200_, lean_object* v_val_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_lsize_4197_, v_rsize_4198_, v_histogram_4199_, v_index_4200_, v_val_4201_);
lean_dec(v_rsize_4198_);
lean_dec(v_lsize_4197_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(lean_object* v_upperBound_4203_, lean_object* v___x_4204_, lean_object* v_fst_4205_, lean_object* v___x_4206_, lean_object* v_inst_4207_, lean_object* v_R_4208_, lean_object* v_a_4209_, lean_object* v_b_4210_, lean_object* v_c_4211_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_upperBound_4203_, v___x_4204_, v_fst_4205_, v___x_4206_, v_a_4209_, v_b_4210_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___boxed(lean_object* v_upperBound_4213_, lean_object* v___x_4214_, lean_object* v_fst_4215_, lean_object* v___x_4216_, lean_object* v_inst_4217_, lean_object* v_R_4218_, lean_object* v_a_4219_, lean_object* v_b_4220_, lean_object* v_c_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(v_upperBound_4213_, v___x_4214_, v_fst_4215_, v___x_4216_, v_inst_4217_, v_R_4218_, v_a_4219_, v_b_4220_, v_c_4221_);
lean_dec(v___x_4216_);
lean_dec_ref(v_fst_4215_);
lean_dec(v___x_4214_);
lean_dec(v_upperBound_4213_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(lean_object* v_lsize_4223_, lean_object* v_rsize_4224_, lean_object* v_histogram_4225_, lean_object* v_index_4226_, lean_object* v_val_4227_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_histogram_4225_, v_index_4226_, v_val_4227_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___boxed(lean_object* v_lsize_4229_, lean_object* v_rsize_4230_, lean_object* v_histogram_4231_, lean_object* v_index_4232_, lean_object* v_val_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(v_lsize_4229_, v_rsize_4230_, v_histogram_4231_, v_index_4232_, v_val_4233_);
lean_dec(v_rsize_4230_);
lean_dec(v_lsize_4229_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(lean_object* v_upperBound_4235_, lean_object* v_fst_4236_, lean_object* v___x_4237_, lean_object* v_fst_4238_, lean_object* v_inst_4239_, lean_object* v_R_4240_, lean_object* v_a_4241_, lean_object* v_b_4242_, lean_object* v_c_4243_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_upperBound_4235_, v_fst_4236_, v___x_4237_, v_fst_4238_, v_a_4241_, v_b_4242_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___boxed(lean_object* v_upperBound_4245_, lean_object* v_fst_4246_, lean_object* v___x_4247_, lean_object* v_fst_4248_, lean_object* v_inst_4249_, lean_object* v_R_4250_, lean_object* v_a_4251_, lean_object* v_b_4252_, lean_object* v_c_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(v_upperBound_4245_, v_fst_4246_, v___x_4247_, v_fst_4248_, v_inst_4249_, v_R_4250_, v_a_4251_, v_b_4252_, v_c_4253_);
lean_dec_ref(v_fst_4248_);
lean_dec(v___x_4247_);
lean_dec_ref(v_fst_4246_);
lean_dec(v_upperBound_4245_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34(lean_object* v_00_u03b1_4255_, lean_object* v_msg_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34___redArg(v_msg_4256_, v___y_4257_, v___y_4258_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34___boxed(lean_object* v_00_u03b1_4261_, lean_object* v_msg_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34(v_00_u03b1_4261_, v_msg_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22(lean_object* v_00_u03b2_4267_, lean_object* v_m_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v___x_4270_; 
v___x_4270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22___redArg(v_m_4268_, v_a_4269_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22___boxed(lean_object* v_00_u03b2_4271_, lean_object* v_m_4272_, lean_object* v_a_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22(v_00_u03b2_4271_, v_m_4272_, v_a_4273_);
lean_dec_ref(v_a_4273_);
lean_dec_ref(v_m_4272_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23(lean_object* v_00_u03b2_4275_, lean_object* v_m_4276_, lean_object* v_query_4277_){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___redArg(v_m_4276_, v_query_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23___boxed(lean_object* v_00_u03b2_4279_, lean_object* v_m_4280_, lean_object* v_query_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23(v_00_u03b2_4279_, v_m_4280_, v_query_4281_);
lean_dec_ref(v_query_4281_);
lean_dec_ref(v_m_4280_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24(lean_object* v_00_u03b2_4283_, lean_object* v_m_4284_){
_start:
{
lean_object* v___x_4285_; 
v___x_4285_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___redArg(v_m_4284_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24___boxed(lean_object* v_00_u03b2_4286_, lean_object* v_m_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24(v_00_u03b2_4286_, v_m_4287_);
lean_dec_ref(v_m_4287_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40(lean_object* v_msgData_4289_, lean_object* v_macroStack_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___redArg(v_msgData_4289_, v_macroStack_4290_, v___y_4292_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40___boxed(lean_object* v_msgData_4295_, lean_object* v_macroStack_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__34_spec__40(v_msgData_4295_, v_macroStack_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29(lean_object* v_inst_4301_, lean_object* v_R_4302_, lean_object* v_a_4303_, lean_object* v_b_4304_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v_a_4303_, v_b_4304_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34(lean_object* v_00_u03b2_4306_, lean_object* v_m_4307_, lean_object* v_query_4308_){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34___redArg(v_m_4307_, v_query_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34___boxed(lean_object* v_00_u03b2_4310_, lean_object* v_m_4311_, lean_object* v_query_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__22_spec__34(v_00_u03b2_4310_, v_m_4311_, v_query_4312_);
lean_dec_ref(v_query_4312_);
lean_dec_ref(v_m_4311_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36(lean_object* v_00_u03b2_4314_, lean_object* v_m_4315_, lean_object* v_query_4316_, lean_object* v_x_4317_, lean_object* v_x_4318_, lean_object* v_x_4319_, lean_object* v_x_4320_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36___redArg(v_m_4315_, v_query_4316_, v_x_4317_, v_x_4318_, v_x_4319_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36___boxed(lean_object* v_00_u03b2_4322_, lean_object* v_m_4323_, lean_object* v_query_4324_, lean_object* v_x_4325_, lean_object* v_x_4326_, lean_object* v_x_4327_, lean_object* v_x_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__23_spec__36(v_00_u03b2_4322_, v_m_4323_, v_query_4324_, v_x_4325_, v_x_4326_, v_x_4327_, v_x_4328_);
lean_dec_ref(v_query_4324_);
lean_dec_ref(v_m_4323_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38(lean_object* v_00_u03b2_4330_, lean_object* v_init_4331_, lean_object* v_b_4332_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38___redArg(v_init_4331_, v_b_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38___boxed(lean_object* v_00_u03b2_4334_, lean_object* v_init_4335_, lean_object* v_b_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38(v_00_u03b2_4334_, v_init_4335_, v_b_4336_);
lean_dec_ref(v_b_4336_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44(lean_object* v_00_u03b2_4338_, lean_object* v_b_4339_, lean_object* v_acc_4340_, lean_object* v_i_4341_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44___redArg(v_b_4339_, v_acc_4340_, v_i_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44___boxed(lean_object* v_00_u03b2_4343_, lean_object* v_b_4344_, lean_object* v_acc_4345_, lean_object* v_i_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16_spec__24_spec__38_spec__44(v_00_u03b2_4343_, v_b_4344_, v_acc_4345_, v_i_4346_);
lean_dec_ref(v_b_4344_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4356_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4357_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
v___x_4358_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4359_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4360_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4356_, v___x_4357_, v___x_4358_, v___x_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4389_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4390_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4391_ = l_Lean_addBuiltinDeclarationRanges(v___x_4389_, v___x_4390_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4394_){
_start:
{
lean_object* v_doc_4396_; lean_object* v___x_4397_; 
v_doc_4396_ = lean_ctor_get(v___y_4394_, 1);
lean_inc_ref(v_doc_4396_);
v___x_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4397_, 0, v_doc_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4398_);
lean_dec_ref(v___y_4398_);
return v_res_4400_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4401_, lean_object* v_a_4402_, uint8_t v_b_4403_){
_start:
{
lean_object* v_str_4404_; lean_object* v_startInclusive_4405_; lean_object* v_endExclusive_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v_str_4404_ = lean_ctor_get(v_s_4401_, 0);
v_startInclusive_4405_ = lean_ctor_get(v_s_4401_, 1);
v_endExclusive_4406_ = lean_ctor_get(v_s_4401_, 2);
v___x_4407_ = lean_nat_sub(v_endExclusive_4406_, v_startInclusive_4405_);
v___x_4408_ = lean_nat_dec_eq(v_a_4402_, v___x_4407_);
lean_dec(v___x_4407_);
if (v___x_4408_ == 0)
{
lean_object* v___x_4409_; uint32_t v___x_4410_; uint32_t v___x_4411_; uint8_t v___x_4412_; 
v___x_4409_ = lean_nat_add(v_startInclusive_4405_, v_a_4402_);
lean_dec(v_a_4402_);
v___x_4410_ = lean_string_utf8_get_fast(v_str_4404_, v___x_4409_);
v___x_4411_ = 10;
v___x_4412_ = lean_uint32_dec_eq(v___x_4410_, v___x_4411_);
if (v___x_4412_ == 0)
{
lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4413_ = lean_string_utf8_next_fast(v_str_4404_, v___x_4409_);
lean_dec(v___x_4409_);
v___x_4414_ = lean_nat_sub(v___x_4413_, v_startInclusive_4405_);
v_a_4402_ = v___x_4414_;
v_b_4403_ = v___x_4412_;
goto _start;
}
else
{
lean_dec(v___x_4409_);
return v___x_4412_;
}
}
else
{
lean_dec(v_a_4402_);
return v_b_4403_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4416_, lean_object* v_a_4417_, lean_object* v_b_4418_){
_start:
{
uint8_t v_b_boxed_4419_; uint8_t v_res_4420_; lean_object* v_r_4421_; 
v_b_boxed_4419_ = lean_unbox(v_b_4418_);
v_res_4420_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4416_, v_a_4417_, v_b_boxed_4419_);
lean_dec_ref(v_s_4416_);
v_r_4421_ = lean_box(v_res_4420_);
return v_r_4421_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4422_){
_start:
{
lean_object* v_searcher_4423_; uint8_t v___x_4424_; uint8_t v___x_4425_; 
v_searcher_4423_ = lean_unsigned_to_nat(0u);
v___x_4424_ = 0;
v___x_4425_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4422_, v_searcher_4423_, v___x_4424_);
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4426_){
_start:
{
uint8_t v_res_4427_; lean_object* v_r_4428_; 
v_res_4427_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4426_);
lean_dec_ref(v_s_4426_);
v_r_4428_ = lean_box(v_res_4427_);
return v_r_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4440_, lean_object* v_fst_4441_, uint8_t v___x_4442_, lean_object* v_a_4443_, lean_object* v___x_4444_, lean_object* v___x_4445_, lean_object* v___x_4446_, lean_object* v___x_4447_, lean_object* v___x_4448_, lean_object* v___x_4449_, lean_object* v___x_4450_, lean_object* v___x_4451_, lean_object* v_snd_4452_, lean_object* v___x_4453_){
_start:
{
if (lean_obj_tag(v___x_4440_) == 1)
{
lean_object* v_val_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4518_; 
v_val_4455_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4457_ = v___x_4440_;
v_isShared_4458_ = v_isSharedCheck_4518_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_val_4455_);
lean_dec(v___x_4440_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4518_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4459_ = lean_unsigned_to_nat(0u);
v___x_4460_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4461_ = l_Lean_Syntax_setArg(v_fst_4441_, v___x_4459_, v___x_4460_);
v___x_4462_ = l_Lean_Syntax_getPos_x3f(v___x_4461_, v___x_4442_);
lean_dec(v___x_4461_);
if (lean_obj_tag(v___x_4462_) == 1)
{
lean_object* v_val_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4514_; 
lean_dec_ref(v___x_4453_);
v_val_4463_ = lean_ctor_get(v___x_4462_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4462_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4465_ = v___x_4462_;
v_isShared_4466_ = v_isSharedCheck_4514_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_val_4463_);
lean_dec(v___x_4462_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4514_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___y_4468_; lean_object* v___x_4494_; uint8_t v___y_4501_; lean_object* v___x_4506_; uint8_t v___x_4507_; 
v___x_4494_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4452_);
v___x_4506_ = lean_string_utf8_byte_size(v___x_4494_);
v___x_4507_ = lean_nat_dec_eq(v___x_4506_, v___x_4459_);
if (v___x_4507_ == 0)
{
lean_object* v___x_4508_; lean_object* v___x_4509_; uint8_t v___x_4510_; 
v___x_4508_ = lean_string_length(v___x_4494_);
v___x_4509_ = lean_unsigned_to_nat(93u);
v___x_4510_ = lean_nat_dec_le(v___x_4508_, v___x_4509_);
if (v___x_4510_ == 0)
{
v___y_4501_ = v___x_4510_;
goto v___jp_4500_;
}
else
{
lean_object* v___x_4511_; uint8_t v___x_4512_; 
lean_inc_ref(v___x_4494_);
v___x_4511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4494_);
lean_ctor_set(v___x_4511_, 1, v___x_4459_);
lean_ctor_set(v___x_4511_, 2, v___x_4506_);
v___x_4512_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4511_);
lean_dec_ref_known(v___x_4511_, 3);
if (v___x_4512_ == 0)
{
v___y_4501_ = v___x_4510_;
goto v___jp_4500_;
}
else
{
goto v___jp_4495_;
}
}
}
else
{
lean_object* v___x_4513_; 
lean_dec_ref(v___x_4494_);
v___x_4513_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_4468_ = v___x_4513_;
goto v___jp_4467_;
}
v___jp_4467_:
{
lean_object* v_toEditableDocumentCore_4469_; lean_object* v_meta_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4490_; 
v_toEditableDocumentCore_4469_ = lean_ctor_get(v_a_4443_, 0);
lean_inc_ref(v_toEditableDocumentCore_4469_);
v_meta_4470_ = lean_ctor_get(v_toEditableDocumentCore_4469_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v_toEditableDocumentCore_4469_);
if (v_isSharedCheck_4490_ == 0)
{
lean_object* v_unused_4491_; lean_object* v_unused_4492_; lean_object* v_unused_4493_; 
v_unused_4491_ = lean_ctor_get(v_toEditableDocumentCore_4469_, 3);
lean_dec(v_unused_4491_);
v_unused_4492_ = lean_ctor_get(v_toEditableDocumentCore_4469_, 2);
lean_dec(v_unused_4492_);
v_unused_4493_ = lean_ctor_get(v_toEditableDocumentCore_4469_, 1);
lean_dec(v_unused_4493_);
v___x_4472_ = v_toEditableDocumentCore_4469_;
v_isShared_4473_ = v_isSharedCheck_4490_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_meta_4470_);
lean_dec(v_toEditableDocumentCore_4469_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4490_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v_text_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4480_; 
v_text_4474_ = lean_ctor_get(v_meta_4470_, 3);
lean_inc_ref(v_text_4474_);
lean_dec_ref(v_meta_4470_);
v___x_4475_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4443_);
v___x_4476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4476_, 0, v_val_4455_);
lean_ctor_set(v___x_4476_, 1, v_val_4463_);
v___x_4477_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4474_, v___x_4476_);
v___x_4478_ = lean_box(0);
lean_inc(v___x_4444_);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 3, v___x_4444_);
lean_ctor_set(v___x_4472_, 2, v___x_4478_);
lean_ctor_set(v___x_4472_, 1, v___y_4468_);
lean_ctor_set(v___x_4472_, 0, v___x_4477_);
v___x_4480_ = v___x_4472_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4477_);
lean_ctor_set(v_reuseFailAlloc_4489_, 1, v___y_4468_);
lean_ctor_set(v_reuseFailAlloc_4489_, 2, v___x_4478_);
lean_ctor_set(v_reuseFailAlloc_4489_, 3, v___x_4444_);
v___x_4480_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
lean_object* v___x_4481_; lean_object* v___x_4483_; 
v___x_4481_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4475_, v___x_4480_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 0, v___x_4481_);
v___x_4483_ = v___x_4465_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4481_);
v___x_4483_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
lean_inc(v___x_4444_);
v___x_4484_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4444_);
lean_ctor_set(v___x_4484_, 1, v___x_4444_);
lean_ctor_set(v___x_4484_, 2, v___x_4445_);
lean_ctor_set(v___x_4484_, 3, v___x_4446_);
lean_ctor_set(v___x_4484_, 4, v___x_4447_);
lean_ctor_set(v___x_4484_, 5, v___x_4448_);
lean_ctor_set(v___x_4484_, 6, v___x_4449_);
lean_ctor_set(v___x_4484_, 7, v___x_4483_);
lean_ctor_set(v___x_4484_, 8, v___x_4450_);
lean_ctor_set(v___x_4484_, 9, v___x_4451_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set_tag(v___x_4457_, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4484_);
v___x_4486_ = v___x_4457_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4484_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
}
v___jp_4495_:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4496_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4497_ = lean_string_append(v___x_4496_, v___x_4494_);
lean_dec_ref(v___x_4494_);
v___x_4498_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4499_ = lean_string_append(v___x_4497_, v___x_4498_);
v___y_4468_ = v___x_4499_;
goto v___jp_4467_;
}
v___jp_4500_:
{
if (v___y_4501_ == 0)
{
goto v___jp_4495_;
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4502_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4503_ = lean_string_append(v___x_4502_, v___x_4494_);
lean_dec_ref(v___x_4494_);
v___x_4504_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4505_ = lean_string_append(v___x_4503_, v___x_4504_);
v___y_4468_ = v___x_4505_;
goto v___jp_4467_;
}
}
}
}
else
{
lean_object* v___x_4516_; 
lean_dec(v___x_4462_);
lean_dec(v_val_4455_);
lean_dec_ref(v_snd_4452_);
lean_dec(v___x_4451_);
lean_dec(v___x_4450_);
lean_dec(v___x_4449_);
lean_dec(v___x_4448_);
lean_dec(v___x_4447_);
lean_dec(v___x_4446_);
lean_dec_ref(v___x_4445_);
lean_dec(v___x_4444_);
lean_dec_ref(v_a_4443_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set_tag(v___x_4457_, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4453_);
v___x_4516_ = v___x_4457_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4453_);
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
else
{
lean_object* v___x_4519_; 
lean_dec_ref(v_snd_4452_);
lean_dec(v___x_4451_);
lean_dec(v___x_4450_);
lean_dec(v___x_4449_);
lean_dec(v___x_4448_);
lean_dec(v___x_4447_);
lean_dec(v___x_4446_);
lean_dec_ref(v___x_4445_);
lean_dec(v___x_4444_);
lean_dec_ref(v_a_4443_);
lean_dec(v_fst_4441_);
lean_dec(v___x_4440_);
v___x_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4453_);
return v___x_4519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4520_, lean_object* v_fst_4521_, lean_object* v___x_4522_, lean_object* v_a_4523_, lean_object* v___x_4524_, lean_object* v___x_4525_, lean_object* v___x_4526_, lean_object* v___x_4527_, lean_object* v___x_4528_, lean_object* v___x_4529_, lean_object* v___x_4530_, lean_object* v___x_4531_, lean_object* v_snd_4532_, lean_object* v___x_4533_, lean_object* v___y_4534_){
_start:
{
uint8_t v___x_4549__boxed_4535_; lean_object* v_res_4536_; 
v___x_4549__boxed_4535_ = lean_unbox(v___x_4522_);
v_res_4536_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4520_, v_fst_4521_, v___x_4549__boxed_4535_, v_a_4523_, v___x_4524_, v___x_4525_, v___x_4526_, v___x_4527_, v___x_4528_, v___x_4529_, v___x_4530_, v___x_4531_, v_snd_4532_, v___x_4533_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4540_, size_t v_sz_4541_, size_t v_i_4542_, lean_object* v_b_4543_){
_start:
{
lean_object* v_a_4545_; uint8_t v___x_4549_; 
v___x_4549_ = lean_usize_dec_lt(v_i_4542_, v_sz_4541_);
if (v___x_4549_ == 0)
{
lean_inc_ref(v_b_4543_);
return v_b_4543_;
}
else
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v_a_4552_; 
v___x_4550_ = lean_box(0);
v___x_4551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4552_ = lean_array_uget(v_as_4540_, v_i_4542_);
if (lean_obj_tag(v_a_4552_) == 1)
{
lean_object* v_i_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4587_; 
v_i_4553_ = lean_ctor_get(v_a_4552_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_a_4552_);
if (v_isSharedCheck_4587_ == 0)
{
lean_object* v_unused_4588_; 
v_unused_4588_ = lean_ctor_get(v_a_4552_, 1);
lean_dec(v_unused_4588_);
v___x_4555_ = v_a_4552_;
v_isShared_4556_ = v_isSharedCheck_4587_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_i_4553_);
lean_dec(v_a_4552_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4587_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
if (lean_obj_tag(v_i_4553_) == 10)
{
lean_object* v_i_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4586_; 
v_i_4557_ = lean_ctor_get(v_i_4553_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v_i_4553_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4559_ = v_i_4553_;
v_isShared_4560_ = v_isSharedCheck_4586_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_i_4557_);
lean_dec(v_i_4553_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4586_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v_stx_4561_; lean_object* v_value_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4585_; 
v_stx_4561_ = lean_ctor_get(v_i_4557_, 0);
v_value_4562_ = lean_ctor_get(v_i_4557_, 1);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_i_4557_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4564_ = v_i_4557_;
v_isShared_4565_ = v_isSharedCheck_4585_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_value_4562_);
lean_inc(v_stx_4561_);
lean_dec(v_i_4557_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4585_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4566_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4567_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4562_, v___x_4566_);
lean_dec(v_value_4562_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_del_object(v___x_4564_);
lean_dec(v_stx_4561_);
lean_del_object(v___x_4559_);
lean_del_object(v___x_4555_);
v_a_4545_ = v___x_4551_;
goto v___jp_4544_;
}
else
{
lean_object* v_val_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4584_; 
v_val_4568_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4570_ = v___x_4567_;
v_isShared_4571_ = v_isSharedCheck_4584_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_val_4568_);
lean_dec(v___x_4567_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4584_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 1, v_val_4568_);
v___x_4573_ = v___x_4564_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_stx_4561_);
lean_ctor_set(v_reuseFailAlloc_4583_, 1, v_val_4568_);
v___x_4573_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
lean_object* v___x_4575_; 
if (v_isShared_4571_ == 0)
{
lean_ctor_set(v___x_4570_, 0, v___x_4573_);
v___x_4575_ = v___x_4570_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4573_);
v___x_4575_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
lean_object* v___x_4577_; 
if (v_isShared_4560_ == 0)
{
lean_ctor_set_tag(v___x_4559_, 1);
lean_ctor_set(v___x_4559_, 0, v___x_4575_);
v___x_4577_ = v___x_4559_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4575_);
v___x_4577_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
lean_object* v___x_4579_; 
if (v_isShared_4556_ == 0)
{
lean_ctor_set_tag(v___x_4555_, 0);
lean_ctor_set(v___x_4555_, 1, v___x_4550_);
lean_ctor_set(v___x_4555_, 0, v___x_4577_);
v___x_4579_ = v___x_4555_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v___x_4577_);
lean_ctor_set(v_reuseFailAlloc_4580_, 1, v___x_4550_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
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
lean_del_object(v___x_4555_);
lean_dec_ref(v_i_4553_);
v_a_4545_ = v___x_4551_;
goto v___jp_4544_;
}
}
}
else
{
lean_dec(v_a_4552_);
v_a_4545_ = v___x_4551_;
goto v___jp_4544_;
}
}
v___jp_4544_:
{
size_t v___x_4546_; size_t v___x_4547_; 
v___x_4546_ = ((size_t)1ULL);
v___x_4547_ = lean_usize_add(v_i_4542_, v___x_4546_);
v_i_4542_ = v___x_4547_;
v_b_4543_ = v_a_4545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4589_, lean_object* v_sz_4590_, lean_object* v_i_4591_, lean_object* v_b_4592_){
_start:
{
size_t v_sz_boxed_4593_; size_t v_i_boxed_4594_; lean_object* v_res_4595_; 
v_sz_boxed_4593_ = lean_unbox_usize(v_sz_4590_);
lean_dec(v_sz_4590_);
v_i_boxed_4594_ = lean_unbox_usize(v_i_4591_);
lean_dec(v_i_4591_);
v_res_4595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4589_, v_sz_boxed_4593_, v_i_boxed_4594_, v_b_4592_);
lean_dec_ref(v_b_4592_);
lean_dec_ref(v_as_4589_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4596_, size_t v_sz_4597_, size_t v_i_4598_, lean_object* v_b_4599_){
_start:
{
lean_object* v_a_4601_; uint8_t v___x_4605_; 
v___x_4605_ = lean_usize_dec_lt(v_i_4598_, v_sz_4597_);
if (v___x_4605_ == 0)
{
lean_inc_ref(v_b_4599_);
return v_b_4599_;
}
else
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v_a_4608_; 
v___x_4606_ = lean_box(0);
v___x_4607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4608_ = lean_array_uget(v_as_4596_, v_i_4598_);
if (lean_obj_tag(v_a_4608_) == 1)
{
lean_object* v_i_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4643_; 
v_i_4609_ = lean_ctor_get(v_a_4608_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v_a_4608_);
if (v_isSharedCheck_4643_ == 0)
{
lean_object* v_unused_4644_; 
v_unused_4644_ = lean_ctor_get(v_a_4608_, 1);
lean_dec(v_unused_4644_);
v___x_4611_ = v_a_4608_;
v_isShared_4612_ = v_isSharedCheck_4643_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_i_4609_);
lean_dec(v_a_4608_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4643_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
if (lean_obj_tag(v_i_4609_) == 10)
{
lean_object* v_i_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4642_; 
v_i_4613_ = lean_ctor_get(v_i_4609_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v_i_4609_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4615_ = v_i_4609_;
v_isShared_4616_ = v_isSharedCheck_4642_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_i_4613_);
lean_dec(v_i_4609_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4642_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v_stx_4617_; lean_object* v_value_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4641_; 
v_stx_4617_ = lean_ctor_get(v_i_4613_, 0);
v_value_4618_ = lean_ctor_get(v_i_4613_, 1);
v_isSharedCheck_4641_ = !lean_is_exclusive(v_i_4613_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4620_ = v_i_4613_;
v_isShared_4621_ = v_isSharedCheck_4641_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_value_4618_);
lean_inc(v_stx_4617_);
lean_dec(v_i_4613_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4641_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4623_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4618_, v___x_4622_);
lean_dec(v_value_4618_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_del_object(v___x_4620_);
lean_dec(v_stx_4617_);
lean_del_object(v___x_4615_);
lean_del_object(v___x_4611_);
v_a_4601_ = v___x_4607_;
goto v___jp_4600_;
}
else
{
lean_object* v_val_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4640_; 
v_val_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4640_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_val_4624_);
lean_dec(v___x_4623_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4640_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 1, v_val_4624_);
v___x_4629_ = v___x_4620_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_stx_4617_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_val_4624_);
v___x_4629_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
lean_object* v___x_4631_; 
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v___x_4629_);
v___x_4631_ = v___x_4626_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4629_);
v___x_4631_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4633_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set_tag(v___x_4615_, 1);
lean_ctor_set(v___x_4615_, 0, v___x_4631_);
v___x_4633_ = v___x_4615_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4631_);
v___x_4633_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
lean_object* v___x_4635_; 
if (v_isShared_4612_ == 0)
{
lean_ctor_set_tag(v___x_4611_, 0);
lean_ctor_set(v___x_4611_, 1, v___x_4606_);
lean_ctor_set(v___x_4611_, 0, v___x_4633_);
v___x_4635_ = v___x_4611_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v___x_4606_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
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
lean_del_object(v___x_4611_);
lean_dec_ref(v_i_4609_);
v_a_4601_ = v___x_4607_;
goto v___jp_4600_;
}
}
}
else
{
lean_dec(v_a_4608_);
v_a_4601_ = v___x_4607_;
goto v___jp_4600_;
}
}
v___jp_4600_:
{
size_t v___x_4602_; size_t v___x_4603_; lean_object* v___x_4604_; 
v___x_4602_ = ((size_t)1ULL);
v___x_4603_ = lean_usize_add(v_i_4598_, v___x_4602_);
v___x_4604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4596_, v_sz_4597_, v___x_4603_, v_a_4601_);
return v___x_4604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4645_, lean_object* v_sz_4646_, lean_object* v_i_4647_, lean_object* v_b_4648_){
_start:
{
size_t v_sz_boxed_4649_; size_t v_i_boxed_4650_; lean_object* v_res_4651_; 
v_sz_boxed_4649_ = lean_unbox_usize(v_sz_4646_);
lean_dec(v_sz_4646_);
v_i_boxed_4650_ = lean_unbox_usize(v_i_4647_);
lean_dec(v_i_4647_);
v_res_4651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4645_, v_sz_boxed_4649_, v_i_boxed_4650_, v_b_4648_);
lean_dec_ref(v_b_4648_);
lean_dec_ref(v_as_4645_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4652_){
_start:
{
if (lean_obj_tag(v_x_4652_) == 0)
{
lean_object* v_cs_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; size_t v_sz_4656_; size_t v___x_4657_; lean_object* v___x_4658_; lean_object* v_fst_4659_; 
v_cs_4653_ = lean_ctor_get(v_x_4652_, 0);
v___x_4654_ = lean_box(0);
v___x_4655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4656_ = lean_array_size(v_cs_4653_);
v___x_4657_ = ((size_t)0ULL);
v___x_4658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4653_, v_sz_4656_, v___x_4657_, v___x_4655_);
v_fst_4659_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_fst_4659_);
lean_dec_ref(v___x_4658_);
if (lean_obj_tag(v_fst_4659_) == 0)
{
return v___x_4654_;
}
else
{
lean_object* v_val_4660_; 
v_val_4660_ = lean_ctor_get(v_fst_4659_, 0);
lean_inc(v_val_4660_);
lean_dec_ref_known(v_fst_4659_, 1);
return v_val_4660_;
}
}
else
{
lean_object* v_vs_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; size_t v_sz_4664_; size_t v___x_4665_; lean_object* v___x_4666_; lean_object* v_fst_4667_; 
v_vs_4661_ = lean_ctor_get(v_x_4652_, 0);
v___x_4662_ = lean_box(0);
v___x_4663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4664_ = lean_array_size(v_vs_4661_);
v___x_4665_ = ((size_t)0ULL);
v___x_4666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4661_, v_sz_4664_, v___x_4665_, v___x_4663_);
v_fst_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc(v_fst_4667_);
lean_dec_ref(v___x_4666_);
if (lean_obj_tag(v_fst_4667_) == 0)
{
return v___x_4662_;
}
else
{
lean_object* v_val_4668_; 
v_val_4668_ = lean_ctor_get(v_fst_4667_, 0);
lean_inc(v_val_4668_);
lean_dec_ref_known(v_fst_4667_, 1);
return v_val_4668_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4669_, size_t v_sz_4670_, size_t v_i_4671_, lean_object* v_b_4672_){
_start:
{
uint8_t v___x_4673_; 
v___x_4673_ = lean_usize_dec_lt(v_i_4671_, v_sz_4670_);
if (v___x_4673_ == 0)
{
lean_inc_ref(v_b_4672_);
return v_b_4672_;
}
else
{
lean_object* v___x_4674_; lean_object* v_a_4675_; lean_object* v___x_4676_; 
v___x_4674_ = lean_box(0);
v_a_4675_ = lean_array_uget_borrowed(v_as_4669_, v_i_4671_);
v___x_4676_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4675_);
if (lean_obj_tag(v___x_4676_) == 1)
{
lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4676_);
v___x_4678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
lean_ctor_set(v___x_4678_, 1, v___x_4674_);
return v___x_4678_;
}
else
{
lean_object* v___x_4679_; size_t v___x_4680_; size_t v___x_4681_; 
lean_dec(v___x_4676_);
v___x_4679_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4680_ = ((size_t)1ULL);
v___x_4681_ = lean_usize_add(v_i_4671_, v___x_4680_);
v_i_4671_ = v___x_4681_;
v_b_4672_ = v___x_4679_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4683_, lean_object* v_sz_4684_, lean_object* v_i_4685_, lean_object* v_b_4686_){
_start:
{
size_t v_sz_boxed_4687_; size_t v_i_boxed_4688_; lean_object* v_res_4689_; 
v_sz_boxed_4687_ = lean_unbox_usize(v_sz_4684_);
lean_dec(v_sz_4684_);
v_i_boxed_4688_ = lean_unbox_usize(v_i_4685_);
lean_dec(v_i_4685_);
v_res_4689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4683_, v_sz_boxed_4687_, v_i_boxed_4688_, v_b_4686_);
lean_dec_ref(v_b_4686_);
lean_dec_ref(v_as_4683_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4690_);
lean_dec_ref(v_x_4690_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4692_){
_start:
{
lean_object* v_root_4693_; lean_object* v_tail_4694_; lean_object* v___x_4695_; 
v_root_4693_ = lean_ctor_get(v_t_4692_, 0);
v_tail_4694_ = lean_ctor_get(v_t_4692_, 1);
v___x_4695_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4693_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v___x_4696_; size_t v_sz_4697_; size_t v___x_4698_; lean_object* v___x_4699_; lean_object* v_fst_4700_; 
v___x_4696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4697_ = lean_array_size(v_tail_4694_);
v___x_4698_ = ((size_t)0ULL);
v___x_4699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4694_, v_sz_4697_, v___x_4698_, v___x_4696_);
v_fst_4700_ = lean_ctor_get(v___x_4699_, 0);
lean_inc(v_fst_4700_);
lean_dec_ref(v___x_4699_);
if (lean_obj_tag(v_fst_4700_) == 0)
{
return v___x_4695_;
}
else
{
lean_object* v_val_4701_; 
v_val_4701_ = lean_ctor_get(v_fst_4700_, 0);
lean_inc(v_val_4701_);
lean_dec_ref_known(v_fst_4700_, 1);
return v_val_4701_;
}
}
else
{
return v___x_4695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4702_){
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4702_);
lean_dec_ref(v_t_4702_);
return v_res_4703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4718_, lean_object* v_a_4719_){
_start:
{
if (lean_obj_tag(v_node_4718_) == 1)
{
lean_object* v_children_4721_; lean_object* v_res_4722_; 
v_children_4721_ = lean_ctor_get(v_node_4718_, 1);
v_res_4722_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4721_);
if (lean_obj_tag(v_res_4722_) == 1)
{
lean_object* v_val_4723_; lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4760_; 
v_val_4723_ = lean_ctor_get(v_res_4722_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v_res_4722_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4725_ = v_res_4722_;
v_isShared_4726_ = v_isSharedCheck_4760_;
goto v_resetjp_4724_;
}
else
{
lean_inc(v_val_4723_);
lean_dec(v_res_4722_);
v___x_4725_ = lean_box(0);
v_isShared_4726_ = v_isSharedCheck_4760_;
goto v_resetjp_4724_;
}
v_resetjp_4724_:
{
lean_object* v_fst_4727_; lean_object* v_snd_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4759_; 
v_fst_4727_ = lean_ctor_get(v_val_4723_, 0);
v_snd_4728_ = lean_ctor_get(v_val_4723_, 1);
v_isSharedCheck_4759_ = !lean_is_exclusive(v_val_4723_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4730_ = v_val_4723_;
v_isShared_4731_ = v_isSharedCheck_4759_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_snd_4728_);
lean_inc(v_fst_4727_);
lean_dec(v_val_4723_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4759_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4732_; lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4758_; 
v___x_4732_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4719_);
v_a_4733_ = lean_ctor_get(v___x_4732_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4735_ = v___x_4732_;
v_isShared_4736_ = v_isSharedCheck_4758_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4732_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4758_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___y_4745_; lean_object* v___x_4747_; 
v___x_4737_ = lean_box(0);
v___x_4738_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4739_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4740_ = 1;
v___x_4741_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4742_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4743_ = l_Lean_Syntax_getPos_x3f(v_fst_4727_, v___x_4740_);
v___x_4744_ = lean_box(v___x_4740_);
v___y_4745_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4745_, 0, v___x_4743_);
lean_closure_set(v___y_4745_, 1, v_fst_4727_);
lean_closure_set(v___y_4745_, 2, v___x_4744_);
lean_closure_set(v___y_4745_, 3, v_a_4733_);
lean_closure_set(v___y_4745_, 4, v___x_4737_);
lean_closure_set(v___y_4745_, 5, v___x_4738_);
lean_closure_set(v___y_4745_, 6, v___x_4739_);
lean_closure_set(v___y_4745_, 7, v___x_4737_);
lean_closure_set(v___y_4745_, 8, v___x_4741_);
lean_closure_set(v___y_4745_, 9, v___x_4737_);
lean_closure_set(v___y_4745_, 10, v___x_4737_);
lean_closure_set(v___y_4745_, 11, v___x_4737_);
lean_closure_set(v___y_4745_, 12, v_snd_4728_);
lean_closure_set(v___y_4745_, 13, v___x_4742_);
if (v_isShared_4726_ == 0)
{
lean_ctor_set(v___x_4725_, 0, v___y_4745_);
v___x_4747_ = v___x_4725_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___y_4745_);
v___x_4747_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
lean_object* v___x_4749_; 
if (v_isShared_4731_ == 0)
{
lean_ctor_set(v___x_4730_, 1, v___x_4747_);
lean_ctor_set(v___x_4730_, 0, v___x_4742_);
v___x_4749_ = v___x_4730_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4742_);
lean_ctor_set(v_reuseFailAlloc_4756_, 1, v___x_4747_);
v___x_4749_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4754_; 
v___x_4750_ = lean_unsigned_to_nat(1u);
v___x_4751_ = lean_mk_empty_array_with_capacity(v___x_4750_);
v___x_4752_ = lean_array_push(v___x_4751_, v___x_4749_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 0, v___x_4752_);
v___x_4754_ = v___x_4735_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4752_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
lean_dec(v_res_4722_);
v___x_4761_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4761_);
return v___x_4762_;
}
}
else
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4763_);
return v___x_4764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4765_, v_a_4766_);
lean_dec_ref(v_a_4766_);
lean_dec_ref(v_node_4765_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4769_, lean_object* v_x_4770_, lean_object* v_x_4771_, lean_object* v_node_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v___x_4775_; 
v___x_4775_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4772_, v_a_4773_);
return v___x_4775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4776_, lean_object* v_x_4777_, lean_object* v_x_4778_, lean_object* v_node_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4776_, v_x_4777_, v_x_4778_, v_node_4779_, v_a_4780_);
lean_dec_ref(v_a_4780_);
lean_dec_ref(v_node_4779_);
lean_dec_ref(v_x_4778_);
lean_dec_ref(v_x_4777_);
lean_dec_ref(v_x_4776_);
return v_res_4782_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4783_, lean_object* v_inst_4784_, lean_object* v_R_4785_, lean_object* v_a_4786_, uint8_t v_b_4787_, lean_object* v_c_4788_){
_start:
{
uint8_t v___x_4789_; 
v___x_4789_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4783_, v_a_4786_, v_b_4787_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4790_, lean_object* v_inst_4791_, lean_object* v_R_4792_, lean_object* v_a_4793_, lean_object* v_b_4794_, lean_object* v_c_4795_){
_start:
{
uint8_t v_b_boxed_4796_; uint8_t v_res_4797_; lean_object* v_r_4798_; 
v_b_boxed_4796_ = lean_unbox(v_b_4794_);
v_res_4797_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4790_, v_inst_4791_, v_R_4792_, v_a_4793_, v_b_boxed_4796_, v_c_4795_);
lean_dec_ref(v_s_4790_);
v_r_4798_ = lean_box(v_res_4797_);
return v_r_4798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_(){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4804_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_));
v___x_4805_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4806_ = l_Lean_CodeAction_insertBuiltin(v___x_4804_, v___x_4805_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355____boxed(lean_object* v_a_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_();
return v_res_4808_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4810_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4811_ = lean_string_utf8_byte_size(v___x_4810_);
return v___x_4811_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; uint8_t v___x_4814_; 
v___x_4812_ = lean_unsigned_to_nat(0u);
v___x_4813_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4814_ = lean_nat_dec_eq(v___x_4813_, v___x_4812_);
return v___x_4814_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4815_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4816_ = lean_unsigned_to_nat(0u);
v___x_4817_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4817_);
lean_ctor_set(v___x_4818_, 1, v___x_4816_);
lean_ctor_set(v___x_4818_, 2, v___x_4815_);
return v___x_4818_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4(void){
_start:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; 
v___x_4819_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4820_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4819_);
return v___x_4820_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4821_ = lean_unsigned_to_nat(0u);
v___x_4822_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4);
v___x_4823_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4824_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4823_);
lean_ctor_set(v___x_4824_, 1, v___x_4822_);
lean_ctor_set(v___x_4824_, 2, v___x_4821_);
lean_ctor_set(v___x_4824_, 3, v___x_4821_);
return v___x_4824_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4825_){
_start:
{
lean_object* v___y_4827_; uint8_t v___x_4830_; 
v___x_4830_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
if (v___x_4830_ == 0)
{
lean_object* v___x_4831_; 
v___x_4831_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5);
v___y_4827_ = v___x_4831_;
goto v___jp_4826_;
}
else
{
lean_object* v___x_4832_; 
v___x_4832_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_4827_ = v___x_4832_;
goto v___jp_4826_;
}
v___jp_4826_:
{
uint8_t v___x_4828_; uint8_t v___x_4829_; 
v___x_4828_ = 0;
lean_inc(v___y_4827_);
v___x_4829_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4825_, v___y_4827_, v___x_4828_);
return v___x_4829_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4833_){
_start:
{
uint8_t v_res_4834_; lean_object* v_r_4835_; 
v_res_4834_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4833_);
lean_dec_ref(v_s_4833_);
v_r_4835_ = lean_box(v_res_4834_);
return v_r_4835_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4836_, lean_object* v_as_x27_4837_, uint8_t v_b_4838_){
_start:
{
if (lean_obj_tag(v_as_x27_4837_) == 0)
{
lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4840_ = lean_box(v_b_4838_);
v___x_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4840_);
return v___x_4841_;
}
else
{
lean_object* v_head_4842_; uint8_t v_isSilent_4843_; 
v_head_4842_ = lean_ctor_get(v_as_x27_4837_, 0);
v_isSilent_4843_ = lean_ctor_get_uint8(v_head_4842_, sizeof(void*)*5 + 2);
if (v_isSilent_4843_ == 0)
{
lean_object* v_tail_4844_; lean_object* v_data_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; uint8_t v___x_4850_; 
v_tail_4844_ = lean_ctor_get(v_as_x27_4837_, 1);
v_data_4845_ = lean_ctor_get(v_head_4842_, 4);
lean_inc(v_data_4845_);
v___x_4846_ = l_Lean_MessageData_toString(v_data_4845_);
v___x_4847_ = lean_unsigned_to_nat(0u);
v___x_4848_ = lean_string_utf8_byte_size(v___x_4846_);
v___x_4849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4846_);
lean_ctor_set(v___x_4849_, 1, v___x_4847_);
lean_ctor_set(v___x_4849_, 2, v___x_4848_);
v___x_4850_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4849_);
lean_dec_ref_known(v___x_4849_, 3);
if (v___x_4850_ == 0)
{
v_as_x27_4837_ = v_tail_4844_;
goto _start;
}
else
{
lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4852_ = lean_box(v_foundPanic_4836_);
v___x_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
return v___x_4853_;
}
}
else
{
lean_object* v_tail_4854_; 
v_tail_4854_ = lean_ctor_get(v_as_x27_4837_, 1);
v_as_x27_4837_ = v_tail_4854_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4856_, lean_object* v_as_x27_4857_, lean_object* v_b_4858_, lean_object* v___y_4859_){
_start:
{
uint8_t v_foundPanic_boxed_4860_; uint8_t v_b_boxed_4861_; lean_object* v_res_4862_; 
v_foundPanic_boxed_4860_ = lean_unbox(v_foundPanic_4856_);
v_b_boxed_4861_ = lean_unbox(v_b_4858_);
v_res_4862_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4860_, v_as_x27_4857_, v_b_boxed_4861_);
lean_dec(v_as_x27_4857_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4863_, uint8_t v_severity_4864_, uint8_t v_isSilent_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v___x_4869_; 
v___x_4869_ = l_Lean_Elab_Command_getRef___redArg(v___y_4866_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4871_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
lean_inc(v_a_4870_);
lean_dec_ref_known(v___x_4869_, 1);
v___x_4871_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4870_, v_msgData_4863_, v_severity_4864_, v_isSilent_4865_, v___y_4866_, v___y_4867_);
lean_dec(v_a_4870_);
return v___x_4871_;
}
else
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
lean_dec_ref(v_msgData_4863_);
v_a_4872_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4869_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4869_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
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
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4880_, lean_object* v_severity_4881_, lean_object* v_isSilent_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
uint8_t v_severity_boxed_4886_; uint8_t v_isSilent_boxed_4887_; lean_object* v_res_4888_; 
v_severity_boxed_4886_ = lean_unbox(v_severity_4881_);
v_isSilent_boxed_4887_ = lean_unbox(v_isSilent_4882_);
v_res_4888_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4880_, v_severity_boxed_4886_, v_isSilent_boxed_4887_, v___y_4883_, v___y_4884_);
lean_dec(v___y_4884_);
lean_dec_ref(v___y_4883_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_){
_start:
{
uint8_t v___x_4893_; uint8_t v___x_4894_; lean_object* v___x_4895_; 
v___x_4893_ = 2;
v___x_4894_ = 0;
v___x_4895_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4889_, v___x_4893_, v___x_4894_, v___y_4890_, v___y_4891_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_){
_start:
{
lean_object* v_res_4900_; 
v_res_4900_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4896_, v___y_4897_, v___y_4898_);
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
return v_res_4900_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4909_ = l_Lean_MessageData_ofFormat(v___x_4908_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_){
_start:
{
lean_object* v___x_4914_; uint8_t v_foundPanic_4915_; 
v___x_4914_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4910_);
v_foundPanic_4915_ = l_Lean_Syntax_isOfKind(v_x_4910_, v___x_4914_);
if (v_foundPanic_4915_ == 0)
{
lean_object* v___x_4916_; 
lean_dec(v_x_4910_);
v___x_4916_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4916_;
}
else
{
lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4917_ = lean_unsigned_to_nat(2u);
v___x_4918_ = l_Lean_Syntax_getArg(v_x_4910_, v___x_4917_);
lean_dec(v_x_4910_);
v___x_4919_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4918_, v_a_4911_, v_a_4912_);
if (lean_obj_tag(v___x_4919_) == 0)
{
lean_object* v_a_4920_; uint8_t v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4978_; 
v_a_4920_ = lean_ctor_get(v___x_4919_, 0);
lean_inc(v_a_4920_);
lean_dec_ref_known(v___x_4919_, 1);
v___x_4921_ = 0;
v___x_4922_ = l_Lean_MessageLog_toList(v_a_4920_);
v___x_4923_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4915_, v___x_4922_, v___x_4921_);
lean_dec(v___x_4922_);
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4926_ = v___x_4923_;
v_isShared_4927_ = v_isSharedCheck_4978_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4923_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4978_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
uint8_t v___x_4928_; 
v___x_4928_ = lean_unbox(v_a_4924_);
lean_dec(v_a_4924_);
if (v___x_4928_ == 0)
{
lean_object* v___x_4929_; lean_object* v_env_4930_; lean_object* v_scopes_4931_; lean_object* v_usedQuotCtxts_4932_; lean_object* v_nextMacroScope_4933_; lean_object* v_maxRecDepth_4934_; lean_object* v_ngen_4935_; lean_object* v_auxDeclNGen_4936_; lean_object* v_infoState_4937_; lean_object* v_traceState_4938_; lean_object* v_snapshotTasks_4939_; lean_object* v_prevLinterStates_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4950_; 
lean_del_object(v___x_4926_);
v___x_4929_ = lean_st_ref_take(v_a_4912_);
v_env_4930_ = lean_ctor_get(v___x_4929_, 0);
v_scopes_4931_ = lean_ctor_get(v___x_4929_, 2);
v_usedQuotCtxts_4932_ = lean_ctor_get(v___x_4929_, 3);
v_nextMacroScope_4933_ = lean_ctor_get(v___x_4929_, 4);
v_maxRecDepth_4934_ = lean_ctor_get(v___x_4929_, 5);
v_ngen_4935_ = lean_ctor_get(v___x_4929_, 6);
v_auxDeclNGen_4936_ = lean_ctor_get(v___x_4929_, 7);
v_infoState_4937_ = lean_ctor_get(v___x_4929_, 8);
v_traceState_4938_ = lean_ctor_get(v___x_4929_, 9);
v_snapshotTasks_4939_ = lean_ctor_get(v___x_4929_, 10);
v_prevLinterStates_4940_ = lean_ctor_get(v___x_4929_, 11);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4950_ == 0)
{
lean_object* v_unused_4951_; 
v_unused_4951_ = lean_ctor_get(v___x_4929_, 1);
lean_dec(v_unused_4951_);
v___x_4942_ = v___x_4929_;
v_isShared_4943_ = v_isSharedCheck_4950_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_prevLinterStates_4940_);
lean_inc(v_snapshotTasks_4939_);
lean_inc(v_traceState_4938_);
lean_inc(v_infoState_4937_);
lean_inc(v_auxDeclNGen_4936_);
lean_inc(v_ngen_4935_);
lean_inc(v_maxRecDepth_4934_);
lean_inc(v_nextMacroScope_4933_);
lean_inc(v_usedQuotCtxts_4932_);
lean_inc(v_scopes_4931_);
lean_inc(v_env_4930_);
lean_dec(v___x_4929_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4950_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4945_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 1, v_a_4920_);
v___x_4945_ = v___x_4942_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_env_4930_);
lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_a_4920_);
lean_ctor_set(v_reuseFailAlloc_4949_, 2, v_scopes_4931_);
lean_ctor_set(v_reuseFailAlloc_4949_, 3, v_usedQuotCtxts_4932_);
lean_ctor_set(v_reuseFailAlloc_4949_, 4, v_nextMacroScope_4933_);
lean_ctor_set(v_reuseFailAlloc_4949_, 5, v_maxRecDepth_4934_);
lean_ctor_set(v_reuseFailAlloc_4949_, 6, v_ngen_4935_);
lean_ctor_set(v_reuseFailAlloc_4949_, 7, v_auxDeclNGen_4936_);
lean_ctor_set(v_reuseFailAlloc_4949_, 8, v_infoState_4937_);
lean_ctor_set(v_reuseFailAlloc_4949_, 9, v_traceState_4938_);
lean_ctor_set(v_reuseFailAlloc_4949_, 10, v_snapshotTasks_4939_);
lean_ctor_set(v_reuseFailAlloc_4949_, 11, v_prevLinterStates_4940_);
v___x_4945_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4946_ = lean_st_ref_put(v_a_4912_, v___x_4945_);
v___x_4947_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4948_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4947_, v_a_4911_, v_a_4912_);
return v___x_4948_;
}
}
}
else
{
lean_object* v___x_4952_; lean_object* v_env_4953_; lean_object* v_scopes_4954_; lean_object* v_usedQuotCtxts_4955_; lean_object* v_nextMacroScope_4956_; lean_object* v_maxRecDepth_4957_; lean_object* v_ngen_4958_; lean_object* v_auxDeclNGen_4959_; lean_object* v_infoState_4960_; lean_object* v_traceState_4961_; lean_object* v_snapshotTasks_4962_; lean_object* v_prevLinterStates_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_4976_; 
lean_dec(v_a_4920_);
v___x_4952_ = lean_st_ref_take(v_a_4912_);
v_env_4953_ = lean_ctor_get(v___x_4952_, 0);
v_scopes_4954_ = lean_ctor_get(v___x_4952_, 2);
v_usedQuotCtxts_4955_ = lean_ctor_get(v___x_4952_, 3);
v_nextMacroScope_4956_ = lean_ctor_get(v___x_4952_, 4);
v_maxRecDepth_4957_ = lean_ctor_get(v___x_4952_, 5);
v_ngen_4958_ = lean_ctor_get(v___x_4952_, 6);
v_auxDeclNGen_4959_ = lean_ctor_get(v___x_4952_, 7);
v_infoState_4960_ = lean_ctor_get(v___x_4952_, 8);
v_traceState_4961_ = lean_ctor_get(v___x_4952_, 9);
v_snapshotTasks_4962_ = lean_ctor_get(v___x_4952_, 10);
v_prevLinterStates_4963_ = lean_ctor_get(v___x_4952_, 11);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_4976_ == 0)
{
lean_object* v_unused_4977_; 
v_unused_4977_ = lean_ctor_get(v___x_4952_, 1);
lean_dec(v_unused_4977_);
v___x_4965_ = v___x_4952_;
v_isShared_4966_ = v_isSharedCheck_4976_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_prevLinterStates_4963_);
lean_inc(v_snapshotTasks_4962_);
lean_inc(v_traceState_4961_);
lean_inc(v_infoState_4960_);
lean_inc(v_auxDeclNGen_4959_);
lean_inc(v_ngen_4958_);
lean_inc(v_maxRecDepth_4957_);
lean_inc(v_nextMacroScope_4956_);
lean_inc(v_usedQuotCtxts_4955_);
lean_inc(v_scopes_4954_);
lean_inc(v_env_4953_);
lean_dec(v___x_4952_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_4976_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v___x_4967_; lean_object* v___x_4969_; 
v___x_4967_ = l_Lean_MessageLog_empty;
if (v_isShared_4966_ == 0)
{
lean_ctor_set(v___x_4965_, 1, v___x_4967_);
v___x_4969_ = v___x_4965_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_env_4953_);
lean_ctor_set(v_reuseFailAlloc_4975_, 1, v___x_4967_);
lean_ctor_set(v_reuseFailAlloc_4975_, 2, v_scopes_4954_);
lean_ctor_set(v_reuseFailAlloc_4975_, 3, v_usedQuotCtxts_4955_);
lean_ctor_set(v_reuseFailAlloc_4975_, 4, v_nextMacroScope_4956_);
lean_ctor_set(v_reuseFailAlloc_4975_, 5, v_maxRecDepth_4957_);
lean_ctor_set(v_reuseFailAlloc_4975_, 6, v_ngen_4958_);
lean_ctor_set(v_reuseFailAlloc_4975_, 7, v_auxDeclNGen_4959_);
lean_ctor_set(v_reuseFailAlloc_4975_, 8, v_infoState_4960_);
lean_ctor_set(v_reuseFailAlloc_4975_, 9, v_traceState_4961_);
lean_ctor_set(v_reuseFailAlloc_4975_, 10, v_snapshotTasks_4962_);
lean_ctor_set(v_reuseFailAlloc_4975_, 11, v_prevLinterStates_4963_);
v___x_4969_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4973_; 
v___x_4970_ = lean_st_ref_put(v_a_4912_, v___x_4969_);
v___x_4971_ = lean_box(0);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 0, v___x_4971_);
v___x_4973_ = v___x_4926_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v___x_4971_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
}
}
}
else
{
lean_object* v_a_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_4986_; 
v_a_4979_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4981_ = v___x_4919_;
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_a_4979_);
lean_dec(v___x_4919_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4984_; 
if (v_isShared_4982_ == 0)
{
v___x_4984_ = v___x_4981_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_a_4979_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4987_, v_a_4988_, v_a_4989_);
lean_dec(v_a_4989_);
lean_dec_ref(v_a_4988_);
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4992_, lean_object* v_as_4993_, lean_object* v_as_x27_4994_, uint8_t v_b_4995_, lean_object* v_a_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_){
_start:
{
lean_object* v___x_5000_; 
v___x_5000_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4992_, v_as_x27_4994_, v_b_4995_);
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_5001_, lean_object* v_as_5002_, lean_object* v_as_x27_5003_, lean_object* v_b_5004_, lean_object* v_a_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_){
_start:
{
uint8_t v_foundPanic_boxed_5009_; uint8_t v_b_boxed_5010_; lean_object* v_res_5011_; 
v_foundPanic_boxed_5009_ = lean_unbox(v_foundPanic_5001_);
v_b_boxed_5010_ = lean_unbox(v_b_5004_);
v_res_5011_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_5009_, v_as_5002_, v_as_x27_5003_, v_b_boxed_5010_, v_a_5005_, v___y_5006_, v___y_5007_);
lean_dec(v___y_5007_);
lean_dec_ref(v___y_5006_);
lean_dec(v_as_x27_5003_);
lean_dec(v_as_5002_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
v___x_5020_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_5021_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_5022_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_5023_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_5024_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5020_, v___x_5021_, v___x_5022_, v___x_5023_);
return v___x_5024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_5025_){
_start:
{
lean_object* v_res_5026_; 
v_res_5026_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_5026_;
}
}
lean_object* runtime_initialize_Lean_Elab_Notation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_CodeActions_Attr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_GuardMsgs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_CodeActions_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_guard__msgs_diff = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_guard__msgs_diff);
lean_dec_ref(res);
res = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_();
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
