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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Message_isTrace(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_split___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Message_isTrace___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
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
lean_object* l_Lean_CodeAction_insertBuiltin(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Diff_Action_linePrefix(uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_intercalate(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_value;
static const lean_string_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\n"};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10 = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10_value;
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
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⏎\n"};
static const lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " \n"};
static const lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3;
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object*);
static const lean_ctor_object l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1;
static lean_once_cell_t l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0_value;
static const lean_array_object l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1_value;
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0;
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
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commentBody"};
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
static const lean_ctor_object l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___closed__0 = (const lean_object*)&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0 = (const lean_object*)&l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1;
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "guardMsgsCmd"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 121, 62, 112, 73, 11, 102, 99)}};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 65, .m_data = "❌️ Docstring on `#guard_msgs` does not match generated message:\n\n"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "---\n"};
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46(lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_ = (const lean_object*)&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354____boxed(lean_object*);
static const lean_string_object l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PANIC"};
static const lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0 = (const lean_object*)&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0_value;
static const lean_ctor_object l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1 = (const lean_object*)&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_value;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2;
static lean_once_cell_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(lean_object* v_msg_85_, lean_object* v_reportPos_x3f_86_){
_start:
{
lean_object* v___y_89_; lean_object* v___y_93_; uint32_t v___y_94_; lean_object* v___y_98_; lean_object* v_str_101_; lean_object* v_pos_111_; lean_object* v_endPos_112_; uint8_t v_severity_113_; lean_object* v_caption_114_; lean_object* v_data_115_; lean_object* v___y_117_; lean_object* v___y_118_; lean_object* v___y_119_; lean_object* v_str_130_; lean_object* v_str_142_; lean_object* v___y_153_; lean_object* v_str_157_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v_pos_111_ = lean_ctor_get(v_msg_85_, 1);
lean_inc_ref(v_pos_111_);
v_endPos_112_ = lean_ctor_get(v_msg_85_, 2);
lean_inc(v_endPos_112_);
v_severity_113_ = lean_ctor_get_uint8(v_msg_85_, sizeof(void*)*5 + 1);
v_caption_114_ = lean_ctor_get(v_msg_85_, 3);
v_data_115_ = lean_ctor_get(v_msg_85_, 4);
lean_inc(v_data_115_);
v___x_164_ = l_Lean_MessageData_toString(v_data_115_);
v___x_165_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_166_ = lean_string_dec_eq(v_caption_114_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
lean_inc_ref(v_caption_114_);
v___x_168_ = lean_string_append(v_caption_114_, v___x_167_);
v___x_169_ = lean_string_append(v___x_168_, v___x_164_);
lean_dec_ref(v___x_164_);
v_str_157_ = v___x_169_;
goto v___jp_156_;
}
else
{
v_str_157_ = v___x_164_;
goto v___jp_156_;
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
uint32_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = 10;
v___x_96_ = lean_uint32_dec_eq(v___y_94_, v___x_95_);
if (v___x_96_ == 0)
{
v___y_89_ = v___y_93_;
goto v___jp_88_;
}
else
{
return v___y_93_;
}
}
v___jp_97_:
{
uint32_t v___x_99_; 
v___x_99_ = 65;
v___y_93_ = v___y_98_;
v___y_94_ = v___x_99_;
goto v___jp_92_;
}
v___jp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_102_ = lean_string_utf8_byte_size(v_str_101_);
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_nat_dec_eq(v___x_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_inc_ref(v_str_101_);
v___x_105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_105_, 0, v_str_101_);
lean_ctor_set(v___x_105_, 1, v___x_103_);
lean_ctor_set(v___x_105_, 2, v___x_102_);
v___x_106_ = l_String_Slice_Pos_prev_x3f(v___x_105_, v___x_102_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_dec_ref_known(v___x_105_, 3);
v___y_98_ = v_str_101_;
goto v___jp_97_;
}
else
{
lean_object* v_val_107_; lean_object* v___x_108_; 
v_val_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v___x_106_, 1);
v___x_108_ = l_String_Slice_Pos_get_x3f(v___x_105_, v_val_107_);
lean_dec(v_val_107_);
lean_dec_ref_known(v___x_105_, 3);
if (lean_obj_tag(v___x_108_) == 0)
{
v___y_98_ = v_str_101_;
goto v___jp_97_;
}
else
{
lean_object* v_val_109_; uint32_t v___x_110_; 
v_val_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_val_109_);
lean_dec_ref_known(v___x_108_, 1);
v___x_110_ = lean_unbox_uint32(v_val_109_);
lean_dec(v_val_109_);
v___y_93_ = v_str_101_;
v___y_94_ = v___x_110_;
goto v___jp_92_;
}
}
}
else
{
v___y_89_ = v_str_101_;
goto v___jp_88_;
}
}
v___jp_116_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_120_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__1));
v___x_121_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v___y_118_, v_pos_111_);
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
v_str_101_ = v___x_128_;
goto v___jp_100_;
}
v___jp_129_:
{
if (lean_obj_tag(v_reportPos_x3f_86_) == 1)
{
if (lean_obj_tag(v_endPos_112_) == 0)
{
lean_object* v_val_131_; lean_object* v___x_132_; 
v_val_131_ = lean_ctor_get(v_reportPos_x3f_86_, 0);
v___x_132_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__3));
v___y_117_ = v_str_130_;
v___y_118_ = v_val_131_;
v___y_119_ = v___x_132_;
goto v___jp_116_;
}
else
{
lean_object* v_val_133_; lean_object* v_val_134_; lean_object* v_line_135_; lean_object* v_column_136_; lean_object* v_line_137_; uint8_t v___x_138_; 
v_val_133_ = lean_ctor_get(v_endPos_112_, 0);
lean_inc(v_val_133_);
lean_dec_ref_known(v_endPos_112_, 1);
v_val_134_ = lean_ctor_get(v_reportPos_x3f_86_, 0);
v_line_135_ = lean_ctor_get(v_val_133_, 0);
v_column_136_ = lean_ctor_get(v_val_133_, 1);
v_line_137_ = lean_ctor_get(v_pos_111_, 0);
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
lean_dec(v_endPos_112_);
lean_dec_ref(v_pos_111_);
v_str_101_ = v_str_130_;
goto v___jp_100_;
}
}
v___jp_141_:
{
uint8_t v___x_143_; 
v___x_143_ = l_Lean_Message_isTrace(v_msg_85_);
lean_dec_ref(v_msg_85_);
if (v___x_143_ == 0)
{
switch(v_severity_113_)
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
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_158_ = lean_string_utf8_byte_size(v_str_157_);
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = lean_nat_dec_le(v___x_159_, v___x_158_);
if (v___x_160_ == 0)
{
v___y_153_ = v_str_157_;
goto v___jp_152_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_161_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_string_memcmp(v_str_157_, v___x_161_, v___x_162_, v___x_162_, v___x_159_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___boxed(lean_object* v_msg_170_, lean_object* v_reportPos_x3f_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_msg_170_, v_reportPos_x3f_171_);
lean_dec(v_reportPos_x3f_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(uint8_t v_x_174_){
_start:
{
switch(v_x_174_)
{
case 0:
{
lean_object* v___x_175_; 
v___x_175_ = lean_unsigned_to_nat(0u);
return v___x_175_;
}
case 1:
{
lean_object* v___x_176_; 
v___x_176_ = lean_unsigned_to_nat(1u);
return v___x_176_;
}
default: 
{
lean_object* v___x_177_; 
v___x_177_ = lean_unsigned_to_nat(2u);
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___boxed(lean_object* v_x_178_){
_start:
{
uint8_t v_x_boxed_179_; lean_object* v_res_180_; 
v_x_boxed_179_ = lean_unbox(v_x_178_);
v_res_180_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(v_x_boxed_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(lean_object* v_k_181_){
_start:
{
lean_inc(v_k_181_);
return v_k_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg___boxed(lean_object* v_k_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(v_k_182_);
lean_dec(v_k_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(lean_object* v_motive_184_, lean_object* v_ctorIdx_185_, uint8_t v_t_186_, lean_object* v_h_187_, lean_object* v_k_188_){
_start:
{
lean_inc(v_k_188_);
return v_k_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___boxed(lean_object* v_motive_189_, lean_object* v_ctorIdx_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_k_193_){
_start:
{
uint8_t v_t_boxed_194_; lean_object* v_res_195_; 
v_t_boxed_194_ = lean_unbox(v_t_191_);
v_res_195_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(v_motive_189_, v_ctorIdx_190_, v_t_boxed_194_, v_h_192_, v_k_193_);
lean_dec(v_k_193_);
lean_dec(v_ctorIdx_190_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(lean_object* v_check_196_){
_start:
{
lean_inc(v_check_196_);
return v_check_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg___boxed(lean_object* v_check_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(v_check_197_);
lean_dec(v_check_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(lean_object* v_motive_199_, uint8_t v_t_200_, lean_object* v_h_201_, lean_object* v_check_202_){
_start:
{
lean_inc(v_check_202_);
return v_check_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___boxed(lean_object* v_motive_203_, lean_object* v_t_204_, lean_object* v_h_205_, lean_object* v_check_206_){
_start:
{
uint8_t v_t_boxed_207_; lean_object* v_res_208_; 
v_t_boxed_207_ = lean_unbox(v_t_204_);
v_res_208_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(v_motive_203_, v_t_boxed_207_, v_h_205_, v_check_206_);
lean_dec(v_check_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(lean_object* v_drop_209_){
_start:
{
lean_inc(v_drop_209_);
return v_drop_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg___boxed(lean_object* v_drop_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(v_drop_210_);
lean_dec(v_drop_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(lean_object* v_motive_212_, uint8_t v_t_213_, lean_object* v_h_214_, lean_object* v_drop_215_){
_start:
{
lean_inc(v_drop_215_);
return v_drop_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___boxed(lean_object* v_motive_216_, lean_object* v_t_217_, lean_object* v_h_218_, lean_object* v_drop_219_){
_start:
{
uint8_t v_t_boxed_220_; lean_object* v_res_221_; 
v_t_boxed_220_ = lean_unbox(v_t_217_);
v_res_221_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(v_motive_216_, v_t_boxed_220_, v_h_218_, v_drop_219_);
lean_dec(v_drop_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(lean_object* v_pass_222_){
_start:
{
lean_inc(v_pass_222_);
return v_pass_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg___boxed(lean_object* v_pass_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(v_pass_223_);
lean_dec(v_pass_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(lean_object* v_motive_225_, uint8_t v_t_226_, lean_object* v_h_227_, lean_object* v_pass_228_){
_start:
{
lean_inc(v_pass_228_);
return v_pass_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___boxed(lean_object* v_motive_229_, lean_object* v_t_230_, lean_object* v_h_231_, lean_object* v_pass_232_){
_start:
{
uint8_t v_t_boxed_233_; lean_object* v_res_234_; 
v_t_boxed_233_ = lean_unbox(v_t_230_);
v_res_234_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(v_motive_229_, v_t_boxed_233_, v_h_231_, v_pass_232_);
lean_dec(v_pass_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(uint8_t v_x_235_){
_start:
{
switch(v_x_235_)
{
case 0:
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(0u);
return v___x_236_;
}
case 1:
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(1u);
return v___x_237_;
}
default: 
{
lean_object* v___x_238_; 
v___x_238_ = lean_unsigned_to_nat(2u);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___boxed(lean_object* v_x_239_){
_start:
{
uint8_t v_x_boxed_240_; lean_object* v_res_241_; 
v_x_boxed_240_ = lean_unbox(v_x_239_);
v_res_241_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(v_x_boxed_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(lean_object* v_k_242_){
_start:
{
lean_inc(v_k_242_);
return v_k_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg___boxed(lean_object* v_k_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(v_k_243_);
lean_dec(v_k_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(lean_object* v_motive_245_, lean_object* v_ctorIdx_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_k_249_){
_start:
{
lean_inc(v_k_249_);
return v_k_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___boxed(lean_object* v_motive_250_, lean_object* v_ctorIdx_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_k_254_){
_start:
{
uint8_t v_t_boxed_255_; lean_object* v_res_256_; 
v_t_boxed_255_ = lean_unbox(v_t_252_);
v_res_256_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(v_motive_250_, v_ctorIdx_251_, v_t_boxed_255_, v_h_253_, v_k_254_);
lean_dec(v_k_254_);
lean_dec(v_ctorIdx_251_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(lean_object* v_exact_257_){
_start:
{
lean_inc(v_exact_257_);
return v_exact_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg___boxed(lean_object* v_exact_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(v_exact_258_);
lean_dec(v_exact_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(lean_object* v_motive_260_, uint8_t v_t_261_, lean_object* v_h_262_, lean_object* v_exact_263_){
_start:
{
lean_inc(v_exact_263_);
return v_exact_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___boxed(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_exact_267_){
_start:
{
uint8_t v_t_boxed_268_; lean_object* v_res_269_; 
v_t_boxed_268_ = lean_unbox(v_t_265_);
v_res_269_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(v_motive_264_, v_t_boxed_268_, v_h_266_, v_exact_267_);
lean_dec(v_exact_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(lean_object* v_normalized_270_){
_start:
{
lean_inc(v_normalized_270_);
return v_normalized_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg___boxed(lean_object* v_normalized_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(v_normalized_271_);
lean_dec(v_normalized_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(lean_object* v_motive_273_, uint8_t v_t_274_, lean_object* v_h_275_, lean_object* v_normalized_276_){
_start:
{
lean_inc(v_normalized_276_);
return v_normalized_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___boxed(lean_object* v_motive_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_normalized_280_){
_start:
{
uint8_t v_t_boxed_281_; lean_object* v_res_282_; 
v_t_boxed_281_ = lean_unbox(v_t_278_);
v_res_282_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(v_motive_277_, v_t_boxed_281_, v_h_279_, v_normalized_280_);
lean_dec(v_normalized_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(lean_object* v_lax_283_){
_start:
{
lean_inc(v_lax_283_);
return v_lax_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg___boxed(lean_object* v_lax_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(v_lax_284_);
lean_dec(v_lax_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(lean_object* v_motive_286_, uint8_t v_t_287_, lean_object* v_h_288_, lean_object* v_lax_289_){
_start:
{
lean_inc(v_lax_289_);
return v_lax_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___boxed(lean_object* v_motive_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_lax_293_){
_start:
{
uint8_t v_t_boxed_294_; lean_object* v_res_295_; 
v_t_boxed_294_ = lean_unbox(v_t_291_);
v_res_295_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(v_motive_290_, v_t_boxed_294_, v_h_292_, v_lax_293_);
lean_dec(v_lax_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(uint8_t v_x_296_){
_start:
{
if (v_x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_unsigned_to_nat(0u);
return v___x_297_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_unsigned_to_nat(1u);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___boxed(lean_object* v_x_299_){
_start:
{
uint8_t v_x_boxed_300_; lean_object* v_res_301_; 
v_x_boxed_300_ = lean_unbox(v_x_299_);
v_res_301_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(v_x_boxed_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(lean_object* v_k_302_){
_start:
{
lean_inc(v_k_302_);
return v_k_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg___boxed(lean_object* v_k_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(v_k_303_);
lean_dec(v_k_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(lean_object* v_motive_305_, lean_object* v_ctorIdx_306_, uint8_t v_t_307_, lean_object* v_h_308_, lean_object* v_k_309_){
_start:
{
lean_inc(v_k_309_);
return v_k_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___boxed(lean_object* v_motive_310_, lean_object* v_ctorIdx_311_, lean_object* v_t_312_, lean_object* v_h_313_, lean_object* v_k_314_){
_start:
{
uint8_t v_t_boxed_315_; lean_object* v_res_316_; 
v_t_boxed_315_ = lean_unbox(v_t_312_);
v_res_316_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(v_motive_310_, v_ctorIdx_311_, v_t_boxed_315_, v_h_313_, v_k_314_);
lean_dec(v_k_314_);
lean_dec(v_ctorIdx_311_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(lean_object* v_exact_317_){
_start:
{
lean_inc(v_exact_317_);
return v_exact_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg___boxed(lean_object* v_exact_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(v_exact_318_);
lean_dec(v_exact_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(lean_object* v_motive_320_, uint8_t v_t_321_, lean_object* v_h_322_, lean_object* v_exact_323_){
_start:
{
lean_inc(v_exact_323_);
return v_exact_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___boxed(lean_object* v_motive_324_, lean_object* v_t_325_, lean_object* v_h_326_, lean_object* v_exact_327_){
_start:
{
uint8_t v_t_boxed_328_; lean_object* v_res_329_; 
v_t_boxed_328_ = lean_unbox(v_t_325_);
v_res_329_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(v_motive_324_, v_t_boxed_328_, v_h_326_, v_exact_327_);
lean_dec(v_exact_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(lean_object* v_sorted_330_){
_start:
{
lean_inc(v_sorted_330_);
return v_sorted_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg___boxed(lean_object* v_sorted_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(v_sorted_331_);
lean_dec(v_sorted_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(lean_object* v_motive_333_, uint8_t v_t_334_, lean_object* v_h_335_, lean_object* v_sorted_336_){
_start:
{
lean_inc(v_sorted_336_);
return v_sorted_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___boxed(lean_object* v_motive_337_, lean_object* v_t_338_, lean_object* v_h_339_, lean_object* v_sorted_340_){
_start:
{
uint8_t v_t_boxed_341_; lean_object* v_res_342_; 
v_t_boxed_341_ = lean_unbox(v_t_338_);
v_res_342_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(v_motive_337_, v_t_boxed_341_, v_h_339_, v_sorted_340_);
lean_dec(v_sorted_340_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_box(0);
v___x_344_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg(){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___boxed(lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(lean_object* v_00_u03b1_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___boxed(lean_object* v_00_u03b1_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(v_00_u03b1_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(lean_object* v_action_x3f_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
if (lean_obj_tag(v_action_x3f_378_) == 1)
{
lean_object* v_val_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_413_; 
v_val_382_ = lean_ctor_get(v_action_x3f_378_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v_action_x3f_378_);
if (v_isSharedCheck_413_ == 0)
{
v___x_384_ = v_action_x3f_378_;
v_isShared_385_ = v_isSharedCheck_413_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_val_382_);
lean_dec(v_action_x3f_378_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_413_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1));
lean_inc(v_val_382_);
v___x_387_ = l_Lean_Syntax_isOfKind(v_val_382_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_del_object(v___x_384_);
lean_dec(v_val_382_);
v___x_388_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = l_Lean_Syntax_getArg(v_val_382_, v___x_389_);
lean_dec(v_val_382_);
v___x_391_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4));
lean_inc(v___x_390_);
v___x_392_ = l_Lean_Syntax_isOfKind(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6));
lean_inc(v___x_390_);
v___x_394_ = l_Lean_Syntax_isOfKind(v___x_390_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8));
v___x_396_ = l_Lean_Syntax_isOfKind(v___x_390_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_del_object(v___x_384_);
v___x_397_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_397_;
}
else
{
uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_398_ = 2;
v___x_399_ = lean_box(v___x_398_);
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 0);
lean_ctor_set(v___x_384_, 0, v___x_399_);
v___x_401_ = v___x_384_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
lean_dec(v___x_390_);
v___x_403_ = 1;
v___x_404_ = lean_box(v___x_403_);
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 0);
lean_ctor_set(v___x_384_, 0, v___x_404_);
v___x_406_ = v___x_384_;
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
lean_dec(v___x_390_);
v___x_408_ = 0;
v___x_409_ = lean_box(v___x_408_);
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 0);
lean_ctor_set(v___x_384_, 0, v___x_409_);
v___x_411_ = v___x_384_;
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
}
}
else
{
uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec(v_action_x3f_378_);
v___x_414_ = 0;
v___x_415_ = lean_box(v___x_414_);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___boxed(lean_object* v_action_x3f_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
return v_res_421_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(uint8_t v___x_422_, lean_object* v_x_423_){
_start:
{
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed(lean_object* v___x_424_, lean_object* v_x_425_){
_start:
{
uint8_t v___x_777__boxed_426_; uint8_t v_res_427_; lean_object* v_r_428_; 
v___x_777__boxed_426_ = lean_unbox(v___x_424_);
v_res_427_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_777__boxed_426_, v_x_425_);
lean_dec_ref(v_x_425_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(uint8_t v___x_429_, uint8_t v___x_430_, lean_object* v_msg_431_){
_start:
{
uint8_t v___y_433_; uint8_t v___x_437_; 
v___x_437_ = l_Lean_Message_isTrace(v_msg_431_);
if (v___x_437_ == 0)
{
v___y_433_ = v___x_430_;
goto v___jp_432_;
}
else
{
v___y_433_ = v___x_429_;
goto v___jp_432_;
}
v___jp_432_:
{
if (v___y_433_ == 0)
{
return v___x_429_;
}
else
{
uint8_t v_severity_434_; uint8_t v___x_435_; uint8_t v___x_436_; 
v_severity_434_ = lean_ctor_get_uint8(v_msg_431_, sizeof(void*)*5 + 1);
v___x_435_ = 2;
v___x_436_ = l_Lean_instBEqMessageSeverity_beq(v_severity_434_, v___x_435_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v_msg_440_){
_start:
{
uint8_t v___x_783__boxed_441_; uint8_t v___x_784__boxed_442_; uint8_t v_res_443_; lean_object* v_r_444_; 
v___x_783__boxed_441_ = lean_unbox(v___x_438_);
v___x_784__boxed_442_ = lean_unbox(v___x_439_);
v_res_443_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_783__boxed_441_, v___x_784__boxed_442_, v_msg_440_);
lean_dec_ref(v_msg_440_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(uint8_t v___x_445_, uint8_t v___x_446_, lean_object* v_msg_447_){
_start:
{
uint8_t v___y_449_; uint8_t v___x_453_; 
v___x_453_ = l_Lean_Message_isTrace(v_msg_447_);
if (v___x_453_ == 0)
{
v___y_449_ = v___x_446_;
goto v___jp_448_;
}
else
{
v___y_449_ = v___x_445_;
goto v___jp_448_;
}
v___jp_448_:
{
if (v___y_449_ == 0)
{
return v___x_445_;
}
else
{
uint8_t v_severity_450_; uint8_t v___x_451_; uint8_t v___x_452_; 
v_severity_450_ = lean_ctor_get_uint8(v_msg_447_, sizeof(void*)*5 + 1);
v___x_451_ = 1;
v___x_452_ = l_Lean_instBEqMessageSeverity_beq(v_severity_450_, v___x_451_);
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object* v___x_454_, lean_object* v___x_455_, lean_object* v_msg_456_){
_start:
{
uint8_t v___x_799__boxed_457_; uint8_t v___x_800__boxed_458_; uint8_t v_res_459_; lean_object* v_r_460_; 
v___x_799__boxed_457_ = lean_unbox(v___x_454_);
v___x_800__boxed_458_ = lean_unbox(v___x_455_);
v_res_459_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_799__boxed_457_, v___x_800__boxed_458_, v_msg_456_);
lean_dec_ref(v_msg_456_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(uint8_t v___x_461_, uint8_t v___x_462_, lean_object* v_msg_463_){
_start:
{
uint8_t v___y_465_; uint8_t v___x_469_; 
v___x_469_ = l_Lean_Message_isTrace(v_msg_463_);
if (v___x_469_ == 0)
{
v___y_465_ = v___x_462_;
goto v___jp_464_;
}
else
{
v___y_465_ = v___x_461_;
goto v___jp_464_;
}
v___jp_464_:
{
if (v___y_465_ == 0)
{
return v___x_461_;
}
else
{
uint8_t v_severity_466_; uint8_t v___x_467_; uint8_t v___x_468_; 
v_severity_466_ = lean_ctor_get_uint8(v_msg_463_, sizeof(void*)*5 + 1);
v___x_467_ = 0;
v___x_468_ = l_Lean_instBEqMessageSeverity_beq(v_severity_466_, v___x_467_);
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v_msg_472_){
_start:
{
uint8_t v___x_815__boxed_473_; uint8_t v___x_816__boxed_474_; uint8_t v_res_475_; lean_object* v_r_476_; 
v___x_815__boxed_473_ = lean_unbox(v___x_470_);
v___x_816__boxed_474_ = lean_unbox(v___x_471_);
v_res_475_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_815__boxed_473_, v___x_816__boxed_474_, v_msg_472_);
lean_dec_ref(v_msg_472_);
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
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___f_525_; lean_object* v___x_526_; 
lean_dec(v___x_508_);
v___x_523_ = lean_box(v___x_514_);
v___x_524_ = lean_box(v___x_516_);
v___f_525_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_525_, 0, v___x_523_);
lean_closure_set(v___f_525_, 1, v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___f_525_);
return v___x_526_;
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___f_529_; lean_object* v___x_530_; 
lean_dec(v___x_508_);
v___x_527_ = lean_box(v___x_512_);
v___x_528_ = lean_box(v___x_514_);
v___f_529_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_529_, 0, v___x_527_);
lean_closure_set(v___f_529_, 1, v___x_528_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___f_529_);
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___f_533_; lean_object* v___x_534_; 
lean_dec(v___x_508_);
v___x_531_ = lean_box(v___x_510_);
v___x_532_ = lean_box(v___x_512_);
v___f_533_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_533_, 0, v___x_531_);
lean_closure_set(v___f_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___f_533_);
return v___x_534_;
}
}
else
{
lean_object* v___f_535_; lean_object* v___x_536_; 
lean_dec(v___x_508_);
v___f_535_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12));
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___f_535_);
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___boxed(lean_object* v_x_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(lean_object* v_x_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_540_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___boxed(lean_object* v_x_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(v_x_545_, v_a_546_, v_a_547_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
return v_res_549_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object* v_x_550_){
_start:
{
uint8_t v___x_551_; 
v___x_551_ = 0;
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object* v_x_552_){
_start:
{
uint8_t v_res_553_; lean_object* v_r_554_; 
v_res_553_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(v_x_552_);
lean_dec_ref(v_x_552_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(lean_object* v_snd_555_, lean_object* v___y_556_){
_start:
{
if (lean_obj_tag(v_snd_555_) == 0)
{
uint8_t v___x_557_; 
lean_dec_ref(v___y_556_);
v___x_557_ = 0;
return v___x_557_;
}
else
{
lean_object* v_val_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_val_558_ = lean_ctor_get(v_snd_555_, 0);
lean_inc(v_val_558_);
lean_dec_ref_known(v_snd_555_, 1);
v___x_559_ = lean_apply_1(v_val_558_, v___y_556_);
v___x_560_ = lean_unbox(v___x_559_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed(lean_object* v_snd_561_, lean_object* v___y_562_){
_start:
{
uint8_t v_res_563_; lean_object* v_r_564_; 
v_res_563_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(v_snd_561_, v___y_562_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(lean_object* v_a_565_, lean_object* v_snd_566_, uint8_t v_a_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
lean_inc_ref(v___y_568_);
v___x_569_ = lean_apply_1(v_a_565_, v___y_568_);
v___x_570_ = lean_unbox(v___x_569_);
if (v___x_570_ == 0)
{
if (lean_obj_tag(v_snd_566_) == 0)
{
uint8_t v___x_571_; 
lean_dec_ref(v___y_568_);
v___x_571_ = 2;
return v___x_571_;
}
else
{
lean_object* v_val_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_val_572_ = lean_ctor_get(v_snd_566_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v_snd_566_, 1);
v___x_573_ = lean_apply_1(v_val_572_, v___y_568_);
v___x_574_ = lean_unbox(v___x_573_);
return v___x_574_;
}
}
else
{
lean_dec_ref(v___y_568_);
lean_dec(v_snd_566_);
return v_a_567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed(lean_object* v_a_575_, lean_object* v_snd_576_, lean_object* v_a_577_, lean_object* v___y_578_){
_start:
{
uint8_t v_a_6444__boxed_579_; uint8_t v_res_580_; lean_object* v_r_581_; 
v_a_6444__boxed_579_ = lean_unbox(v_a_577_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_575_, v_snd_576_, v_a_6444__boxed_579_, v___y_578_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object* v_as_642_, size_t v_sz_643_, size_t v_i_644_, lean_object* v_b_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_a_650_; uint8_t v___x_654_; 
v___x_654_ = lean_usize_dec_lt(v_i_644_, v_sz_643_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_b_645_);
return v___x_655_;
}
else
{
lean_object* v_snd_656_; lean_object* v_snd_657_; lean_object* v_snd_658_; lean_object* v_fst_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_966_; 
v_snd_656_ = lean_ctor_get(v_b_645_, 1);
lean_inc(v_snd_656_);
v_snd_657_ = lean_ctor_get(v_snd_656_, 1);
lean_inc(v_snd_657_);
v_snd_658_ = lean_ctor_get(v_snd_657_, 1);
lean_inc(v_snd_658_);
v_fst_659_ = lean_ctor_get(v_b_645_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v_b_645_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v_b_645_, 1);
lean_dec(v_unused_967_);
v___x_661_ = v_b_645_;
v_isShared_662_ = v_isSharedCheck_966_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_fst_659_);
lean_dec(v_b_645_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_966_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_fst_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_964_; 
v_fst_663_ = lean_ctor_get(v_snd_656_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_snd_656_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v_snd_656_, 1);
lean_dec(v_unused_965_);
v___x_665_ = v_snd_656_;
v_isShared_666_ = v_isSharedCheck_964_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_fst_663_);
lean_dec(v_snd_656_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_964_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_fst_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_962_; 
v_fst_667_ = lean_ctor_get(v_snd_657_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_snd_657_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_snd_657_, 1);
lean_dec(v_unused_963_);
v___x_669_ = v_snd_657_;
v_isShared_670_ = v_isSharedCheck_962_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_fst_667_);
lean_dec(v_snd_657_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_962_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_fst_671_; lean_object* v_snd_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_961_; 
v_fst_671_ = lean_ctor_get(v_snd_658_, 0);
v_snd_672_ = lean_ctor_get(v_snd_658_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_snd_658_);
if (v_isSharedCheck_961_ == 0)
{
v___x_674_ = v_snd_658_;
v_isShared_675_ = v_isSharedCheck_961_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snd_672_);
lean_inc(v_fst_671_);
lean_dec(v_snd_658_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_961_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_a_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_a_676_ = lean_array_uget_borrowed(v_as_642_, v_i_644_);
v___x_677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_a_676_);
v___x_678_ = l_Lean_Syntax_isOfKind(v_a_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v___x_681_; 
lean_dec_ref_known(v___x_679_, 1);
if (v_isShared_675_ == 0)
{
v___x_681_ = v___x_674_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_fst_671_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_snd_672_);
v___x_681_ = v_reuseFailAlloc_691_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v___x_681_);
v___x_683_ = v___x_669_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_fst_667_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_681_);
v___x_683_ = v_reuseFailAlloc_690_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_685_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_683_);
v___x_685_ = v___x_665_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_fst_663_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_683_);
v___x_685_ = v_reuseFailAlloc_689_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_687_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_685_);
v___x_687_ = v___x_661_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_fst_659_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
v_a_650_ = v___x_687_;
goto v___jp_649_;
}
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_del_object(v___x_674_);
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_del_object(v___x_669_);
lean_dec(v_fst_667_);
lean_del_object(v___x_665_);
lean_dec(v_fst_663_);
lean_del_object(v___x_661_);
lean_dec(v_fst_659_);
v_a_692_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_679_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_679_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_action_x3f_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = l_Lean_Syntax_getArg(v_a_676_, v___x_700_);
v___x_742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3));
lean_inc(v___x_701_);
v___x_743_ = l_Lean_Syntax_isOfKind(v___x_701_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; uint8_t v___x_745_; 
lean_del_object(v___x_674_);
lean_del_object(v___x_669_);
lean_del_object(v___x_665_);
lean_del_object(v___x_661_);
v___x_744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5));
lean_inc(v___x_701_);
v___x_745_ = l_Lean_Syntax_isOfKind(v___x_701_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; uint8_t v_reportPositions_747_; 
v___x_746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7));
lean_inc(v___x_701_);
v_reportPositions_747_ = l_Lean_Syntax_isOfKind(v___x_701_, v___x_746_);
if (v_reportPositions_747_ == 0)
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9));
lean_inc(v___x_701_);
v___x_749_ = l_Lean_Syntax_isOfKind(v___x_701_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11));
lean_inc(v___x_701_);
v___x_751_ = l_Lean_Syntax_isOfKind(v___x_701_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_dec(v___x_701_);
v___x_752_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec_ref_known(v___x_752_, 1);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_fst_671_);
lean_ctor_set(v___x_753_, 1, v_snd_672_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_fst_667_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_fst_663_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_fst_659_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v_a_650_ = v___x_756_;
goto v___jp_649_;
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
v_a_757_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_752_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_752_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_765_ = lean_unsigned_to_nat(2u);
v___x_766_ = l_Lean_Syntax_getArg(v___x_701_, v___x_765_);
lean_dec(v___x_701_);
v___x_767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_766_);
v___x_768_ = l_Lean_Syntax_isOfKind(v___x_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_770_ = l_Lean_Syntax_isOfKind(v___x_766_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec_ref_known(v___x_771_, 1);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_fst_671_);
lean_ctor_set(v___x_772_, 1, v_snd_672_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_fst_667_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_fst_663_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_fst_659_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v_a_650_ = v___x_775_;
goto v___jp_649_;
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
v_a_776_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_771_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_771_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec(v_fst_671_);
v___x_784_ = lean_box(v_reportPositions_747_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v_snd_672_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_fst_667_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_fst_663_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_fst_659_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v_a_650_ = v___x_788_;
goto v___jp_649_;
}
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec(v___x_766_);
lean_dec(v_fst_671_);
v___x_789_ = lean_box(v___x_678_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v_snd_672_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_fst_667_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v_fst_663_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_fst_659_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v_a_650_ = v___x_793_;
goto v___jp_649_;
}
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_794_ = lean_unsigned_to_nat(2u);
v___x_795_ = l_Lean_Syntax_getArg(v___x_701_, v___x_794_);
lean_dec(v___x_701_);
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17));
lean_inc(v___x_795_);
v___x_797_ = l_Lean_Syntax_isOfKind(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec(v___x_795_);
v___x_798_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec_ref_known(v___x_798_, 1);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_fst_671_);
lean_ctor_set(v___x_799_, 1, v_snd_672_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_fst_667_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_fst_663_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_fst_659_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v_a_650_ = v___x_802_;
goto v___jp_649_;
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
v_a_803_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_798_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_798_);
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
lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_811_ = l_Lean_Syntax_getArg(v___x_795_, v___x_700_);
lean_dec(v___x_795_);
v___x_812_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_811_);
v___x_813_ = l_Lean_Syntax_isOfKind(v___x_811_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_815_ = l_Lean_Syntax_isOfKind(v___x_811_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec_ref_known(v___x_816_, 1);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_fst_671_);
lean_ctor_set(v___x_817_, 1, v_snd_672_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_fst_667_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_fst_663_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_fst_659_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v_a_650_ = v___x_820_;
goto v___jp_649_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
v_a_821_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_816_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_816_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec(v_fst_667_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v_fst_671_);
lean_ctor_set(v___x_829_, 1, v_snd_672_);
v___x_830_ = lean_box(v_reportPositions_747_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v___x_829_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_fst_663_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_fst_659_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v_a_650_ = v___x_833_;
goto v___jp_649_;
}
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v___x_811_);
lean_dec(v_fst_667_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_fst_671_);
lean_ctor_set(v___x_834_, 1, v_snd_672_);
v___x_835_ = lean_box(v___x_678_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v___x_834_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_fst_663_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_fst_659_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v_a_650_ = v___x_838_;
goto v___jp_649_;
}
}
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_839_ = lean_unsigned_to_nat(2u);
v___x_840_ = l_Lean_Syntax_getArg(v___x_701_, v___x_839_);
lean_dec(v___x_701_);
v___x_841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19));
lean_inc(v___x_840_);
v___x_842_ = l_Lean_Syntax_isOfKind(v___x_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec(v___x_840_);
v___x_843_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref_known(v___x_843_, 1);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_fst_671_);
lean_ctor_set(v___x_844_, 1, v_snd_672_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_fst_667_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v_fst_663_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_fst_659_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v_a_650_ = v___x_847_;
goto v___jp_649_;
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
v_a_848_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_843_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_843_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_856_ = l_Lean_Syntax_getArg(v___x_840_, v___x_700_);
lean_dec(v___x_840_);
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_856_);
v___x_858_ = l_Lean_Syntax_isOfKind(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23));
v___x_860_ = l_Lean_Syntax_isOfKind(v___x_856_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec_ref_known(v___x_861_, 1);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_fst_671_);
lean_ctor_set(v___x_862_, 1, v_snd_672_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_fst_667_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v_fst_663_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v_fst_659_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v_a_650_ = v___x_865_;
goto v___jp_649_;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
v_a_866_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_861_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_861_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec(v_fst_663_);
v___x_874_ = 1;
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v_fst_671_);
lean_ctor_set(v___x_875_, 1, v_snd_672_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v_fst_667_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_box(v___x_874_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_876_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_fst_659_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v_a_650_ = v___x_879_;
goto v___jp_649_;
}
}
else
{
uint8_t v_ordering_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec(v___x_856_);
lean_dec(v_fst_663_);
v_ordering_880_ = 0;
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v_fst_671_);
lean_ctor_set(v___x_881_, 1, v_snd_672_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_fst_667_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_box(v_ordering_880_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_882_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v_fst_659_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v_a_650_ = v___x_885_;
goto v___jp_649_;
}
}
}
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_886_ = lean_unsigned_to_nat(2u);
v___x_887_ = l_Lean_Syntax_getArg(v___x_701_, v___x_886_);
lean_dec(v___x_701_);
v___x_888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25));
lean_inc(v___x_887_);
v___x_889_ = l_Lean_Syntax_isOfKind(v___x_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v___x_887_);
v___x_890_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec_ref_known(v___x_890_, 1);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_fst_671_);
lean_ctor_set(v___x_891_, 1, v_snd_672_);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v_fst_667_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_fst_663_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v_fst_659_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v_a_650_ = v___x_894_;
goto v___jp_649_;
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
v_a_895_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_890_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_890_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_903_ = l_Lean_Syntax_getArg(v___x_887_, v___x_700_);
lean_dec(v___x_887_);
v___x_904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_903_);
v___x_905_ = l_Lean_Syntax_isOfKind(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27));
lean_inc(v___x_903_);
v___x_907_ = l_Lean_Syntax_isOfKind(v___x_903_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29));
v___x_909_ = l_Lean_Syntax_isOfKind(v___x_903_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec_ref_known(v___x_910_, 1);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_fst_671_);
lean_ctor_set(v___x_911_, 1, v_snd_672_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_fst_667_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_fst_663_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_fst_659_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v_a_650_ = v___x_914_;
goto v___jp_649_;
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
v_a_915_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_910_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_910_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v_fst_659_);
v___x_923_ = 2;
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v_fst_671_);
lean_ctor_set(v___x_924_, 1, v_snd_672_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_fst_667_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_fst_663_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_box(v___x_923_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_926_);
v_a_650_ = v___x_928_;
goto v___jp_649_;
}
}
else
{
uint8_t v_whitespace_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v___x_903_);
lean_dec(v_fst_659_);
v_whitespace_929_ = 1;
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v_fst_671_);
lean_ctor_set(v___x_930_, 1, v_snd_672_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v_fst_667_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_fst_663_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_box(v_whitespace_929_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_932_);
v_a_650_ = v___x_934_;
goto v___jp_649_;
}
}
else
{
uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v___x_903_);
lean_dec(v_fst_659_);
v___x_935_ = 0;
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_fst_671_);
lean_ctor_set(v___x_936_, 1, v_snd_672_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_fst_667_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_fst_663_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_box(v___x_935_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___x_938_);
v_a_650_ = v___x_940_;
goto v___jp_649_;
}
}
}
}
else
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = l_Lean_Syntax_getArg(v___x_701_, v___x_700_);
v___x_942_ = l_Lean_Syntax_isNone(v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_941_);
v___x_944_ = l_Lean_Syntax_matchesNull(v___x_941_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
lean_dec(v___x_941_);
lean_dec(v___x_701_);
lean_del_object(v___x_674_);
lean_del_object(v___x_669_);
lean_del_object(v___x_665_);
lean_del_object(v___x_661_);
v___x_945_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec_ref_known(v___x_945_, 1);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_fst_671_);
lean_ctor_set(v___x_946_, 1, v_snd_672_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v_fst_667_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v_fst_663_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_fst_659_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v_a_650_ = v___x_949_;
goto v___jp_649_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
v_a_950_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_945_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_945_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = l_Lean_Syntax_getArg(v___x_941_, v___x_700_);
lean_dec(v___x_941_);
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
v_action_x3f_703_ = v___x_959_;
v___y_704_ = v___y_646_;
v___y_705_ = v___y_647_;
goto v___jp_702_;
}
}
else
{
lean_object* v___x_960_; 
lean_dec(v___x_941_);
v___x_960_ = lean_box(0);
v_action_x3f_703_ = v___x_960_;
v___y_704_ = v___y_646_;
v___y_705_ = v___y_647_;
goto v___jp_702_;
}
}
v___jp_702_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = l_Lean_Syntax_getArg(v___x_701_, v___x_706_);
lean_dec(v___x_701_);
v___x_708_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_703_, v___y_704_, v___y_705_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v___x_707_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___f_712_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_712_, 0, v_a_711_);
lean_closure_set(v___f_712_, 1, v_snd_672_);
lean_closure_set(v___f_712_, 2, v_a_709_);
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v___f_712_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_713_);
v___x_715_ = v___x_674_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_fst_671_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_713_);
v___x_715_ = v_reuseFailAlloc_725_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v___x_715_);
v___x_717_ = v___x_669_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_fst_667_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_724_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_717_);
v___x_719_ = v___x_665_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_fst_663_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_719_);
v___x_721_ = v___x_661_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_fst_659_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v_a_650_ = v___x_721_;
goto v___jp_649_;
}
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec(v_a_709_);
lean_del_object(v___x_674_);
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_del_object(v___x_669_);
lean_dec(v_fst_667_);
lean_del_object(v___x_665_);
lean_dec(v_fst_663_);
lean_del_object(v___x_661_);
lean_dec(v_fst_659_);
v_a_726_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_710_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_710_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v___x_707_);
lean_del_object(v___x_674_);
lean_dec(v_snd_672_);
lean_dec(v_fst_671_);
lean_del_object(v___x_669_);
lean_dec(v_fst_667_);
lean_del_object(v___x_665_);
lean_dec(v_fst_663_);
lean_del_object(v___x_661_);
lean_dec(v_fst_659_);
v_a_734_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_708_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_708_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
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
v___jp_649_:
{
size_t v___x_651_; size_t v___x_652_; 
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_add(v_i_644_, v___x_651_);
v_i_644_ = v___x_652_;
v_b_645_ = v_a_650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object* v_as_968_, lean_object* v_sz_969_, lean_object* v_i_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
size_t v_sz_boxed_975_; size_t v_i_boxed_976_; lean_object* v_res_977_; 
v_sz_boxed_975_ = lean_unbox_usize(v_sz_969_);
lean_dec(v_sz_969_);
v_i_boxed_976_ = lean_unbox_usize(v_i_970_);
lean_dec(v_i_970_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v_as_968_, v_sz_boxed_975_, v_i_boxed_976_, v_b_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec_ref(v_as_968_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(size_t v_sz_978_, size_t v_i_979_, lean_object* v_bs_980_){
_start:
{
uint8_t v___x_981_; 
v___x_981_ = lean_usize_dec_lt(v_i_979_, v_sz_978_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v_bs_980_);
return v___x_982_;
}
else
{
lean_object* v_v_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v_v_983_ = lean_array_uget(v_bs_980_, v_i_979_);
v___x_984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_v_983_);
v___x_985_ = l_Lean_Syntax_isOfKind(v_v_983_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
lean_dec(v_v_983_);
lean_dec_ref(v_bs_980_);
v___x_986_ = lean_box(0);
return v___x_986_;
}
else
{
lean_object* v___x_987_; lean_object* v_bs_x27_988_; size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v_bs_x27_988_ = lean_array_uset(v_bs_980_, v_i_979_, v___x_987_);
v___x_989_ = ((size_t)1ULL);
v___x_990_ = lean_usize_add(v_i_979_, v___x_989_);
v___x_991_ = lean_array_uset(v_bs_x27_988_, v_i_979_, v_v_983_);
v_i_979_ = v___x_990_;
v_bs_980_ = v___x_991_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1___boxed(lean_object* v_sz_993_, lean_object* v_i_994_, lean_object* v_bs_995_){
_start:
{
size_t v_sz_boxed_996_; size_t v_i_boxed_997_; lean_object* v_res_998_; 
v_sz_boxed_996_ = lean_unbox_usize(v_sz_993_);
lean_dec(v_sz_993_);
v_i_boxed_997_ = lean_unbox_usize(v_i_994_);
lean_dec(v_i_994_);
v_res_998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_boxed_996_, v_i_boxed_997_, v_bs_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(uint8_t v___x_999_, lean_object* v_as_1000_, size_t v_i_1001_, size_t v_stop_1002_, lean_object* v_b_1003_){
_start:
{
lean_object* v___y_1005_; uint8_t v___x_1009_; 
v___x_1009_ = lean_usize_dec_eq(v_i_1001_, v_stop_1002_);
if (v___x_1009_ == 0)
{
lean_object* v_fst_1010_; uint8_t v___x_1011_; 
v_fst_1010_ = lean_ctor_get(v_b_1003_, 0);
v___x_1011_ = lean_unbox(v_fst_1010_);
if (v___x_1011_ == 0)
{
lean_object* v_snd_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_snd_1012_ = lean_ctor_get(v_b_1003_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_b_1003_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_b_1003_, 0);
lean_dec(v_unused_1021_);
v___x_1014_ = v_b_1003_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_snd_1012_);
lean_dec(v_b_1003_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = lean_box(v___x_999_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_snd_1012_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
v___y_1005_ = v___x_1018_;
goto v___jp_1004_;
}
}
}
else
{
lean_object* v_snd_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1032_; 
v_snd_1022_ = lean_ctor_get(v_b_1003_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_b_1003_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v_b_1003_, 0);
lean_dec(v_unused_1033_);
v___x_1024_ = v_b_1003_;
v_isShared_1025_ = v_isSharedCheck_1032_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_snd_1022_);
lean_dec(v_b_1003_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1032_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1026_ = lean_array_uget_borrowed(v_as_1000_, v_i_1001_);
lean_inc(v___x_1026_);
v___x_1027_ = lean_array_push(v_snd_1022_, v___x_1026_);
v___x_1028_ = lean_box(v___x_1009_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v___x_1027_);
lean_ctor_set(v___x_1024_, 0, v___x_1028_);
v___x_1030_ = v___x_1024_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___x_1027_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
v___y_1005_ = v___x_1030_;
goto v___jp_1004_;
}
}
}
}
else
{
return v_b_1003_;
}
v___jp_1004_:
{
size_t v___x_1006_; size_t v___x_1007_; 
v___x_1006_ = ((size_t)1ULL);
v___x_1007_ = lean_usize_add(v_i_1001_, v___x_1006_);
v_i_1001_ = v___x_1007_;
v_b_1003_ = v___y_1005_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object* v___x_1034_, lean_object* v_as_1035_, lean_object* v_i_1036_, lean_object* v_stop_1037_, lean_object* v_b_1038_){
_start:
{
uint8_t v___x_7319__boxed_1039_; size_t v_i_boxed_1040_; size_t v_stop_boxed_1041_; lean_object* v_res_1042_; 
v___x_7319__boxed_1039_ = lean_unbox(v___x_1034_);
v_i_boxed_1040_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_stop_boxed_1041_ = lean_unbox_usize(v_stop_1037_);
lean_dec(v_stop_1037_);
v_res_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_7319__boxed_1039_, v_as_1035_, v_i_boxed_1040_, v_stop_boxed_1041_, v_b_1038_);
lean_dec_ref(v_as_1035_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object* v_spec_x3f_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_elts_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1115_; lean_object* v_cfg_1129_; 
v_cfg_1129_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5));
if (lean_obj_tag(v_spec_x3f_1071_) == 1)
{
lean_object* v_val_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_val_1130_ = lean_ctor_get(v_spec_x3f_1071_, 0);
lean_inc_n(v_val_1130_, 2);
lean_dec_ref_known(v_spec_x3f_1071_, 1);
v___x_1131_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7));
v___x_1132_ = l_Lean_Syntax_isOfKind(v_val_1130_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_val_1130_);
v___x_1133_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = l_Lean_Syntax_getArg(v_val_1130_, v___x_1142_);
lean_dec(v_val_1130_);
v___x_1144_ = l_Lean_Syntax_getArgs(v___x_1143_);
lean_dec(v___x_1143_);
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8));
v___x_1147_ = lean_array_get_size(v___x_1144_);
v___x_1148_ = lean_nat_dec_lt(v___x_1145_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_dec_ref(v___x_1144_);
v___y_1115_ = v___x_1146_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; lean_object* v___x_1153_; lean_object* v_snd_1154_; 
v___x_1149_ = lean_box(v___x_1148_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v___x_1146_);
v___x_1151_ = ((size_t)0ULL);
v___x_1152_ = lean_usize_of_nat(v___x_1147_);
v___x_1153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1132_, v___x_1144_, v___x_1151_, v___x_1152_, v___x_1150_);
lean_dec_ref(v___x_1144_);
v_snd_1154_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_snd_1154_);
lean_dec_ref(v___x_1153_);
v___y_1115_ = v_snd_1154_;
goto v___jp_1114_;
}
}
}
else
{
lean_object* v___x_1155_; 
lean_dec(v_spec_x3f_1071_);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_cfg_1129_);
return v___x_1155_;
}
v___jp_1075_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; size_t v_sz_1081_; size_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1079_ = l_Array_reverse___redArg(v_elts_1076_);
v___x_1080_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4));
v_sz_1081_ = lean_array_size(v___x_1079_);
v___x_1082_ = ((size_t)0ULL);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v___x_1079_, v_sz_1081_, v___x_1082_, v___x_1080_, v___y_1077_, v___y_1078_);
lean_dec_ref(v___x_1079_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1105_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1105_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1105_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v_snd_1088_; lean_object* v_snd_1089_; lean_object* v_snd_1090_; lean_object* v_fst_1091_; lean_object* v_fst_1092_; lean_object* v_fst_1093_; lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___y_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; uint8_t v___x_1099_; uint8_t v___x_1100_; uint8_t v___x_1101_; lean_object* v___x_1103_; 
v_snd_1088_ = lean_ctor_get(v_a_1084_, 1);
lean_inc(v_snd_1088_);
v_snd_1089_ = lean_ctor_get(v_snd_1088_, 1);
lean_inc(v_snd_1089_);
v_snd_1090_ = lean_ctor_get(v_snd_1089_, 1);
lean_inc(v_snd_1090_);
v_fst_1091_ = lean_ctor_get(v_a_1084_, 0);
lean_inc(v_fst_1091_);
lean_dec(v_a_1084_);
v_fst_1092_ = lean_ctor_get(v_snd_1088_, 0);
lean_inc(v_fst_1092_);
lean_dec(v_snd_1088_);
v_fst_1093_ = lean_ctor_get(v_snd_1089_, 0);
lean_inc(v_fst_1093_);
lean_dec(v_snd_1089_);
v_fst_1094_ = lean_ctor_get(v_snd_1090_, 0);
lean_inc(v_fst_1094_);
v_snd_1095_ = lean_ctor_get(v_snd_1090_, 1);
lean_inc(v_snd_1095_);
lean_dec(v_snd_1090_);
v___y_1096_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___y_1096_, 0, v_snd_1095_);
v___x_1097_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1097_, 0, v___y_1096_);
v___x_1098_ = lean_unbox(v_fst_1091_);
lean_dec(v_fst_1091_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*1, v___x_1098_);
v___x_1099_ = lean_unbox(v_fst_1092_);
lean_dec(v_fst_1092_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*1 + 1, v___x_1099_);
v___x_1100_ = lean_unbox(v_fst_1093_);
lean_dec(v_fst_1093_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*1 + 2, v___x_1100_);
v___x_1101_ = lean_unbox(v_fst_1094_);
lean_dec(v_fst_1094_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*1 + 3, v___x_1101_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1097_);
v___x_1103_ = v___x_1086_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1097_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1106_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1083_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1083_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
v___jp_1114_:
{
size_t v_sz_1116_; size_t v___x_1117_; lean_object* v___x_1118_; 
v_sz_1116_ = lean_array_size(v___y_1115_);
v___x_1117_ = ((size_t)0ULL);
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_1116_, v___x_1117_, v___y_1115_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1119_; lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v___x_1119_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_object* v_val_1128_; 
v_val_1128_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_val_1128_);
lean_dec_ref_known(v___x_1118_, 1);
v_elts_1076_ = v_val_1128_;
v___y_1077_ = v_a_1072_;
v___y_1078_ = v_a_1073_;
goto v___jp_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object* v_spec_x3f_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v_spec_x3f_1156_, v_a_1157_, v_a_1158_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(lean_object* v_s_1173_, lean_object* v_replacement_1174_, lean_object* v_a_1175_, lean_object* v_b_1176_){
_start:
{
lean_object* v_it_1178_; lean_object* v_startPos_1179_; lean_object* v_endPos_1180_; lean_object* v_it_1189_; 
switch(lean_obj_tag(v_a_1175_))
{
case 0:
{
lean_object* v_pos_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1207_; 
v_pos_1195_ = lean_ctor_get(v_a_1175_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_a_1175_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1197_ = v_a_1175_;
v_isShared_1198_ = v_isSharedCheck_1207_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_pos_1195_);
lean_dec(v_a_1175_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1207_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v_startInclusive_1199_; lean_object* v_endExclusive_1200_; lean_object* v___x_1201_; uint8_t v_decide_1202_; 
v_startInclusive_1199_ = lean_ctor_get(v_s_1173_, 1);
v_endExclusive_1200_ = lean_ctor_get(v_s_1173_, 2);
v___x_1201_ = lean_nat_sub(v_endExclusive_1200_, v_startInclusive_1199_);
v_decide_1202_ = lean_nat_dec_eq(v_pos_1195_, v___x_1201_);
lean_dec(v___x_1201_);
if (v_decide_1202_ == 0)
{
lean_object* v___x_1204_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set_tag(v___x_1197_, 1);
v___x_1204_ = v___x_1197_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_pos_1195_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
v_it_1189_ = v___x_1204_;
goto v___jp_1188_;
}
}
else
{
lean_object* v___x_1206_; 
lean_del_object(v___x_1197_);
lean_dec(v_pos_1195_);
v___x_1206_ = lean_box(3);
v_it_1189_ = v___x_1206_;
goto v___jp_1188_;
}
}
}
case 1:
{
lean_object* v_pos_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1220_; 
v_pos_1208_ = lean_ctor_get(v_a_1175_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_a_1175_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1210_ = v_a_1175_;
v_isShared_1211_ = v_isSharedCheck_1220_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_pos_1208_);
lean_dec(v_a_1175_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1220_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v_str_1212_; lean_object* v_startInclusive_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
v_str_1212_ = lean_ctor_get(v_s_1173_, 0);
v_startInclusive_1213_ = lean_ctor_get(v_s_1173_, 1);
v___x_1214_ = lean_nat_add(v_startInclusive_1213_, v_pos_1208_);
v___x_1215_ = lean_string_utf8_next_fast(v_str_1212_, v___x_1214_);
lean_dec(v___x_1214_);
v___x_1216_ = lean_nat_sub(v___x_1215_, v_startInclusive_1213_);
lean_inc(v___x_1216_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set_tag(v___x_1210_, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1216_);
v___x_1218_ = v___x_1210_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
v_it_1178_ = v___x_1218_;
v_startPos_1179_ = v_pos_1208_;
v_endPos_1180_ = v___x_1216_;
goto v___jp_1177_;
}
}
}
case 2:
{
lean_object* v_needle_1221_; lean_object* v_table_1222_; lean_object* v_stackPos_1223_; lean_object* v_needlePos_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1285_; 
v_needle_1221_ = lean_ctor_get(v_a_1175_, 0);
v_table_1222_ = lean_ctor_get(v_a_1175_, 1);
v_stackPos_1223_ = lean_ctor_get(v_a_1175_, 2);
v_needlePos_1224_ = lean_ctor_get(v_a_1175_, 3);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_a_1175_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1226_ = v_a_1175_;
v_isShared_1227_ = v_isSharedCheck_1285_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_needlePos_1224_);
lean_inc(v_stackPos_1223_);
lean_inc(v_table_1222_);
lean_inc(v_needle_1221_);
lean_dec(v_a_1175_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1285_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_str_1228_; lean_object* v_startInclusive_1229_; lean_object* v_endExclusive_1230_; lean_object* v_str_1231_; lean_object* v_startInclusive_1232_; lean_object* v_endExclusive_1233_; lean_object* v_basePos_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_str_1228_ = lean_ctor_get(v_needle_1221_, 0);
v_startInclusive_1229_ = lean_ctor_get(v_needle_1221_, 1);
v_endExclusive_1230_ = lean_ctor_get(v_needle_1221_, 2);
v_str_1231_ = lean_ctor_get(v_s_1173_, 0);
v_startInclusive_1232_ = lean_ctor_get(v_s_1173_, 1);
v_endExclusive_1233_ = lean_ctor_get(v_s_1173_, 2);
v_basePos_1234_ = lean_nat_sub(v_stackPos_1223_, v_needlePos_1224_);
v___x_1235_ = lean_nat_sub(v_endExclusive_1230_, v_startInclusive_1229_);
v___x_1236_ = lean_nat_add(v_basePos_1234_, v___x_1235_);
v___x_1237_ = lean_nat_sub(v_endExclusive_1233_, v_startInclusive_1232_);
v___x_1238_ = lean_nat_dec_le(v___x_1236_, v___x_1237_);
lean_dec(v___x_1236_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
lean_dec(v___x_1235_);
lean_del_object(v___x_1226_);
lean_dec(v_needlePos_1224_);
lean_dec(v_stackPos_1223_);
lean_dec_ref(v_table_1222_);
lean_dec_ref(v_needle_1221_);
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_nat_add(v_basePos_1234_, v___x_1239_);
v___x_1241_ = lean_nat_dec_le(v___x_1240_, v___x_1237_);
lean_dec(v___x_1240_);
if (v___x_1241_ == 0)
{
lean_dec(v___x_1237_);
lean_dec(v_basePos_1234_);
lean_dec_ref(v_s_1173_);
return v_b_1176_;
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = l_String_Slice_pos_x21(v_s_1173_, v_basePos_1234_);
lean_dec(v_basePos_1234_);
v___x_1243_ = lean_box(3);
v_it_1178_ = v___x_1243_;
v_startPos_1179_ = v___x_1242_;
v_endPos_1180_ = v___x_1237_;
goto v___jp_1177_;
}
}
else
{
lean_object* v___x_1244_; uint8_t v_stackByte_1245_; lean_object* v___x_1246_; uint8_t v_patByte_1247_; uint8_t v___x_1248_; 
lean_dec(v___x_1237_);
v___x_1244_ = lean_nat_add(v_startInclusive_1232_, v_stackPos_1223_);
v_stackByte_1245_ = lean_string_get_byte_fast(v_str_1231_, v___x_1244_);
v___x_1246_ = lean_nat_add(v_startInclusive_1229_, v_needlePos_1224_);
v_patByte_1247_ = lean_string_get_byte_fast(v_str_1228_, v___x_1246_);
v___x_1248_ = lean_uint8_dec_eq(v_stackByte_1245_, v_patByte_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; uint8_t v_decide_1250_; 
lean_dec(v___x_1235_);
v___x_1249_ = lean_unsigned_to_nat(0u);
v_decide_1250_ = lean_nat_dec_eq(v_needlePos_1224_, v___x_1249_);
if (v_decide_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_newNeedlePos_1253_; uint8_t v___x_1254_; 
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_nat_sub(v_needlePos_1224_, v___x_1251_);
lean_dec(v_needlePos_1224_);
v_newNeedlePos_1253_ = lean_array_fget_borrowed(v_table_1222_, v___x_1252_);
lean_dec(v___x_1252_);
v___x_1254_ = lean_nat_dec_eq(v_newNeedlePos_1253_, v___x_1249_);
if (v___x_1254_ == 0)
{
lean_object* v_oldBasePos_1255_; lean_object* v___x_1256_; lean_object* v_newBasePos_1257_; lean_object* v___x_1259_; 
lean_inc(v_newNeedlePos_1253_);
v_oldBasePos_1255_ = l_String_Slice_pos_x21(v_s_1173_, v_basePos_1234_);
lean_dec(v_basePos_1234_);
v___x_1256_ = lean_nat_sub(v_stackPos_1223_, v_newNeedlePos_1253_);
v_newBasePos_1257_ = l_String_Slice_pos_x21(v_s_1173_, v___x_1256_);
lean_dec(v___x_1256_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 3, v_newNeedlePos_1253_);
v___x_1259_ = v___x_1226_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_needle_1221_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_table_1222_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_stackPos_1223_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_newNeedlePos_1253_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
v_it_1178_ = v___x_1259_;
v_startPos_1179_ = v_oldBasePos_1255_;
v_endPos_1180_ = v_newBasePos_1257_;
goto v___jp_1177_;
}
}
else
{
lean_object* v_basePos_1261_; lean_object* v_nextStackPos_1262_; lean_object* v___x_1264_; 
v_basePos_1261_ = l_String_Slice_pos_x21(v_s_1173_, v_basePos_1234_);
lean_dec(v_basePos_1234_);
v_nextStackPos_1262_ = l_String_Slice_posGE___redArg(v_s_1173_, v_stackPos_1223_);
lean_inc(v_nextStackPos_1262_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 3, v___x_1249_);
lean_ctor_set(v___x_1226_, 2, v_nextStackPos_1262_);
v___x_1264_ = v___x_1226_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_needle_1221_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_table_1222_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_nextStackPos_1262_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v___x_1249_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
v_it_1178_ = v___x_1264_;
v_startPos_1179_ = v_basePos_1261_;
v_endPos_1180_ = v_nextStackPos_1262_;
goto v___jp_1177_;
}
}
}
else
{
lean_object* v_basePos_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_nextStackPos_1269_; lean_object* v___x_1271_; 
lean_dec(v_basePos_1234_);
lean_dec(v_needlePos_1224_);
v_basePos_1266_ = l_String_Slice_pos_x21(v_s_1173_, v_stackPos_1223_);
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = lean_nat_add(v_stackPos_1223_, v___x_1267_);
lean_dec(v_stackPos_1223_);
v_nextStackPos_1269_ = l_String_Slice_posGE___redArg(v_s_1173_, v___x_1268_);
lean_inc(v_nextStackPos_1269_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 3, v___x_1249_);
lean_ctor_set(v___x_1226_, 2, v_nextStackPos_1269_);
v___x_1271_ = v___x_1226_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_needle_1221_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_table_1222_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_nextStackPos_1269_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v___x_1249_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
v_it_1178_ = v___x_1271_;
v_startPos_1179_ = v_basePos_1266_;
v_endPos_1180_ = v_nextStackPos_1269_;
goto v___jp_1177_;
}
}
}
else
{
lean_object* v___x_1273_; lean_object* v_nextStackPos_1274_; lean_object* v_nextNeedlePos_1275_; uint8_t v_decide_1276_; 
lean_dec(v_basePos_1234_);
v___x_1273_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1274_ = lean_nat_add(v_stackPos_1223_, v___x_1273_);
lean_dec(v_stackPos_1223_);
v_nextNeedlePos_1275_ = lean_nat_add(v_needlePos_1224_, v___x_1273_);
lean_dec(v_needlePos_1224_);
v_decide_1276_ = lean_nat_dec_eq(v_nextNeedlePos_1275_, v___x_1235_);
lean_dec(v___x_1235_);
if (v_decide_1276_ == 0)
{
lean_object* v___x_1278_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 3, v_nextNeedlePos_1275_);
lean_ctor_set(v___x_1226_, 2, v_nextStackPos_1274_);
v___x_1278_ = v___x_1226_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_needle_1221_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_table_1222_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_nextStackPos_1274_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v_nextNeedlePos_1275_);
v___x_1278_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
v_a_1175_ = v___x_1278_;
goto _start;
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
lean_dec(v_nextNeedlePos_1275_);
v___x_1281_ = lean_unsigned_to_nat(0u);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 3, v___x_1281_);
lean_ctor_set(v___x_1226_, 2, v_nextStackPos_1274_);
v___x_1283_ = v___x_1226_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_needle_1221_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_table_1222_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_nextStackPos_1274_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
v_it_1189_ = v___x_1283_;
goto v___jp_1188_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1173_);
return v_b_1176_;
}
}
v___jp_1177_:
{
lean_object* v___x_1181_; lean_object* v_str_1182_; lean_object* v_startInclusive_1183_; lean_object* v_endExclusive_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_inc_ref(v_s_1173_);
v___x_1181_ = l_String_Slice_slice_x21(v_s_1173_, v_startPos_1179_, v_endPos_1180_);
lean_dec(v_endPos_1180_);
lean_dec(v_startPos_1179_);
v_str_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc_ref(v_str_1182_);
v_startInclusive_1183_ = lean_ctor_get(v___x_1181_, 1);
lean_inc(v_startInclusive_1183_);
v_endExclusive_1184_ = lean_ctor_get(v___x_1181_, 2);
lean_inc(v_endExclusive_1184_);
lean_dec_ref(v___x_1181_);
v___x_1185_ = lean_string_utf8_extract_fast(v_str_1182_, v_startInclusive_1183_, v_endExclusive_1184_);
lean_dec(v_endExclusive_1184_);
lean_dec(v_startInclusive_1183_);
lean_dec_ref(v_str_1182_);
v___x_1186_ = lean_string_append(v_b_1176_, v___x_1185_);
lean_dec_ref(v___x_1185_);
v_a_1175_ = v_it_1178_;
v_b_1176_ = v___x_1186_;
goto _start;
}
v___jp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_string_utf8_byte_size(v_replacement_1174_);
v___x_1192_ = lean_string_utf8_extract_fast(v_replacement_1174_, v___x_1190_, v___x_1191_);
v___x_1193_ = lean_string_append(v_b_1176_, v___x_1192_);
lean_dec_ref(v___x_1192_);
v_a_1175_ = v_it_1189_;
v_b_1176_ = v___x_1193_;
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
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1));
v___x_1297_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2);
v___x_1300_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1));
v___x_1301_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___x_1299_);
lean_ctor_set(v___x_1301_, 2, v___x_1298_);
lean_ctor_set(v___x_1301_, 3, v___x_1298_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object* v_s_1302_, lean_object* v_replacement_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1305_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1306_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1302_, v_replacement_1303_, v___x_1305_, v___x_1304_);
return v___x_1306_;
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
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1));
v___x_1316_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2);
v___x_1319_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1));
v___x_1320_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v___x_1318_);
lean_ctor_set(v___x_1320_, 2, v___x_1317_);
lean_ctor_set(v___x_1320_, 3, v___x_1317_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object* v_s_1321_, lean_object* v_replacement_1322_){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1324_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1325_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1321_, v_replacement_1322_, v___x_1324_, v___x_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object* v_s_1326_, lean_object* v_replacement_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1326_, v_replacement_1327_);
lean_dec_ref(v_replacement_1327_);
return v_res_1328_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1));
v___x_1335_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1334_);
return v___x_1335_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2);
v___x_1338_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1));
v___x_1339_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v___x_1337_);
lean_ctor_set(v___x_1339_, 2, v___x_1336_);
lean_ctor_set(v___x_1339_, 3, v___x_1336_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(lean_object* v_s_1340_, lean_object* v_replacement_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1343_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1344_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1340_, v_replacement_1341_, v___x_1343_, v___x_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___boxed(lean_object* v_s_1345_, lean_object* v_replacement_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1345_, v_replacement_1346_);
lean_dec_ref(v_replacement_1346_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object* v_s_1351_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1352_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0));
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = lean_string_utf8_byte_size(v_s_1351_);
v___x_1355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1355_, 0, v_s_1351_);
lean_ctor_set(v___x_1355_, 1, v___x_1353_);
lean_ctor_set(v___x_1355_, 2, v___x_1354_);
v___x_1356_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1355_, v___x_1352_);
v___x_1357_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1));
v___x_1358_ = lean_string_utf8_byte_size(v___x_1356_);
v___x_1359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1356_);
lean_ctor_set(v___x_1359_, 1, v___x_1353_);
lean_ctor_set(v___x_1359_, 2, v___x_1358_);
v___x_1360_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v___x_1359_, v___x_1357_);
v___x_1361_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2));
v___x_1362_ = lean_string_utf8_byte_size(v___x_1360_);
v___x_1363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1360_);
lean_ctor_set(v___x_1363_, 1, v___x_1353_);
lean_ctor_set(v___x_1363_, 2, v___x_1362_);
v___x_1364_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v___x_1363_, v___x_1361_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(lean_object* v_s_1365_, lean_object* v_pattern_1366_, lean_object* v_replacement_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1365_, v_replacement_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___boxed(lean_object* v_s_1369_, lean_object* v_pattern_1370_, lean_object* v_replacement_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(v_s_1369_, v_pattern_1370_, v_replacement_1371_);
lean_dec_ref(v_replacement_1371_);
lean_dec_ref(v_pattern_1370_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(lean_object* v_s_1373_, lean_object* v_pattern_1374_, lean_object* v_replacement_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1373_, v_replacement_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___boxed(lean_object* v_s_1377_, lean_object* v_pattern_1378_, lean_object* v_replacement_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(v_s_1377_, v_pattern_1378_, v_replacement_1379_);
lean_dec_ref(v_replacement_1379_);
lean_dec_ref(v_pattern_1378_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(lean_object* v_s_1381_, lean_object* v_pattern_1382_, lean_object* v_replacement_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1381_, v_replacement_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___boxed(lean_object* v_s_1385_, lean_object* v_pattern_1386_, lean_object* v_replacement_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(v_s_1385_, v_pattern_1386_, v_replacement_1387_);
lean_dec_ref(v_replacement_1387_);
lean_dec_ref(v_pattern_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(lean_object* v_s_1389_, lean_object* v_replacement_1390_, lean_object* v_inst_1391_, lean_object* v_R_1392_, lean_object* v_a_1393_, lean_object* v_b_1394_, lean_object* v_c_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1389_, v_replacement_1390_, v_a_1393_, v_b_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___boxed(lean_object* v_s_1397_, lean_object* v_replacement_1398_, lean_object* v_inst_1399_, lean_object* v_R_1400_, lean_object* v_a_1401_, lean_object* v_b_1402_, lean_object* v_c_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(v_s_1397_, v_replacement_1398_, v_inst_1399_, v_R_1400_, v_a_1401_, v_b_1402_, v_c_1403_);
lean_dec_ref(v_replacement_1398_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object* v_s_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1406_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1407_ = lean_unsigned_to_nat(0u);
v___x_1408_ = lean_string_utf8_byte_size(v_s_1405_);
v___x_1409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1409_, 0, v_s_1405_);
lean_ctor_set(v___x_1409_, 1, v___x_1407_);
lean_ctor_set(v___x_1409_, 2, v___x_1408_);
v___x_1410_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1409_, v___x_1406_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg(){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___closed__0));
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___boxed(lean_object* v___dummy_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
return v_res_1416_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object* v_s_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object* v_s_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v_s_1420_);
lean_dec_ref(v_s_1420_);
return v_res_1421_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0));
v___x_1427_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1430_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0));
v___x_1431_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1429_);
lean_ctor_set(v___x_1431_, 2, v___x_1428_);
lean_ctor_set(v___x_1431_, 3, v___x_1428_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object* v_s_1432_, lean_object* v_replacement_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1435_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2);
v___x_1436_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1432_, v_replacement_1433_, v___x_1435_, v___x_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object* v_s_1437_, lean_object* v_replacement_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1437_, v_replacement_1438_);
lean_dec_ref(v_replacement_1438_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object* v_s_1440_, lean_object* v___x_1441_, lean_object* v___x_1442_, lean_object* v_a_1443_, lean_object* v_b_1444_){
_start:
{
lean_object* v_it_1446_; lean_object* v_startInclusive_1447_; lean_object* v_endExclusive_1448_; 
if (lean_obj_tag(v_a_1443_) == 0)
{
lean_object* v_currPos_1456_; lean_object* v_searcher_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1485_; 
v_currPos_1456_ = lean_ctor_get(v_a_1443_, 0);
v_searcher_1457_ = lean_ctor_get(v_a_1443_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_a_1443_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1459_ = v_a_1443_;
v_isShared_1460_ = v_isSharedCheck_1485_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_searcher_1457_);
lean_inc(v_currPos_1456_);
lean_dec(v_a_1443_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1485_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
uint8_t v_decide_1471_; 
v_decide_1471_ = lean_nat_dec_eq(v_searcher_1457_, v___x_1442_);
if (v_decide_1471_ == 0)
{
uint32_t v___x_1472_; uint32_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = lean_string_utf8_get_fast(v_s_1440_, v_searcher_1457_);
v___x_1473_ = 32;
v___x_1474_ = lean_uint32_dec_eq(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
uint32_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = 9;
v___x_1476_ = lean_uint32_dec_eq(v___x_1472_, v___x_1475_);
if (v___x_1476_ == 0)
{
uint32_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = 13;
v___x_1478_ = lean_uint32_dec_eq(v___x_1472_, v___x_1477_);
if (v___x_1478_ == 0)
{
uint32_t v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = 10;
v___x_1480_ = lean_uint32_dec_eq(v___x_1472_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_del_object(v___x_1459_);
v___x_1481_ = lean_string_utf8_next_fast(v_s_1440_, v_searcher_1457_);
lean_dec(v_searcher_1457_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_currPos_1456_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v_a_1443_ = v___x_1482_;
goto _start;
}
else
{
goto v___jp_1461_;
}
}
else
{
goto v___jp_1461_;
}
}
else
{
goto v___jp_1461_;
}
}
else
{
goto v___jp_1461_;
}
}
else
{
lean_object* v___x_1484_; 
lean_del_object(v___x_1459_);
lean_dec(v_searcher_1457_);
v___x_1484_ = lean_box(1);
lean_inc(v___x_1442_);
v_it_1446_ = v___x_1484_;
v_startInclusive_1447_ = v_currPos_1456_;
v_endExclusive_1448_ = v___x_1442_;
goto v___jp_1445_;
}
v___jp_1461_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v_slice_1465_; lean_object* v_nextIt_1467_; 
v___x_1462_ = lean_string_utf8_next_fast(v_s_1440_, v_searcher_1457_);
v___x_1463_ = lean_nat_sub(v___x_1462_, v_searcher_1457_);
v___x_1464_ = lean_nat_add(v_searcher_1457_, v___x_1463_);
lean_dec(v___x_1463_);
v_slice_1465_ = l_String_Slice_subslice_x21(v___x_1441_, v_currPos_1456_, v_searcher_1457_);
lean_inc(v___x_1464_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 1, v___x_1464_);
lean_ctor_set(v___x_1459_, 0, v___x_1464_);
v_nextIt_1467_ = v___x_1459_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v___x_1464_);
v_nextIt_1467_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v_startInclusive_1468_; lean_object* v_endExclusive_1469_; 
v_startInclusive_1468_ = lean_ctor_get(v_slice_1465_, 0);
lean_inc(v_startInclusive_1468_);
v_endExclusive_1469_ = lean_ctor_get(v_slice_1465_, 1);
lean_inc(v_endExclusive_1469_);
lean_dec_ref(v_slice_1465_);
v_it_1446_ = v_nextIt_1467_;
v_startInclusive_1447_ = v_startInclusive_1468_;
v_endExclusive_1448_ = v_endExclusive_1469_;
goto v___jp_1445_;
}
}
}
}
else
{
lean_dec(v___x_1442_);
lean_dec_ref(v_s_1440_);
return v_b_1444_;
}
v___jp_1445_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = lean_nat_sub(v_endExclusive_1448_, v_startInclusive_1447_);
v___x_1450_ = lean_unsigned_to_nat(0u);
v___x_1451_ = lean_nat_dec_eq(v___x_1449_, v___x_1450_);
lean_dec(v___x_1449_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_inc_ref(v_s_1440_);
v___x_1452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1452_, 0, v_s_1440_);
lean_ctor_set(v___x_1452_, 1, v_startInclusive_1447_);
lean_ctor_set(v___x_1452_, 2, v_endExclusive_1448_);
v___x_1453_ = lean_array_push(v_b_1444_, v___x_1452_);
v_a_1443_ = v_it_1446_;
v_b_1444_ = v___x_1453_;
goto _start;
}
else
{
lean_dec(v_endExclusive_1448_);
lean_dec(v_startInclusive_1447_);
v_a_1443_ = v_it_1446_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object* v_s_1486_, lean_object* v___x_1487_, lean_object* v___x_1488_, lean_object* v_a_1489_, lean_object* v_b_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1486_, v___x_1487_, v___x_1488_, v_a_1489_, v_b_1490_);
lean_dec_ref(v___x_1487_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t v_mode_1498_, lean_object* v_s_1499_){
_start:
{
switch(v_mode_1498_)
{
case 0:
{
return v_s_1499_;
}
case 1:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1500_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = lean_string_utf8_byte_size(v_s_1499_);
v___x_1503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1503_, 0, v_s_1499_);
lean_ctor_set(v___x_1503_, 1, v___x_1501_);
lean_ctor_set(v___x_1503_, 2, v___x_1502_);
v___x_1504_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v___x_1503_, v___x_1500_);
return v___x_1504_;
}
default: 
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0));
v___x_1507_ = lean_string_utf8_byte_size(v_s_1499_);
lean_inc_ref(v_s_1499_);
v___x_1508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1508_, 0, v_s_1499_);
lean_ctor_set(v___x_1508_, 1, v___x_1505_);
lean_ctor_set(v___x_1508_, 2, v___x_1507_);
v___x_1509_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0);
v___x_1510_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1));
v___x_1511_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1499_, v___x_1508_, v___x_1507_, v___x_1509_, v___x_1510_);
lean_dec_ref_known(v___x_1508_, 3);
v___x_1512_ = lean_array_to_list(v___x_1511_);
v___x_1513_ = l_String_Slice_intercalate(v___x_1506_, v___x_1512_);
lean_dec(v___x_1512_);
return v___x_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object* v_mode_1514_, lean_object* v_s_1515_){
_start:
{
uint8_t v_mode_boxed_1516_; lean_object* v_res_1517_; 
v_mode_boxed_1516_ = lean_unbox(v_mode_1514_);
v_res_1517_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v_mode_boxed_1516_, v_s_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object* v_s_1518_, lean_object* v_pattern_1519_, lean_object* v_replacement_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1518_, v_replacement_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object* v_s_1522_, lean_object* v_pattern_1523_, lean_object* v_replacement_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(v_s_1522_, v_pattern_1523_, v_replacement_1524_);
lean_dec_ref(v_replacement_1524_);
lean_dec_ref(v_pattern_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object* v_s_1526_, lean_object* v___x_1527_, lean_object* v___x_1528_, lean_object* v_inst_1529_, lean_object* v_R_1530_, lean_object* v_a_1531_, lean_object* v_b_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1526_, v___x_1527_, v___x_1528_, v_a_1531_, v_b_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___boxed(lean_object* v_s_1534_, lean_object* v___x_1535_, lean_object* v___x_1536_, lean_object* v_inst_1537_, lean_object* v_R_1538_, lean_object* v_a_1539_, lean_object* v_b_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(v_s_1534_, v___x_1535_, v___x_1536_, v_inst_1537_, v_R_1538_, v_a_1539_, v_b_1540_);
lean_dec_ref(v___x_1535_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(lean_object* v_hi_1542_, lean_object* v_pivot_1543_, lean_object* v_as_1544_, lean_object* v_i_1545_, lean_object* v_k_1546_){
_start:
{
uint8_t v___x_1547_; 
v___x_1547_ = lean_nat_dec_lt(v_k_1546_, v_hi_1542_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v_k_1546_);
v___x_1548_ = lean_array_fswap(v_as_1544_, v_i_1545_, v_hi_1542_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_i_1545_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = lean_array_fget_borrowed(v_as_1544_, v_k_1546_);
v___x_1551_ = lean_string_dec_lt(v___x_1550_, v_pivot_1543_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = lean_nat_add(v_k_1546_, v___x_1552_);
lean_dec(v_k_1546_);
v_k_1546_ = v___x_1553_;
goto _start;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1555_ = lean_array_fswap(v_as_1544_, v_i_1545_, v_k_1546_);
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_add(v_i_1545_, v___x_1556_);
lean_dec(v_i_1545_);
v___x_1558_ = lean_nat_add(v_k_1546_, v___x_1556_);
lean_dec(v_k_1546_);
v_as_1544_ = v___x_1555_;
v_i_1545_ = v___x_1557_;
v_k_1546_ = v___x_1558_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg___boxed(lean_object* v_hi_1560_, lean_object* v_pivot_1561_, lean_object* v_as_1562_, lean_object* v_i_1563_, lean_object* v_k_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1560_, v_pivot_1561_, v_as_1562_, v_i_1563_, v_k_1564_);
lean_dec_ref(v_pivot_1561_);
lean_dec(v_hi_1560_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object* v_n_1566_, lean_object* v_as_1567_, lean_object* v_lo_1568_, lean_object* v_hi_1569_){
_start:
{
lean_object* v___y_1571_; uint8_t v___x_1581_; 
v___x_1581_ = lean_nat_dec_lt(v_lo_1568_, v_hi_1569_);
if (v___x_1581_ == 0)
{
lean_dec(v_lo_1568_);
return v_as_1567_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v_mid_1584_; lean_object* v___y_1586_; lean_object* v___y_1592_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1582_ = lean_nat_add(v_lo_1568_, v_hi_1569_);
v___x_1583_ = lean_unsigned_to_nat(1u);
v_mid_1584_ = lean_nat_shiftr(v___x_1582_, v___x_1583_);
lean_dec(v___x_1582_);
v___x_1597_ = lean_array_fget_borrowed(v_as_1567_, v_mid_1584_);
v___x_1598_ = lean_array_fget_borrowed(v_as_1567_, v_lo_1568_);
v___x_1599_ = lean_string_dec_lt(v___x_1597_, v___x_1598_);
if (v___x_1599_ == 0)
{
v___y_1592_ = v_as_1567_;
goto v___jp_1591_;
}
else
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_array_fswap(v_as_1567_, v_lo_1568_, v_mid_1584_);
v___y_1592_ = v___x_1600_;
goto v___jp_1591_;
}
v___jp_1585_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1587_ = lean_array_fget_borrowed(v___y_1586_, v_mid_1584_);
v___x_1588_ = lean_array_fget_borrowed(v___y_1586_, v_hi_1569_);
v___x_1589_ = lean_string_dec_lt(v___x_1587_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_dec(v_mid_1584_);
v___y_1571_ = v___y_1586_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_array_fswap(v___y_1586_, v_mid_1584_, v_hi_1569_);
lean_dec(v_mid_1584_);
v___y_1571_ = v___x_1590_;
goto v___jp_1570_;
}
}
v___jp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1593_ = lean_array_fget_borrowed(v___y_1592_, v_hi_1569_);
v___x_1594_ = lean_array_fget_borrowed(v___y_1592_, v_lo_1568_);
v___x_1595_ = lean_string_dec_lt(v___x_1593_, v___x_1594_);
if (v___x_1595_ == 0)
{
v___y_1586_ = v___y_1592_;
goto v___jp_1585_;
}
else
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_array_fswap(v___y_1592_, v_lo_1568_, v_hi_1569_);
v___y_1586_ = v___x_1596_;
goto v___jp_1585_;
}
}
}
v___jp_1570_:
{
lean_object* v_pivot_1572_; lean_object* v___x_1573_; lean_object* v_fst_1574_; lean_object* v_snd_1575_; uint8_t v___x_1576_; 
v_pivot_1572_ = lean_array_fget(v___y_1571_, v_hi_1569_);
lean_inc_n(v_lo_1568_, 2);
v___x_1573_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1569_, v_pivot_1572_, v___y_1571_, v_lo_1568_, v_lo_1568_);
lean_dec(v_pivot_1572_);
v_fst_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_fst_1574_);
v_snd_1575_ = lean_ctor_get(v___x_1573_, 1);
lean_inc(v_snd_1575_);
lean_dec_ref(v___x_1573_);
v___x_1576_ = lean_nat_dec_le(v_hi_1569_, v_fst_1574_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1566_, v_snd_1575_, v_lo_1568_, v_fst_1574_);
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_add(v_fst_1574_, v___x_1578_);
lean_dec(v_fst_1574_);
v_as_1567_ = v___x_1577_;
v_lo_1568_ = v___x_1579_;
goto _start;
}
else
{
lean_dec(v_fst_1574_);
lean_dec(v_lo_1568_);
return v_snd_1575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object* v_n_1601_, lean_object* v_as_1602_, lean_object* v_lo_1603_, lean_object* v_hi_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1601_, v_as_1602_, v_lo_1603_, v_hi_1604_);
lean_dec(v_hi_1604_);
lean_dec(v_n_1601_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t v_mode_1606_, lean_object* v_msgs_1607_){
_start:
{
if (v_mode_1606_ == 0)
{
return v_msgs_1607_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1608_ = lean_array_mk(v_msgs_1607_);
v___x_1609_ = lean_array_get_size(v___x_1608_);
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_nat_dec_eq(v___x_1609_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___y_1620_; uint8_t v___x_1622_; 
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_nat_sub(v___x_1609_, v___x_1617_);
v___x_1622_ = lean_nat_dec_le(v___x_1615_, v___x_1618_);
if (v___x_1622_ == 0)
{
lean_inc(v___x_1618_);
v___y_1620_ = v___x_1618_;
goto v___jp_1619_;
}
else
{
v___y_1620_ = v___x_1615_;
goto v___jp_1619_;
}
v___jp_1619_:
{
uint8_t v___x_1621_; 
v___x_1621_ = lean_nat_dec_le(v___y_1620_, v___x_1618_);
if (v___x_1621_ == 0)
{
lean_dec(v___x_1618_);
lean_inc(v___y_1620_);
v___y_1611_ = v___y_1620_;
v___y_1612_ = v___y_1620_;
goto v___jp_1610_;
}
else
{
v___y_1611_ = v___y_1620_;
v___y_1612_ = v___x_1618_;
goto v___jp_1610_;
}
}
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_array_to_list(v___x_1608_);
return v___x_1623_;
}
v___jp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v___x_1609_, v___x_1608_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
v___x_1614_ = lean_array_to_list(v___x_1613_);
return v___x_1614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* v_mode_1624_, lean_object* v_msgs_1625_){
_start:
{
uint8_t v_mode_boxed_1626_; lean_object* v_res_1627_; 
v_mode_boxed_1626_ = lean_unbox(v_mode_1624_);
v_res_1627_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_boxed_1626_, v_msgs_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object* v_n_1628_, lean_object* v_as_1629_, lean_object* v_lo_1630_, lean_object* v_hi_1631_, lean_object* v_w_1632_, lean_object* v_hlo_1633_, lean_object* v_hhi_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1628_, v_as_1629_, v_lo_1630_, v_hi_1631_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object* v_n_1636_, lean_object* v_as_1637_, lean_object* v_lo_1638_, lean_object* v_hi_1639_, lean_object* v_w_1640_, lean_object* v_hlo_1641_, lean_object* v_hhi_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(v_n_1636_, v_as_1637_, v_lo_1638_, v_hi_1639_, v_w_1640_, v_hlo_1641_, v_hhi_1642_);
lean_dec(v_hi_1639_);
lean_dec(v_n_1636_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(lean_object* v_n_1644_, lean_object* v_lo_1645_, lean_object* v_hi_1646_, lean_object* v_hhi_1647_, lean_object* v_pivot_1648_, lean_object* v_as_1649_, lean_object* v_i_1650_, lean_object* v_k_1651_, lean_object* v_ilo_1652_, lean_object* v_ik_1653_, lean_object* v_w_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1646_, v_pivot_1648_, v_as_1649_, v_i_1650_, v_k_1651_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___boxed(lean_object* v_n_1656_, lean_object* v_lo_1657_, lean_object* v_hi_1658_, lean_object* v_hhi_1659_, lean_object* v_pivot_1660_, lean_object* v_as_1661_, lean_object* v_i_1662_, lean_object* v_k_1663_, lean_object* v_ilo_1664_, lean_object* v_ik_1665_, lean_object* v_w_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(v_n_1656_, v_lo_1657_, v_hi_1658_, v_hhi_1659_, v_pivot_1660_, v_as_1661_, v_i_1662_, v_k_1663_, v_ilo_1664_, v_ik_1665_, v_w_1666_);
lean_dec_ref(v_pivot_1660_);
lean_dec(v_hi_1658_);
lean_dec(v_lo_1657_);
lean_dec(v_n_1656_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object* v_as_1668_, size_t v_i_1669_, size_t v_stop_1670_, lean_object* v_b_1671_){
_start:
{
uint8_t v___x_1672_; 
v___x_1672_ = lean_usize_dec_eq(v_i_1669_, v_stop_1670_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v_diagnostics_1674_; lean_object* v_msgLog_1675_; lean_object* v___x_1676_; size_t v___x_1677_; size_t v___x_1678_; 
v___x_1673_ = lean_array_uget_borrowed(v_as_1668_, v_i_1669_);
v_diagnostics_1674_ = lean_ctor_get(v___x_1673_, 1);
v_msgLog_1675_ = lean_ctor_get(v_diagnostics_1674_, 0);
lean_inc_ref(v_msgLog_1675_);
v___x_1676_ = l_Lean_MessageLog_append(v_b_1671_, v_msgLog_1675_);
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_add(v_i_1669_, v___x_1677_);
v_i_1669_ = v___x_1678_;
v_b_1671_ = v___x_1676_;
goto _start;
}
else
{
return v_b_1671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0___boxed(lean_object* v_as_1680_, lean_object* v_i_1681_, lean_object* v_stop_1682_, lean_object* v_b_1683_){
_start:
{
size_t v_i_boxed_1684_; size_t v_stop_boxed_1685_; lean_object* v_res_1686_; 
v_i_boxed_1684_ = lean_unbox_usize(v_i_1681_);
lean_dec(v_i_1681_);
v_stop_boxed_1685_ = lean_unbox_usize(v_stop_1682_);
lean_dec(v_stop_1682_);
v_res_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v_as_1680_, v_i_boxed_1684_, v_stop_boxed_1685_, v_b_1683_);
lean_dec_ref(v_as_1680_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object* v_as_1687_, size_t v_i_1688_, size_t v_stop_1689_, lean_object* v_b_1690_){
_start:
{
lean_object* v___y_1692_; uint8_t v___x_1696_; 
v___x_1696_ = lean_usize_dec_eq(v_i_1688_, v_stop_1689_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1697_ = lean_array_uget_borrowed(v_as_1687_, v_i_1688_);
v___x_1698_ = l_Lean_MessageLog_empty;
lean_inc(v___x_1697_);
v___x_1699_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1697_);
v___x_1700_ = l_Lean_Language_SnapshotTree_getAll(v___x_1699_);
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = lean_array_get_size(v___x_1700_);
v___x_1703_ = lean_nat_dec_lt(v___x_1701_, v___x_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
lean_dec_ref(v___x_1700_);
v___x_1704_ = l_Lean_MessageLog_append(v_b_1690_, v___x_1698_);
v___y_1692_ = v___x_1704_;
goto v___jp_1691_;
}
else
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_nat_dec_le(v___x_1702_, v___x_1702_);
if (v___x_1705_ == 0)
{
if (v___x_1703_ == 0)
{
lean_object* v___x_1706_; 
lean_dec_ref(v___x_1700_);
v___x_1706_ = l_Lean_MessageLog_append(v_b_1690_, v___x_1698_);
v___y_1692_ = v___x_1706_;
goto v___jp_1691_;
}
else
{
size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = lean_usize_of_nat(v___x_1702_);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1700_, v___x_1707_, v___x_1708_, v___x_1698_);
lean_dec_ref(v___x_1700_);
v___x_1710_ = l_Lean_MessageLog_append(v_b_1690_, v___x_1709_);
v___y_1692_ = v___x_1710_;
goto v___jp_1691_;
}
}
else
{
size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1711_ = ((size_t)0ULL);
v___x_1712_ = lean_usize_of_nat(v___x_1702_);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1700_, v___x_1711_, v___x_1712_, v___x_1698_);
lean_dec_ref(v___x_1700_);
v___x_1714_ = l_Lean_MessageLog_append(v_b_1690_, v___x_1713_);
v___y_1692_ = v___x_1714_;
goto v___jp_1691_;
}
}
}
else
{
return v_b_1690_;
}
v___jp_1691_:
{
size_t v___x_1693_; size_t v___x_1694_; 
v___x_1693_ = ((size_t)1ULL);
v___x_1694_ = lean_usize_add(v_i_1688_, v___x_1693_);
v_i_1688_ = v___x_1694_;
v_b_1690_ = v___y_1692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1___boxed(lean_object* v_as_1715_, lean_object* v_i_1716_, lean_object* v_stop_1717_, lean_object* v_b_1718_){
_start:
{
size_t v_i_boxed_1719_; size_t v_stop_boxed_1720_; lean_object* v_res_1721_; 
v_i_boxed_1719_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_stop_boxed_1720_ = lean_unbox_usize(v_stop_1717_);
lean_dec(v_stop_1717_);
v_res_1721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_as_1715_, v_i_boxed_1719_, v_stop_boxed_1720_, v_b_1718_);
lean_dec_ref(v_as_1715_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object* v_cmd_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_fileName_1728_; lean_object* v_fileMap_1729_; lean_object* v_currRecDepth_1730_; lean_object* v_cmdPos_1731_; lean_object* v_macroStack_1732_; lean_object* v_quotContext_x3f_1733_; lean_object* v_currMacroScope_1734_; lean_object* v_ref_1735_; lean_object* v_cancelTk_x3f_1736_; uint8_t v_suppressElabErrors_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_fileName_1728_ = lean_ctor_get(v_a_1725_, 0);
v_fileMap_1729_ = lean_ctor_get(v_a_1725_, 1);
v_currRecDepth_1730_ = lean_ctor_get(v_a_1725_, 2);
v_cmdPos_1731_ = lean_ctor_get(v_a_1725_, 3);
v_macroStack_1732_ = lean_ctor_get(v_a_1725_, 4);
v_quotContext_x3f_1733_ = lean_ctor_get(v_a_1725_, 5);
v_currMacroScope_1734_ = lean_ctor_get(v_a_1725_, 6);
v_ref_1735_ = lean_ctor_get(v_a_1725_, 7);
v_cancelTk_x3f_1736_ = lean_ctor_get(v_a_1725_, 9);
v_suppressElabErrors_1737_ = lean_ctor_get_uint8(v_a_1725_, sizeof(void*)*10);
v___x_1738_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1736_);
lean_inc(v_ref_1735_);
lean_inc(v_currMacroScope_1734_);
lean_inc(v_quotContext_x3f_1733_);
lean_inc(v_macroStack_1732_);
lean_inc(v_cmdPos_1731_);
lean_inc(v_currRecDepth_1730_);
lean_inc_ref(v_fileMap_1729_);
lean_inc_ref(v_fileName_1728_);
v___x_1739_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1739_, 0, v_fileName_1728_);
lean_ctor_set(v___x_1739_, 1, v_fileMap_1729_);
lean_ctor_set(v___x_1739_, 2, v_currRecDepth_1730_);
lean_ctor_set(v___x_1739_, 3, v_cmdPos_1731_);
lean_ctor_set(v___x_1739_, 4, v_macroStack_1732_);
lean_ctor_set(v___x_1739_, 5, v_quotContext_x3f_1733_);
lean_ctor_set(v___x_1739_, 6, v_currMacroScope_1734_);
lean_ctor_set(v___x_1739_, 7, v_ref_1735_);
lean_ctor_set(v___x_1739_, 8, v___x_1738_);
lean_ctor_set(v___x_1739_, 9, v_cancelTk_x3f_1736_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*10, v_suppressElabErrors_1737_);
v___x_1740_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1724_, v___x_1739_, v_a_1726_);
lean_dec_ref_known(v___x_1739_, 10);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1788_; 
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; 
v_unused_1789_ = lean_ctor_get(v___x_1740_, 0);
lean_dec(v_unused_1789_);
v___x_1742_ = v___x_1740_;
v_isShared_1743_ = v_isSharedCheck_1788_;
goto v_resetjp_1741_;
}
else
{
lean_dec(v___x_1740_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1788_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v_messages_1746_; lean_object* v___y_1748_; lean_object* v_snapshotTasks_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1744_ = lean_st_ref_get(v_a_1726_);
v___x_1745_ = lean_st_ref_get(v_a_1726_);
v_messages_1746_ = lean_ctor_get(v___x_1744_, 1);
lean_inc_ref(v_messages_1746_);
lean_dec(v___x_1744_);
v_snapshotTasks_1776_ = lean_ctor_get(v___x_1745_, 10);
lean_inc_ref(v_snapshotTasks_1776_);
lean_dec(v___x_1745_);
v___x_1777_ = l_Lean_MessageLog_empty;
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_array_get_size(v_snapshotTasks_1776_);
v___x_1780_ = lean_nat_dec_lt(v___x_1778_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_dec_ref(v_snapshotTasks_1776_);
v___y_1748_ = v___x_1777_;
goto v___jp_1747_;
}
else
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_nat_dec_le(v___x_1779_, v___x_1779_);
if (v___x_1781_ == 0)
{
if (v___x_1780_ == 0)
{
lean_dec_ref(v_snapshotTasks_1776_);
v___y_1748_ = v___x_1777_;
goto v___jp_1747_;
}
else
{
size_t v___x_1782_; size_t v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = ((size_t)0ULL);
v___x_1783_ = lean_usize_of_nat(v___x_1779_);
v___x_1784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1776_, v___x_1782_, v___x_1783_, v___x_1777_);
lean_dec_ref(v_snapshotTasks_1776_);
v___y_1748_ = v___x_1784_;
goto v___jp_1747_;
}
}
else
{
size_t v___x_1785_; size_t v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = ((size_t)0ULL);
v___x_1786_ = lean_usize_of_nat(v___x_1779_);
v___x_1787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1776_, v___x_1785_, v___x_1786_, v___x_1777_);
lean_dec_ref(v_snapshotTasks_1776_);
v___y_1748_ = v___x_1787_;
goto v___jp_1747_;
}
}
v___jp_1747_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v_env_1751_; lean_object* v_messages_1752_; lean_object* v_scopes_1753_; lean_object* v_usedQuotCtxts_1754_; lean_object* v_nextMacroScope_1755_; lean_object* v_maxRecDepth_1756_; lean_object* v_ngen_1757_; lean_object* v_auxDeclNGen_1758_; lean_object* v_infoState_1759_; lean_object* v_traceState_1760_; lean_object* v_prevLinterStates_1761_; lean_object* v_codeQualityEntryTasks_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1774_; 
v___x_1749_ = l_Lean_MessageLog_append(v_messages_1746_, v___y_1748_);
v___x_1750_ = lean_st_ref_take(v_a_1726_);
v_env_1751_ = lean_ctor_get(v___x_1750_, 0);
v_messages_1752_ = lean_ctor_get(v___x_1750_, 1);
v_scopes_1753_ = lean_ctor_get(v___x_1750_, 2);
v_usedQuotCtxts_1754_ = lean_ctor_get(v___x_1750_, 3);
v_nextMacroScope_1755_ = lean_ctor_get(v___x_1750_, 4);
v_maxRecDepth_1756_ = lean_ctor_get(v___x_1750_, 5);
v_ngen_1757_ = lean_ctor_get(v___x_1750_, 6);
v_auxDeclNGen_1758_ = lean_ctor_get(v___x_1750_, 7);
v_infoState_1759_ = lean_ctor_get(v___x_1750_, 8);
v_traceState_1760_ = lean_ctor_get(v___x_1750_, 9);
v_prevLinterStates_1761_ = lean_ctor_get(v___x_1750_, 11);
v_codeQualityEntryTasks_1762_ = lean_ctor_get(v___x_1750_, 12);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; 
v_unused_1775_ = lean_ctor_get(v___x_1750_, 10);
lean_dec(v_unused_1775_);
v___x_1764_ = v___x_1750_;
v_isShared_1765_ = v_isSharedCheck_1774_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1762_);
lean_inc(v_prevLinterStates_1761_);
lean_inc(v_traceState_1760_);
lean_inc(v_infoState_1759_);
lean_inc(v_auxDeclNGen_1758_);
lean_inc(v_ngen_1757_);
lean_inc(v_maxRecDepth_1756_);
lean_inc(v_nextMacroScope_1755_);
lean_inc(v_usedQuotCtxts_1754_);
lean_inc(v_scopes_1753_);
lean_inc(v_messages_1752_);
lean_inc(v_env_1751_);
lean_dec(v___x_1750_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1774_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1766_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 10, v___x_1766_);
v___x_1768_ = v___x_1764_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_env_1751_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_messages_1752_);
lean_ctor_set(v_reuseFailAlloc_1773_, 2, v_scopes_1753_);
lean_ctor_set(v_reuseFailAlloc_1773_, 3, v_usedQuotCtxts_1754_);
lean_ctor_set(v_reuseFailAlloc_1773_, 4, v_nextMacroScope_1755_);
lean_ctor_set(v_reuseFailAlloc_1773_, 5, v_maxRecDepth_1756_);
lean_ctor_set(v_reuseFailAlloc_1773_, 6, v_ngen_1757_);
lean_ctor_set(v_reuseFailAlloc_1773_, 7, v_auxDeclNGen_1758_);
lean_ctor_set(v_reuseFailAlloc_1773_, 8, v_infoState_1759_);
lean_ctor_set(v_reuseFailAlloc_1773_, 9, v_traceState_1760_);
lean_ctor_set(v_reuseFailAlloc_1773_, 10, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1773_, 11, v_prevLinterStates_1761_);
lean_ctor_set(v_reuseFailAlloc_1773_, 12, v_codeQualityEntryTasks_1762_);
v___x_1768_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1769_ = lean_st_ref_put(v_a_1726_, v___x_1768_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1749_);
v___x_1771_ = v___x_1742_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1749_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_a_1790_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1740_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1740_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1798_, v_a_1799_, v_a_1800_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
return v_res_1802_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1803_, lean_object* v_opt_1804_){
_start:
{
lean_object* v_name_1805_; lean_object* v_defValue_1806_; lean_object* v_map_1807_; lean_object* v___x_1808_; 
v_name_1805_ = lean_ctor_get(v_opt_1804_, 0);
v_defValue_1806_ = lean_ctor_get(v_opt_1804_, 1);
v_map_1807_ = lean_ctor_get(v_opts_1803_, 0);
v___x_1808_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1807_, v_name_1805_);
if (lean_obj_tag(v___x_1808_) == 0)
{
uint8_t v___x_1809_; 
v___x_1809_ = lean_unbox(v_defValue_1806_);
return v___x_1809_;
}
else
{
lean_object* v_val_1810_; 
v_val_1810_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_val_1810_);
lean_dec_ref_known(v___x_1808_, 1);
if (lean_obj_tag(v_val_1810_) == 1)
{
uint8_t v_v_1811_; 
v_v_1811_ = lean_ctor_get_uint8(v_val_1810_, 0);
lean_dec_ref_known(v_val_1810_, 0);
return v_v_1811_;
}
else
{
uint8_t v___x_1812_; 
lean_dec(v_val_1810_);
v___x_1812_ = lean_unbox(v_defValue_1806_);
return v___x_1812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1813_, lean_object* v_opt_1814_){
_start:
{
uint8_t v_res_1815_; lean_object* v_r_1816_; 
v_res_1815_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1813_, v_opt_1814_);
lean_dec_ref(v_opt_1814_);
lean_dec_ref(v_opts_1813_);
v_r_1816_ = lean_box(v_res_1815_);
return v_r_1816_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg(){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___closed__0));
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___boxed(lean_object* v___dummy_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v_res_1822_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1826_);
lean_dec_ref(v_s_1826_);
return v_res_1827_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_box(1);
v___x_1829_ = l_Lean_MessageData_ofFormat(v___x_1828_);
return v___x_1829_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1834_ = l_Lean_MessageData_ofFormat(v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
if (lean_obj_tag(v_x_1836_) == 0)
{
return v_x_1835_;
}
else
{
lean_object* v_head_1837_; lean_object* v_tail_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1860_; 
v_head_1837_ = lean_ctor_get(v_x_1836_, 0);
v_tail_1838_ = lean_ctor_get(v_x_1836_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_x_1836_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1840_ = v_x_1836_;
v_isShared_1841_ = v_isSharedCheck_1860_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_tail_1838_);
lean_inc(v_head_1837_);
lean_dec(v_x_1836_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1860_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_before_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1858_; 
v_before_1842_ = lean_ctor_get(v_head_1837_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_head_1837_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v_head_1837_, 1);
lean_dec(v_unused_1859_);
v___x_1844_ = v_head_1837_;
v_isShared_1845_ = v_isSharedCheck_1858_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_before_1842_);
lean_dec(v_head_1837_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1858_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1845_ == 0)
{
lean_ctor_set_tag(v___x_1844_, 7);
lean_ctor_set(v___x_1844_, 1, v___x_1846_);
lean_ctor_set(v___x_1844_, 0, v_x_1835_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_x_1835_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1841_ == 0)
{
lean_ctor_set_tag(v___x_1840_, 7);
lean_ctor_set(v___x_1840_, 1, v___x_1849_);
lean_ctor_set(v___x_1840_, 0, v___x_1848_);
v___x_1851_ = v___x_1840_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = l_Lean_MessageData_ofSyntax(v_before_1842_);
v___x_1853_ = l_Lean_indentD(v___x_1852_);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1851_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v_x_1835_ = v___x_1854_;
v_x_1836_ = v_tail_1838_;
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
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1865_ = l_Lean_MessageData_ofFormat(v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1866_, lean_object* v_macroStack_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v_scopes_1872_; lean_object* v___x_1873_; lean_object* v_opts_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1870_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1871_ = lean_st_ref_get(v___y_1868_);
v_scopes_1872_ = lean_ctor_get(v___x_1871_, 2);
lean_inc(v_scopes_1872_);
lean_dec(v___x_1871_);
v___x_1873_ = l_List_head_x21___redArg(v___x_1870_, v_scopes_1872_);
lean_dec(v_scopes_1872_);
v_opts_1874_ = lean_ctor_get(v___x_1873_, 1);
lean_inc_ref(v_opts_1874_);
lean_dec(v___x_1873_);
v___x_1875_ = l_Lean_Elab_pp_macroStack;
v___x_1876_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1874_, v___x_1875_);
lean_dec_ref(v_opts_1874_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; 
lean_dec(v_macroStack_1867_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v_msgData_1866_);
return v___x_1877_;
}
else
{
if (lean_obj_tag(v_macroStack_1867_) == 0)
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_msgData_1866_);
return v___x_1878_;
}
else
{
lean_object* v_head_1879_; lean_object* v_after_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1895_; 
v_head_1879_ = lean_ctor_get(v_macroStack_1867_, 0);
lean_inc(v_head_1879_);
v_after_1880_ = lean_ctor_get(v_head_1879_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_head_1879_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v_head_1879_, 0);
lean_dec(v_unused_1896_);
v___x_1882_ = v_head_1879_;
v_isShared_1883_ = v_isSharedCheck_1895_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_after_1880_);
lean_dec(v_head_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1895_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1884_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 7);
lean_ctor_set(v___x_1882_, 1, v___x_1884_);
lean_ctor_set(v___x_1882_, 0, v_msgData_1866_);
v___x_1886_ = v___x_1882_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_msgData_1866_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v_msgData_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1887_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l_Lean_MessageData_ofSyntax(v_after_1880_);
v___x_1890_ = l_Lean_indentD(v___x_1889_);
v_msgData_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1891_, 0, v___x_1888_);
lean_ctor_set(v_msgData_1891_, 1, v___x_1890_);
v___x_1892_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1891_, v_macroStack_1867_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1897_, lean_object* v_macroStack_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1897_, v_macroStack_1898_, v___y_1899_);
lean_dec(v___y_1899_);
return v_res_1901_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1902_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
lean_ctor_set(v___x_1907_, 2, v___x_1906_);
lean_ctor_set(v___x_1907_, 3, v___x_1906_);
lean_ctor_set(v___x_1907_, 4, v___x_1905_);
lean_ctor_set(v___x_1907_, 5, v___x_1905_);
lean_ctor_set(v___x_1907_, 6, v___x_1905_);
lean_ctor_set(v___x_1907_, 7, v___x_1905_);
lean_ctor_set(v___x_1907_, 8, v___x_1905_);
lean_ctor_set(v___x_1907_, 9, v___x_1905_);
lean_ctor_set(v___x_1907_, 10, v___x_1905_);
return v___x_1907_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_unsigned_to_nat(32u);
v___x_1909_ = lean_mk_empty_array_with_capacity(v___x_1908_);
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
return v___x_1910_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1911_ = ((size_t)5ULL);
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = lean_unsigned_to_nat(32u);
v___x_1914_ = lean_mk_empty_array_with_capacity(v___x_1913_);
v___x_1915_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1916_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v___x_1914_);
lean_ctor_set(v___x_1916_, 2, v___x_1912_);
lean_ctor_set(v___x_1916_, 3, v___x_1912_);
lean_ctor_set_usize(v___x_1916_, 4, v___x_1911_);
return v___x_1916_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1917_ = lean_box(1);
v___x_1918_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1919_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1918_);
lean_ctor_set(v___x_1920_, 2, v___x_1917_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; lean_object* v_env_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v_scopes_1928_; lean_object* v___x_1929_; lean_object* v_opts_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1924_ = lean_st_ref_get(v___y_1922_);
v_env_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc_ref(v_env_1925_);
lean_dec(v___x_1924_);
v___x_1926_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1927_ = lean_st_ref_get(v___y_1922_);
v_scopes_1928_ = lean_ctor_get(v___x_1927_, 2);
lean_inc(v_scopes_1928_);
lean_dec(v___x_1927_);
v___x_1929_ = l_List_head_x21___redArg(v___x_1926_, v_scopes_1928_);
lean_dec(v_scopes_1928_);
v_opts_1930_ = lean_ctor_get(v___x_1929_, 1);
lean_inc_ref(v_opts_1930_);
lean_dec(v___x_1929_);
v___x_1931_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1932_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1933_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1933_, 0, v_env_1925_);
lean_ctor_set(v___x_1933_, 1, v___x_1931_);
lean_ctor_set(v___x_1933_, 2, v___x_1932_);
lean_ctor_set(v___x_1933_, 3, v_opts_1930_);
v___x_1934_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v_msgData_1921_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1936_, v___y_1937_);
lean_dec(v___y_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_Elab_Command_getRef___redArg(v___y_1941_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v_macroStack_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_a_1949_; lean_object* v___x_1950_; lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1959_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v_macroStack_1946_ = lean_ctor_get(v___y_1941_, 4);
v___x_1947_ = l_Lean_Elab_getBetterRef(v_a_1945_, v_macroStack_1946_);
lean_dec(v_a_1945_);
v___x_1948_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1940_, v___y_1942_);
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref(v___x_1948_);
lean_inc(v_macroStack_1946_);
v___x_1950_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1949_, v_macroStack_1946_, v___y_1942_);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1947_);
lean_ctor_set(v___x_1955_, 1, v_a_1951_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set_tag(v___x_1953_, 1);
lean_ctor_set(v___x_1953_, 0, v___x_1955_);
v___x_1957_ = v___x_1953_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec_ref(v_msg_1940_);
v_a_1960_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1944_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1944_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_1973_, lean_object* v_msg_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Elab_Command_getRef___redArg(v___y_1975_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v_fileName_1980_; lean_object* v_fileMap_1981_; lean_object* v_currRecDepth_1982_; lean_object* v_cmdPos_1983_; lean_object* v_macroStack_1984_; lean_object* v_quotContext_x3f_1985_; lean_object* v_currMacroScope_1986_; lean_object* v_snap_x3f_1987_; lean_object* v_cancelTk_x3f_1988_; uint8_t v_suppressElabErrors_1989_; lean_object* v_ref_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v_fileName_1980_ = lean_ctor_get(v___y_1975_, 0);
v_fileMap_1981_ = lean_ctor_get(v___y_1975_, 1);
v_currRecDepth_1982_ = lean_ctor_get(v___y_1975_, 2);
v_cmdPos_1983_ = lean_ctor_get(v___y_1975_, 3);
v_macroStack_1984_ = lean_ctor_get(v___y_1975_, 4);
v_quotContext_x3f_1985_ = lean_ctor_get(v___y_1975_, 5);
v_currMacroScope_1986_ = lean_ctor_get(v___y_1975_, 6);
v_snap_x3f_1987_ = lean_ctor_get(v___y_1975_, 8);
v_cancelTk_x3f_1988_ = lean_ctor_get(v___y_1975_, 9);
v_suppressElabErrors_1989_ = lean_ctor_get_uint8(v___y_1975_, sizeof(void*)*10);
v_ref_1990_ = l_Lean_replaceRef(v_ref_1973_, v_a_1979_);
lean_dec(v_a_1979_);
lean_inc(v_cancelTk_x3f_1988_);
lean_inc(v_snap_x3f_1987_);
lean_inc(v_currMacroScope_1986_);
lean_inc(v_quotContext_x3f_1985_);
lean_inc(v_macroStack_1984_);
lean_inc(v_cmdPos_1983_);
lean_inc(v_currRecDepth_1982_);
lean_inc_ref(v_fileMap_1981_);
lean_inc_ref(v_fileName_1980_);
v___x_1991_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1991_, 0, v_fileName_1980_);
lean_ctor_set(v___x_1991_, 1, v_fileMap_1981_);
lean_ctor_set(v___x_1991_, 2, v_currRecDepth_1982_);
lean_ctor_set(v___x_1991_, 3, v_cmdPos_1983_);
lean_ctor_set(v___x_1991_, 4, v_macroStack_1984_);
lean_ctor_set(v___x_1991_, 5, v_quotContext_x3f_1985_);
lean_ctor_set(v___x_1991_, 6, v_currMacroScope_1986_);
lean_ctor_set(v___x_1991_, 7, v_ref_1990_);
lean_ctor_set(v___x_1991_, 8, v_snap_x3f_1987_);
lean_ctor_set(v___x_1991_, 9, v_cancelTk_x3f_1988_);
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*10, v_suppressElabErrors_1989_);
v___x_1992_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1974_, v___x_1991_, v___y_1976_);
lean_dec_ref_known(v___x_1991_, 10);
return v___x_1992_;
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v_msg_1974_);
v_a_1993_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1978_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1978_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_2001_, lean_object* v_msg_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_2001_, v_msg_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v_ref_2001_);
return v_res_2006_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_2009_ = l_Lean_stringToMessageData(v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = l_Lean_Syntax_getArg(v_stx_2013_, v___x_2023_);
if (lean_obj_tag(v___x_2024_) == 1)
{
lean_object* v_kind_2025_; 
v_kind_2025_ = lean_ctor_get(v___x_2024_, 1);
lean_inc(v_kind_2025_);
if (lean_obj_tag(v_kind_2025_) == 1)
{
lean_object* v_pre_2026_; 
v_pre_2026_ = lean_ctor_get(v_kind_2025_, 0);
lean_inc(v_pre_2026_);
if (lean_obj_tag(v_pre_2026_) == 1)
{
lean_object* v_pre_2027_; 
v_pre_2027_ = lean_ctor_get(v_pre_2026_, 0);
lean_inc(v_pre_2027_);
if (lean_obj_tag(v_pre_2027_) == 1)
{
lean_object* v_pre_2028_; 
v_pre_2028_ = lean_ctor_get(v_pre_2027_, 0);
lean_inc(v_pre_2028_);
if (lean_obj_tag(v_pre_2028_) == 1)
{
lean_object* v_pre_2029_; 
v_pre_2029_ = lean_ctor_get(v_pre_2028_, 0);
if (lean_obj_tag(v_pre_2029_) == 0)
{
lean_object* v_args_2030_; lean_object* v_str_2031_; lean_object* v_str_2032_; lean_object* v_str_2033_; lean_object* v_str_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v_args_2030_ = lean_ctor_get(v___x_2024_, 2);
lean_inc_ref(v_args_2030_);
lean_dec_ref_known(v___x_2024_, 3);
v_str_2031_ = lean_ctor_get(v_kind_2025_, 1);
lean_inc_ref(v_str_2031_);
lean_dec_ref_known(v_kind_2025_, 2);
v_str_2032_ = lean_ctor_get(v_pre_2026_, 1);
lean_inc_ref(v_str_2032_);
lean_dec_ref_known(v_pre_2026_, 2);
v_str_2033_ = lean_ctor_get(v_pre_2027_, 1);
lean_inc_ref(v_str_2033_);
lean_dec_ref_known(v_pre_2027_, 2);
v_str_2034_ = lean_ctor_get(v_pre_2028_, 1);
lean_inc_ref(v_str_2034_);
lean_dec_ref_known(v_pre_2028_, 2);
v___x_2035_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_2036_ = lean_string_dec_eq(v_str_2034_, v___x_2035_);
lean_dec_ref(v_str_2034_);
if (v___x_2036_ == 0)
{
lean_dec_ref(v_str_2033_);
lean_dec_ref(v_str_2032_);
lean_dec_ref(v_str_2031_);
lean_dec_ref(v_args_2030_);
goto v___jp_2017_;
}
else
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2038_ = lean_string_dec_eq(v_str_2033_, v___x_2037_);
lean_dec_ref(v_str_2033_);
if (v___x_2038_ == 0)
{
lean_dec_ref(v_str_2032_);
lean_dec_ref(v_str_2031_);
lean_dec_ref(v_args_2030_);
goto v___jp_2017_;
}
else
{
lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2040_ = lean_string_dec_eq(v_str_2032_, v___x_2039_);
lean_dec_ref(v_str_2032_);
if (v___x_2040_ == 0)
{
lean_dec_ref(v_str_2031_);
lean_dec_ref(v_args_2030_);
goto v___jp_2017_;
}
else
{
lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2042_ = lean_string_dec_eq(v_str_2031_, v___x_2041_);
lean_dec_ref(v_str_2031_);
if (v___x_2042_ == 0)
{
lean_dec_ref(v_args_2030_);
goto v___jp_2017_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v___x_2043_ = lean_array_get_size(v_args_2030_);
v___x_2044_ = lean_unsigned_to_nat(2u);
v___x_2045_ = lean_nat_dec_eq(v___x_2043_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_dec_ref(v_args_2030_);
goto v___jp_2017_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = lean_array_fget(v_args_2030_, v___x_2046_);
lean_dec_ref(v_args_2030_);
if (lean_obj_tag(v___x_2047_) == 2)
{
lean_object* v_val_2048_; lean_object* v___x_2049_; 
lean_dec(v_stx_2013_);
v_val_2048_ = lean_ctor_get(v___x_2047_, 1);
lean_inc_ref(v_val_2048_);
lean_dec_ref_known(v___x_2047_, 2);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_val_2048_);
return v___x_2049_;
}
else
{
lean_dec(v___x_2047_);
goto v___jp_2017_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2028_, 2);
lean_dec_ref_known(v_pre_2027_, 2);
lean_dec_ref_known(v_pre_2026_, 2);
lean_dec_ref_known(v_kind_2025_, 2);
lean_dec_ref_known(v___x_2024_, 3);
goto v___jp_2017_;
}
}
else
{
lean_dec_ref_known(v_pre_2027_, 2);
lean_dec(v_pre_2028_);
lean_dec_ref_known(v_pre_2026_, 2);
lean_dec_ref_known(v_kind_2025_, 2);
lean_dec_ref_known(v___x_2024_, 3);
goto v___jp_2017_;
}
}
else
{
lean_dec_ref_known(v_pre_2026_, 2);
lean_dec(v_pre_2027_);
lean_dec_ref_known(v_kind_2025_, 2);
lean_dec_ref_known(v___x_2024_, 3);
goto v___jp_2017_;
}
}
else
{
lean_dec(v_pre_2026_);
lean_dec_ref_known(v_kind_2025_, 2);
lean_dec_ref_known(v___x_2024_, 3);
goto v___jp_2017_;
}
}
else
{
lean_dec_ref_known(v___x_2024_, 3);
lean_dec(v_kind_2025_);
goto v___jp_2017_;
}
}
else
{
lean_dec(v___x_2024_);
goto v___jp_2017_;
}
v___jp_2017_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2018_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2013_);
v___x_2019_ = l_Lean_MessageData_ofSyntax(v_stx_2013_);
v___x_2020_ = l_Lean_indentD(v___x_2019_);
v___x_2021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2018_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2013_, v___x_2021_, v___y_2014_, v___y_2015_);
lean_dec(v_stx_2013_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2055_, size_t v_sz_2056_, size_t v_i_2057_, lean_object* v_b_2058_){
_start:
{
lean_object* v_a_2060_; uint8_t v___x_2064_; 
v___x_2064_ = lean_usize_dec_lt(v_i_2057_, v_sz_2056_);
if (v___x_2064_ == 0)
{
return v_b_2058_;
}
else
{
lean_object* v_a_2065_; lean_object* v_fst_2066_; lean_object* v_snd_2067_; lean_object* v_out_2068_; uint8_t v___x_2069_; 
v_a_2065_ = lean_array_uget_borrowed(v_as_2055_, v_i_2057_);
v_fst_2066_ = lean_ctor_get(v_a_2065_, 0);
v_snd_2067_ = lean_ctor_get(v_a_2065_, 1);
v_out_2068_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2069_ = lean_string_dec_eq(v_snd_2067_, v_out_2068_);
if (v___x_2069_ == 0)
{
uint8_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2070_ = lean_unbox(v_fst_2066_);
v___x_2071_ = l_Lean_Diff_Action_linePrefix(v___x_2070_);
v___x_2072_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2073_ = lean_string_append(v___x_2071_, v___x_2072_);
v___x_2074_ = lean_string_append(v___x_2073_, v_snd_2067_);
v___x_2075_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2076_ = lean_string_append(v___x_2074_, v___x_2075_);
v___x_2077_ = lean_string_append(v_b_2058_, v___x_2076_);
lean_dec_ref(v___x_2076_);
v_a_2060_ = v___x_2077_;
goto v___jp_2059_;
}
else
{
uint8_t v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2078_ = lean_unbox(v_fst_2066_);
v___x_2079_ = l_Lean_Diff_Action_linePrefix(v___x_2078_);
v___x_2080_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2081_ = lean_string_append(v___x_2079_, v___x_2080_);
v___x_2082_ = lean_string_append(v_b_2058_, v___x_2081_);
lean_dec_ref(v___x_2081_);
v_a_2060_ = v___x_2082_;
goto v___jp_2059_;
}
}
v___jp_2059_:
{
size_t v___x_2061_; size_t v___x_2062_; 
v___x_2061_ = ((size_t)1ULL);
v___x_2062_ = lean_usize_add(v_i_2057_, v___x_2061_);
v_i_2057_ = v___x_2062_;
v_b_2058_ = v_a_2060_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2083_, lean_object* v_sz_2084_, lean_object* v_i_2085_, lean_object* v_b_2086_){
_start:
{
size_t v_sz_boxed_2087_; size_t v_i_boxed_2088_; lean_object* v_res_2089_; 
v_sz_boxed_2087_ = lean_unbox_usize(v_sz_2084_);
lean_dec(v_sz_2084_);
v_i_boxed_2088_ = lean_unbox_usize(v_i_2085_);
lean_dec(v_i_2085_);
v_res_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2083_, v_sz_boxed_2087_, v_i_boxed_2088_, v_b_2086_);
lean_dec_ref(v_as_2083_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2090_){
_start:
{
lean_object* v_out_2091_; size_t v_sz_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v_out_2091_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v_sz_2092_ = lean_array_size(v_lines_2090_);
v___x_2093_ = ((size_t)0ULL);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2090_, v_sz_2092_, v___x_2093_, v_out_2091_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2095_);
lean_dec_ref(v_lines_2095_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2097_, lean_object* v_as_x27_2098_, lean_object* v_b_2099_){
_start:
{
if (lean_obj_tag(v_as_x27_2098_) == 0)
{
lean_object* v___x_2101_; 
lean_dec_ref(v_filterFn_2097_);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v_b_2099_);
return v___x_2101_;
}
else
{
lean_object* v_head_2102_; uint8_t v_isSilent_2103_; 
v_head_2102_ = lean_ctor_get(v_as_x27_2098_, 0);
v_isSilent_2103_ = lean_ctor_get_uint8(v_head_2102_, sizeof(void*)*5 + 2);
if (v_isSilent_2103_ == 0)
{
lean_object* v_tail_2104_; lean_object* v_fst_2105_; lean_object* v_snd_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2126_; 
v_tail_2104_ = lean_ctor_get(v_as_x27_2098_, 1);
v_fst_2105_ = lean_ctor_get(v_b_2099_, 0);
v_snd_2106_ = lean_ctor_get(v_b_2099_, 1);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_b_2099_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2108_ = v_b_2099_;
v_isShared_2109_ = v_isSharedCheck_2126_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_snd_2106_);
lean_inc(v_fst_2105_);
lean_dec(v_b_2099_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2126_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
lean_inc_ref(v_filterFn_2097_);
lean_inc(v_head_2102_);
v___x_2110_ = lean_apply_1(v_filterFn_2097_, v_head_2102_);
v___x_2111_ = lean_unbox(v___x_2110_);
switch(v___x_2111_)
{
case 0:
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
lean_inc(v_head_2102_);
v___x_2112_ = l_Lean_MessageLog_add(v_head_2102_, v_fst_2105_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2112_);
v___x_2114_ = v___x_2108_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_snd_2106_);
v___x_2114_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
v_as_x27_2098_ = v_tail_2104_;
v_b_2099_ = v___x_2114_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2118_; 
if (v_isShared_2109_ == 0)
{
v___x_2118_ = v___x_2108_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_fst_2105_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_snd_2106_);
v___x_2118_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
v_as_x27_2098_ = v_tail_2104_;
v_b_2099_ = v___x_2118_;
goto _start;
}
}
default: 
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_inc(v_head_2102_);
v___x_2121_ = l_Lean_MessageLog_add(v_head_2102_, v_snd_2106_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 1, v___x_2121_);
v___x_2123_ = v___x_2108_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_fst_2105_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
v_as_x27_2098_ = v_tail_2104_;
v_b_2099_ = v___x_2123_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2127_; lean_object* v_fst_2128_; lean_object* v_snd_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2137_; 
v_tail_2127_ = lean_ctor_get(v_as_x27_2098_, 1);
v_fst_2128_ = lean_ctor_get(v_b_2099_, 0);
v_snd_2129_ = lean_ctor_get(v_b_2099_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_b_2099_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2131_ = v_b_2099_;
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_snd_2129_);
lean_inc(v_fst_2128_);
lean_dec(v_b_2099_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_fst_2128_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_snd_2129_);
v___x_2134_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
v_as_x27_2098_ = v_tail_2127_;
v_b_2099_ = v___x_2134_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2138_, lean_object* v_as_x27_2139_, lean_object* v_b_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2138_, v_as_x27_2139_, v_b_2140_);
lean_dec(v_as_x27_2139_);
return v_res_2142_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2143_, lean_object* v_a_2144_, uint8_t v_b_2145_){
_start:
{
uint8_t v___x_2146_; 
v___x_2146_ = 0;
switch(lean_obj_tag(v_a_2144_))
{
case 0:
{
lean_object* v_pos_2147_; lean_object* v_startInclusive_2148_; lean_object* v_endExclusive_2149_; lean_object* v___x_2150_; uint8_t v_decide_2151_; 
v_pos_2147_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_pos_2147_);
lean_dec_ref_known(v_a_2144_, 1);
v_startInclusive_2148_ = lean_ctor_get(v_s_2143_, 1);
v_endExclusive_2149_ = lean_ctor_get(v_s_2143_, 2);
v___x_2150_ = lean_nat_sub(v_endExclusive_2149_, v_startInclusive_2148_);
v_decide_2151_ = lean_nat_dec_eq(v_pos_2147_, v___x_2150_);
lean_dec(v___x_2150_);
lean_dec(v_pos_2147_);
if (v_decide_2151_ == 0)
{
uint8_t v___x_2152_; 
v___x_2152_ = 1;
return v___x_2152_;
}
else
{
return v_decide_2151_;
}
}
case 1:
{
lean_object* v_pos_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2166_; 
v_pos_2153_ = lean_ctor_get(v_a_2144_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_a_2144_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2155_ = v_a_2144_;
v_isShared_2156_ = v_isSharedCheck_2166_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_pos_2153_);
lean_dec(v_a_2144_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2166_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v_str_2157_; lean_object* v_startInclusive_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v_str_2157_ = lean_ctor_get(v_s_2143_, 0);
v_startInclusive_2158_ = lean_ctor_get(v_s_2143_, 1);
v___x_2159_ = lean_nat_add(v_startInclusive_2158_, v_pos_2153_);
lean_dec(v_pos_2153_);
v___x_2160_ = lean_string_utf8_next_fast(v_str_2157_, v___x_2159_);
lean_dec(v___x_2159_);
v___x_2161_ = lean_nat_sub(v___x_2160_, v_startInclusive_2158_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2161_);
v___x_2163_ = v___x_2155_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
v_a_2144_ = v___x_2163_;
v_b_2145_ = v___x_2146_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2167_; lean_object* v_table_2168_; lean_object* v_stackPos_2169_; lean_object* v_needlePos_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2225_; 
v_needle_2167_ = lean_ctor_get(v_a_2144_, 0);
v_table_2168_ = lean_ctor_get(v_a_2144_, 1);
v_stackPos_2169_ = lean_ctor_get(v_a_2144_, 2);
v_needlePos_2170_ = lean_ctor_get(v_a_2144_, 3);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_a_2144_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2172_ = v_a_2144_;
v_isShared_2173_ = v_isSharedCheck_2225_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_needlePos_2170_);
lean_inc(v_stackPos_2169_);
lean_inc(v_table_2168_);
lean_inc(v_needle_2167_);
lean_dec(v_a_2144_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2225_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_str_2174_; lean_object* v_startInclusive_2175_; lean_object* v_endExclusive_2176_; lean_object* v_str_2177_; lean_object* v_startInclusive_2178_; lean_object* v_endExclusive_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v_str_2174_ = lean_ctor_get(v_needle_2167_, 0);
v_startInclusive_2175_ = lean_ctor_get(v_needle_2167_, 1);
v_endExclusive_2176_ = lean_ctor_get(v_needle_2167_, 2);
v_str_2177_ = lean_ctor_get(v_s_2143_, 0);
v_startInclusive_2178_ = lean_ctor_get(v_s_2143_, 1);
v_endExclusive_2179_ = lean_ctor_get(v_s_2143_, 2);
v___x_2180_ = lean_nat_sub(v_stackPos_2169_, v_needlePos_2170_);
v___x_2181_ = lean_nat_sub(v_endExclusive_2176_, v_startInclusive_2175_);
v___x_2182_ = lean_nat_add(v___x_2180_, v___x_2181_);
v___x_2183_ = lean_nat_sub(v_endExclusive_2179_, v_startInclusive_2178_);
v___x_2184_ = lean_nat_dec_le(v___x_2182_, v___x_2183_);
lean_dec(v___x_2182_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
lean_dec(v___x_2181_);
lean_del_object(v___x_2172_);
lean_dec(v_needlePos_2170_);
lean_dec(v_stackPos_2169_);
lean_dec_ref(v_table_2168_);
lean_dec_ref(v_needle_2167_);
v___x_2185_ = lean_unsigned_to_nat(1u);
v___x_2186_ = lean_nat_add(v___x_2180_, v___x_2185_);
lean_dec(v___x_2180_);
v___x_2187_ = lean_nat_dec_le(v___x_2186_, v___x_2183_);
lean_dec(v___x_2183_);
lean_dec(v___x_2186_);
if (v___x_2187_ == 0)
{
return v_b_2145_;
}
else
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_box(3);
v_a_2144_ = v___x_2188_;
v_b_2145_ = v___x_2146_;
goto _start;
}
}
else
{
lean_object* v___x_2190_; uint8_t v_stackByte_2191_; lean_object* v___x_2192_; uint8_t v_patByte_2193_; uint8_t v___x_2194_; 
lean_dec(v___x_2183_);
lean_dec(v___x_2180_);
v___x_2190_ = lean_nat_add(v_startInclusive_2178_, v_stackPos_2169_);
v_stackByte_2191_ = lean_string_get_byte_fast(v_str_2177_, v___x_2190_);
v___x_2192_ = lean_nat_add(v_startInclusive_2175_, v_needlePos_2170_);
v_patByte_2193_ = lean_string_get_byte_fast(v_str_2174_, v___x_2192_);
v___x_2194_ = lean_uint8_dec_eq(v_stackByte_2191_, v_patByte_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; uint8_t v_decide_2196_; 
lean_dec(v___x_2181_);
v___x_2195_ = lean_unsigned_to_nat(0u);
v_decide_2196_ = lean_nat_dec_eq(v_needlePos_2170_, v___x_2195_);
if (v_decide_2196_ == 0)
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v_newNeedlePos_2199_; uint8_t v___x_2200_; 
v___x_2197_ = lean_unsigned_to_nat(1u);
v___x_2198_ = lean_nat_sub(v_needlePos_2170_, v___x_2197_);
lean_dec(v_needlePos_2170_);
v_newNeedlePos_2199_ = lean_array_fget_borrowed(v_table_2168_, v___x_2198_);
lean_dec(v___x_2198_);
v___x_2200_ = lean_nat_dec_eq(v_newNeedlePos_2199_, v___x_2195_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2202_; 
lean_inc(v_newNeedlePos_2199_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 3, v_newNeedlePos_2199_);
v___x_2202_ = v___x_2172_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_needle_2167_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_table_2168_);
lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_stackPos_2169_);
lean_ctor_set(v_reuseFailAlloc_2204_, 3, v_newNeedlePos_2199_);
v___x_2202_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
v_a_2144_ = v___x_2202_;
v_b_2145_ = v___x_2146_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2205_; lean_object* v___x_2207_; 
v_nextStackPos_2205_ = l_String_Slice_posGE___redArg(v_s_2143_, v_stackPos_2169_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 3, v___x_2195_);
lean_ctor_set(v___x_2172_, 2, v_nextStackPos_2205_);
v___x_2207_ = v___x_2172_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_needle_2167_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_table_2168_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_nextStackPos_2205_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v___x_2195_);
v___x_2207_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
v_a_2144_ = v___x_2207_;
v_b_2145_ = v___x_2146_;
goto _start;
}
}
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_nextStackPos_2212_; lean_object* v___x_2214_; 
lean_dec(v_needlePos_2170_);
v___x_2210_ = lean_unsigned_to_nat(1u);
v___x_2211_ = lean_nat_add(v_stackPos_2169_, v___x_2210_);
lean_dec(v_stackPos_2169_);
v_nextStackPos_2212_ = l_String_Slice_posGE___redArg(v_s_2143_, v___x_2211_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 3, v___x_2195_);
lean_ctor_set(v___x_2172_, 2, v_nextStackPos_2212_);
v___x_2214_ = v___x_2172_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_needle_2167_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_table_2168_);
lean_ctor_set(v_reuseFailAlloc_2216_, 2, v_nextStackPos_2212_);
lean_ctor_set(v_reuseFailAlloc_2216_, 3, v___x_2195_);
v___x_2214_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
v_a_2144_ = v___x_2214_;
v_b_2145_ = v___x_2146_;
goto _start;
}
}
}
else
{
lean_object* v___x_2217_; lean_object* v_nextNeedlePos_2218_; uint8_t v_decide_2219_; 
v___x_2217_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2218_ = lean_nat_add(v_needlePos_2170_, v___x_2217_);
lean_dec(v_needlePos_2170_);
v_decide_2219_ = lean_nat_dec_eq(v_nextNeedlePos_2218_, v___x_2181_);
lean_dec(v___x_2181_);
if (v_decide_2219_ == 0)
{
lean_object* v_nextStackPos_2220_; lean_object* v___x_2222_; 
v_nextStackPos_2220_ = lean_nat_add(v_stackPos_2169_, v___x_2217_);
lean_dec(v_stackPos_2169_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 3, v_nextNeedlePos_2218_);
lean_ctor_set(v___x_2172_, 2, v_nextStackPos_2220_);
v___x_2222_ = v___x_2172_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_needle_2167_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_table_2168_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_nextStackPos_2220_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_nextNeedlePos_2218_);
v___x_2222_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
v_a_2144_ = v___x_2222_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2218_);
lean_del_object(v___x_2172_);
lean_dec(v_stackPos_2169_);
lean_dec_ref(v_table_2168_);
lean_dec_ref(v_needle_2167_);
return v_decide_2219_;
}
}
}
}
}
default: 
{
return v_b_2145_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2226_, lean_object* v_a_2227_, lean_object* v_b_2228_){
_start:
{
uint8_t v_b_boxed_2229_; uint8_t v_res_2230_; lean_object* v_r_2231_; 
v_b_boxed_2229_ = lean_unbox(v_b_2228_);
v_res_2230_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2226_, v_a_2227_, v_b_boxed_2229_);
lean_dec_ref(v_s_2226_);
v_r_2231_ = lean_box(v_res_2230_);
return v_r_2231_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2234_, lean_object* v_s_2235_){
_start:
{
lean_object* v___y_2237_; lean_object* v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2240_ = lean_unsigned_to_nat(0u);
v___x_2241_ = lean_string_utf8_byte_size(v___x_2234_);
v___x_2242_ = lean_nat_dec_eq(v___x_2241_, v___x_2240_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2234_);
lean_ctor_set(v___x_2243_, 1, v___x_2240_);
lean_ctor_set(v___x_2243_, 2, v___x_2241_);
v___x_2244_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2243_);
v___x_2245_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
lean_ctor_set(v___x_2245_, 2, v___x_2240_);
lean_ctor_set(v___x_2245_, 3, v___x_2240_);
v___y_2237_ = v___x_2245_;
goto v___jp_2236_;
}
else
{
lean_object* v___x_2246_; 
lean_dec_ref(v___x_2234_);
v___x_2246_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___closed__0));
v___y_2237_ = v___x_2246_;
goto v___jp_2236_;
}
v___jp_2236_:
{
uint8_t v___x_2238_; uint8_t v___x_2239_; 
v___x_2238_ = 0;
v___x_2239_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2235_, v___y_2237_, v___x_2238_);
return v___x_2239_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2247_, lean_object* v_s_2248_){
_start:
{
uint8_t v_res_2249_; lean_object* v_r_2250_; 
v_res_2249_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2247_, v_s_2248_);
lean_dec_ref(v_s_2248_);
v_r_2250_ = lean_box(v_res_2249_);
return v_r_2250_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v_suppressElabErrors_2251_, uint8_t v___y_2252_, lean_object* v_x_2253_){
_start:
{
if (lean_obj_tag(v_x_2253_) == 1)
{
lean_object* v_pre_2254_; 
v_pre_2254_ = lean_ctor_get(v_x_2253_, 0);
if (lean_obj_tag(v_pre_2254_) == 0)
{
lean_object* v_str_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v_str_2255_ = lean_ctor_get(v_x_2253_, 1);
v___x_2256_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2257_ = lean_string_dec_eq(v_str_2255_, v___x_2256_);
if (v___x_2257_ == 0)
{
return v___x_2257_;
}
else
{
return v_suppressElabErrors_2251_;
}
}
else
{
return v___y_2252_;
}
}
else
{
return v___y_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_2258_, lean_object* v___y_2259_, lean_object* v_x_2260_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2261_; uint8_t v___y_26131__boxed_2262_; uint8_t v_res_2263_; lean_object* v_r_2264_; 
v_suppressElabErrors_boxed_2261_ = lean_unbox(v_suppressElabErrors_2258_);
v___y_26131__boxed_2262_ = lean_unbox(v___y_2259_);
v_res_2263_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v_suppressElabErrors_boxed_2261_, v___y_26131__boxed_2262_, v_x_2260_);
lean_dec(v_x_2260_);
v_r_2264_ = lean_box(v_res_2263_);
return v_r_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2265_, lean_object* v_msgData_2266_, uint8_t v_severity_2267_, uint8_t v_isSilent_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
uint8_t v___y_2273_; lean_object* v___y_2274_; uint8_t v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; uint8_t v___y_2338_; uint8_t v___y_2339_; uint8_t v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; uint8_t v___y_2366_; uint8_t v___y_2367_; uint8_t v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; uint8_t v___y_2374_; uint8_t v___y_2375_; uint8_t v___y_2376_; uint8_t v___x_2391_; uint8_t v___y_2393_; uint8_t v___y_2394_; uint8_t v___y_2395_; uint8_t v___y_2397_; uint8_t v___x_2409_; 
v___x_2391_ = 2;
v___x_2409_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2267_, v___x_2391_);
if (v___x_2409_ == 0)
{
v___y_2397_ = v___x_2409_;
goto v___jp_2396_;
}
else
{
uint8_t v___x_2410_; 
lean_inc_ref(v_msgData_2266_);
v___x_2410_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2266_);
v___y_2397_ = v___x_2410_;
goto v___jp_2396_;
}
v___jp_2272_:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Elab_Command_getScope___redArg(v___y_2280_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v_currNamespace_2283_; lean_object* v___x_2284_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v_currNamespace_2283_ = lean_ctor_get(v_a_2282_, 2);
lean_inc(v_currNamespace_2283_);
lean_dec(v_a_2282_);
v___x_2284_ = l_Lean_Elab_Command_getScope___redArg(v___y_2280_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2320_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2320_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2320_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v_openDecls_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v_env_2294_; lean_object* v_messages_2295_; lean_object* v_scopes_2296_; lean_object* v_usedQuotCtxts_2297_; lean_object* v_nextMacroScope_2298_; lean_object* v_maxRecDepth_2299_; lean_object* v_ngen_2300_; lean_object* v_auxDeclNGen_2301_; lean_object* v_infoState_2302_; lean_object* v_traceState_2303_; lean_object* v_snapshotTasks_2304_; lean_object* v_prevLinterStates_2305_; lean_object* v_codeQualityEntryTasks_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2319_; 
v_openDecls_2289_ = lean_ctor_get(v_a_2285_, 3);
lean_inc(v_openDecls_2289_);
lean_dec(v_a_2285_);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v_currNamespace_2283_);
lean_ctor_set(v___x_2290_, 1, v_openDecls_2289_);
v___x_2291_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v___y_2274_);
lean_inc_ref(v___y_2278_);
lean_inc_ref(v___y_2277_);
v___x_2292_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2292_, 0, v___y_2277_);
lean_ctor_set(v___x_2292_, 1, v___y_2276_);
lean_ctor_set(v___x_2292_, 2, v___y_2279_);
lean_ctor_set(v___x_2292_, 3, v___y_2278_);
lean_ctor_set(v___x_2292_, 4, v___x_2291_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*5, v___y_2275_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*5 + 1, v___y_2273_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*5 + 2, v_isSilent_2268_);
v___x_2293_ = lean_st_ref_take(v___y_2280_);
v_env_2294_ = lean_ctor_get(v___x_2293_, 0);
v_messages_2295_ = lean_ctor_get(v___x_2293_, 1);
v_scopes_2296_ = lean_ctor_get(v___x_2293_, 2);
v_usedQuotCtxts_2297_ = lean_ctor_get(v___x_2293_, 3);
v_nextMacroScope_2298_ = lean_ctor_get(v___x_2293_, 4);
v_maxRecDepth_2299_ = lean_ctor_get(v___x_2293_, 5);
v_ngen_2300_ = lean_ctor_get(v___x_2293_, 6);
v_auxDeclNGen_2301_ = lean_ctor_get(v___x_2293_, 7);
v_infoState_2302_ = lean_ctor_get(v___x_2293_, 8);
v_traceState_2303_ = lean_ctor_get(v___x_2293_, 9);
v_snapshotTasks_2304_ = lean_ctor_get(v___x_2293_, 10);
v_prevLinterStates_2305_ = lean_ctor_get(v___x_2293_, 11);
v_codeQualityEntryTasks_2306_ = lean_ctor_get(v___x_2293_, 12);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2308_ = v___x_2293_;
v_isShared_2309_ = v_isSharedCheck_2319_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2306_);
lean_inc(v_prevLinterStates_2305_);
lean_inc(v_snapshotTasks_2304_);
lean_inc(v_traceState_2303_);
lean_inc(v_infoState_2302_);
lean_inc(v_auxDeclNGen_2301_);
lean_inc(v_ngen_2300_);
lean_inc(v_maxRecDepth_2299_);
lean_inc(v_nextMacroScope_2298_);
lean_inc(v_usedQuotCtxts_2297_);
lean_inc(v_scopes_2296_);
lean_inc(v_messages_2295_);
lean_inc(v_env_2294_);
lean_dec(v___x_2293_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2319_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2310_ = lean_box(0);
v___x_2311_ = l_Lean_MessageLog_add(v___x_2292_, v_messages_2295_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 1, v___x_2311_);
v___x_2313_ = v___x_2308_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_env_2294_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_scopes_2296_);
lean_ctor_set(v_reuseFailAlloc_2318_, 3, v_usedQuotCtxts_2297_);
lean_ctor_set(v_reuseFailAlloc_2318_, 4, v_nextMacroScope_2298_);
lean_ctor_set(v_reuseFailAlloc_2318_, 5, v_maxRecDepth_2299_);
lean_ctor_set(v_reuseFailAlloc_2318_, 6, v_ngen_2300_);
lean_ctor_set(v_reuseFailAlloc_2318_, 7, v_auxDeclNGen_2301_);
lean_ctor_set(v_reuseFailAlloc_2318_, 8, v_infoState_2302_);
lean_ctor_set(v_reuseFailAlloc_2318_, 9, v_traceState_2303_);
lean_ctor_set(v_reuseFailAlloc_2318_, 10, v_snapshotTasks_2304_);
lean_ctor_set(v_reuseFailAlloc_2318_, 11, v_prevLinterStates_2305_);
lean_ctor_set(v_reuseFailAlloc_2318_, 12, v_codeQualityEntryTasks_2306_);
v___x_2313_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2314_ = lean_st_ref_put(v___y_2280_, v___x_2313_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2310_);
v___x_2316_ = v___x_2287_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2310_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_currNamespace_2283_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2276_);
lean_dec_ref(v___y_2274_);
v_a_2321_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2284_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2284_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2276_);
lean_dec_ref(v___y_2274_);
v_a_2329_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2281_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2281_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
v___jp_2337_:
{
lean_object* v_fileName_2343_; lean_object* v_fileMap_2344_; uint8_t v_suppressElabErrors_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___f_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2364_; 
v_fileName_2343_ = lean_ctor_get(v___y_2269_, 0);
v_fileMap_2344_ = lean_ctor_get(v___y_2269_, 1);
v_suppressElabErrors_2345_ = lean_ctor_get_uint8(v___y_2269_, sizeof(void*)*10);
v___x_2346_ = lean_box(v_suppressElabErrors_2345_);
v___x_2347_ = lean_box(v___y_2338_);
v___f_2348_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2348_, 0, v___x_2346_);
lean_closure_set(v___f_2348_, 1, v___x_2347_);
v___x_2349_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2266_);
v___x_2350_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2349_, v___y_2270_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2364_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2364_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_inc_ref_n(v_fileMap_2344_, 2);
v___x_2355_ = l_Lean_FileMap_toPosition(v_fileMap_2344_, v___y_2341_);
lean_dec(v___y_2341_);
v___x_2356_ = l_Lean_FileMap_toPosition(v_fileMap_2344_, v___y_2342_);
lean_dec(v___y_2342_);
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
v___x_2358_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
if (v_suppressElabErrors_2345_ == 0)
{
lean_del_object(v___x_2353_);
lean_dec_ref(v___f_2348_);
v___y_2273_ = v___y_2339_;
v___y_2274_ = v_a_2351_;
v___y_2275_ = v___y_2340_;
v___y_2276_ = v___x_2355_;
v___y_2277_ = v_fileName_2343_;
v___y_2278_ = v___x_2358_;
v___y_2279_ = v___x_2357_;
v___y_2280_ = v___y_2270_;
goto v___jp_2272_;
}
else
{
uint8_t v___x_2359_; 
lean_inc(v_a_2351_);
v___x_2359_ = l_Lean_MessageData_hasTag(v___f_2348_, v_a_2351_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
lean_dec_ref_known(v___x_2357_, 1);
lean_dec_ref(v___x_2355_);
lean_dec(v_a_2351_);
v___x_2360_ = lean_box(0);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2360_);
v___x_2362_ = v___x_2353_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
else
{
lean_del_object(v___x_2353_);
v___y_2273_ = v___y_2339_;
v___y_2274_ = v_a_2351_;
v___y_2275_ = v___y_2340_;
v___y_2276_ = v___x_2355_;
v___y_2277_ = v_fileName_2343_;
v___y_2278_ = v___x_2358_;
v___y_2279_ = v___x_2357_;
v___y_2280_ = v___y_2270_;
goto v___jp_2272_;
}
}
}
}
v___jp_2365_:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Syntax_getTailPos_x3f(v___y_2369_, v___y_2368_);
lean_dec(v___y_2369_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_inc(v___y_2370_);
v___y_2338_ = v___y_2366_;
v___y_2339_ = v___y_2367_;
v___y_2340_ = v___y_2368_;
v___y_2341_ = v___y_2370_;
v___y_2342_ = v___y_2370_;
goto v___jp_2337_;
}
else
{
lean_object* v_val_2372_; 
v_val_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_val_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v___y_2338_ = v___y_2366_;
v___y_2339_ = v___y_2367_;
v___y_2340_ = v___y_2368_;
v___y_2341_ = v___y_2370_;
v___y_2342_ = v_val_2372_;
goto v___jp_2337_;
}
}
v___jp_2373_:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Lean_Elab_Command_getRef___redArg(v___y_2269_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v_ref_2379_; lean_object* v___x_2380_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2377_, 1);
v_ref_2379_ = l_Lean_replaceRef(v_ref_2265_, v_a_2378_);
lean_dec(v_a_2378_);
v___x_2380_ = l_Lean_Syntax_getPos_x3f(v_ref_2379_, v___y_2375_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_unsigned_to_nat(0u);
v___y_2366_ = v___y_2374_;
v___y_2367_ = v___y_2376_;
v___y_2368_ = v___y_2375_;
v___y_2369_ = v_ref_2379_;
v___y_2370_ = v___x_2381_;
goto v___jp_2365_;
}
else
{
lean_object* v_val_2382_; 
v_val_2382_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_val_2382_);
lean_dec_ref_known(v___x_2380_, 1);
v___y_2366_ = v___y_2374_;
v___y_2367_ = v___y_2376_;
v___y_2368_ = v___y_2375_;
v___y_2369_ = v_ref_2379_;
v___y_2370_ = v_val_2382_;
goto v___jp_2365_;
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec_ref(v_msgData_2266_);
v_a_2383_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2377_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2377_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
v___jp_2392_:
{
if (v___y_2395_ == 0)
{
v___y_2374_ = v___y_2393_;
v___y_2375_ = v___y_2394_;
v___y_2376_ = v_severity_2267_;
goto v___jp_2373_;
}
else
{
v___y_2374_ = v___y_2393_;
v___y_2375_ = v___y_2394_;
v___y_2376_ = v___x_2391_;
goto v___jp_2373_;
}
}
v___jp_2396_:
{
if (v___y_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v_scopes_2400_; lean_object* v___x_2401_; lean_object* v_opts_2402_; uint8_t v___x_2403_; uint8_t v___x_2404_; 
v___x_2398_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2399_ = lean_st_ref_get(v___y_2270_);
v_scopes_2400_ = lean_ctor_get(v___x_2399_, 2);
lean_inc(v_scopes_2400_);
lean_dec(v___x_2399_);
v___x_2401_ = l_List_head_x21___redArg(v___x_2398_, v_scopes_2400_);
lean_dec(v_scopes_2400_);
v_opts_2402_ = lean_ctor_get(v___x_2401_, 1);
lean_inc_ref(v_opts_2402_);
lean_dec(v___x_2401_);
v___x_2403_ = 1;
v___x_2404_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2267_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_dec_ref(v_opts_2402_);
v___y_2393_ = v___y_2397_;
v___y_2394_ = v___y_2397_;
v___y_2395_ = v___x_2404_;
goto v___jp_2392_;
}
else
{
lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = l_Lean_warningAsError;
v___x_2406_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2402_, v___x_2405_);
lean_dec_ref(v_opts_2402_);
v___y_2393_ = v___y_2397_;
v___y_2394_ = v___y_2397_;
v___y_2395_ = v___x_2406_;
goto v___jp_2392_;
}
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_dec_ref(v_msgData_2266_);
v___x_2407_ = lean_box(0);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
return v___x_2408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2411_, lean_object* v_msgData_2412_, lean_object* v_severity_2413_, lean_object* v_isSilent_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
uint8_t v_severity_boxed_2418_; uint8_t v_isSilent_boxed_2419_; lean_object* v_res_2420_; 
v_severity_boxed_2418_ = lean_unbox(v_severity_2413_);
v_isSilent_boxed_2419_ = lean_unbox(v_isSilent_2414_);
v_res_2420_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2411_, v_msgData_2412_, v_severity_boxed_2418_, v_isSilent_boxed_2419_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v_ref_2411_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2421_, lean_object* v_msgData_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
uint8_t v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = 2;
v___x_2427_ = 0;
v___x_2428_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2421_, v_msgData_2422_, v___x_2426_, v___x_2427_, v___y_2423_, v___y_2424_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2429_, lean_object* v_msgData_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2429_, v_msgData_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v_ref_2429_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2435_, lean_object* v___x_2436_, lean_object* v___x_2437_, lean_object* v_a_2438_, lean_object* v_b_2439_){
_start:
{
lean_object* v_it_2441_; lean_object* v_startInclusive_2442_; lean_object* v_endExclusive_2443_; 
if (lean_obj_tag(v_a_2438_) == 0)
{
lean_object* v_currPos_2448_; lean_object* v_searcher_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2478_; 
v_currPos_2448_ = lean_ctor_get(v_a_2438_, 0);
v_searcher_2449_ = lean_ctor_get(v_a_2438_, 1);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_a_2438_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2451_ = v_a_2438_;
v_isShared_2452_ = v_isSharedCheck_2478_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_searcher_2449_);
lean_inc(v_currPos_2448_);
lean_dec(v_a_2438_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2478_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_str_2453_; lean_object* v_startInclusive_2454_; lean_object* v_endExclusive_2455_; lean_object* v___x_2456_; uint8_t v_decide_2457_; 
v_str_2453_ = lean_ctor_get(v___x_2436_, 0);
v_startInclusive_2454_ = lean_ctor_get(v___x_2436_, 1);
v_endExclusive_2455_ = lean_ctor_get(v___x_2436_, 2);
v___x_2456_ = lean_nat_sub(v_endExclusive_2455_, v_startInclusive_2454_);
v_decide_2457_ = lean_nat_dec_eq(v_searcher_2449_, v___x_2456_);
lean_dec(v___x_2456_);
if (v_decide_2457_ == 0)
{
uint32_t v___x_2458_; lean_object* v___x_2459_; uint32_t v___x_2460_; uint8_t v___x_2461_; 
v___x_2458_ = 10;
v___x_2459_ = lean_nat_add(v_startInclusive_2454_, v_searcher_2449_);
v___x_2460_ = lean_string_utf8_get_fast(v_str_2453_, v___x_2459_);
v___x_2461_ = lean_uint32_dec_eq(v___x_2460_, v___x_2458_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
lean_dec(v_searcher_2449_);
v___x_2462_ = lean_string_utf8_next_fast(v_str_2453_, v___x_2459_);
lean_dec(v___x_2459_);
v___x_2463_ = lean_nat_sub(v___x_2462_, v_startInclusive_2454_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___x_2463_);
v___x_2465_ = v___x_2451_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_currPos_2448_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
v_a_2438_ = v___x_2465_;
goto _start;
}
}
else
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v_slice_2471_; lean_object* v_nextIt_2473_; 
v___x_2468_ = lean_string_utf8_next_fast(v_str_2453_, v___x_2459_);
v___x_2469_ = lean_nat_sub(v___x_2468_, v___x_2459_);
lean_dec(v___x_2459_);
v___x_2470_ = lean_nat_add(v_searcher_2449_, v___x_2469_);
lean_dec(v___x_2469_);
v_slice_2471_ = l_String_Slice_subslice_x21(v___x_2436_, v_currPos_2448_, v_searcher_2449_);
lean_inc(v___x_2470_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___x_2470_);
lean_ctor_set(v___x_2451_, 0, v___x_2470_);
v_nextIt_2473_ = v___x_2451_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2470_);
v_nextIt_2473_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v_startInclusive_2474_; lean_object* v_endExclusive_2475_; 
v_startInclusive_2474_ = lean_ctor_get(v_slice_2471_, 0);
lean_inc(v_startInclusive_2474_);
v_endExclusive_2475_ = lean_ctor_get(v_slice_2471_, 1);
lean_inc(v_endExclusive_2475_);
lean_dec_ref(v_slice_2471_);
v_it_2441_ = v_nextIt_2473_;
v_startInclusive_2442_ = v_startInclusive_2474_;
v_endExclusive_2443_ = v_endExclusive_2475_;
goto v___jp_2440_;
}
}
}
else
{
lean_object* v___x_2477_; 
lean_del_object(v___x_2451_);
lean_dec(v_searcher_2449_);
v___x_2477_ = lean_box(1);
lean_inc(v___x_2437_);
v_it_2441_ = v___x_2477_;
v_startInclusive_2442_ = v_currPos_2448_;
v_endExclusive_2443_ = v___x_2437_;
goto v___jp_2440_;
}
}
}
else
{
lean_dec(v___x_2437_);
lean_dec_ref(v___x_2435_);
return v_b_2439_;
}
v___jp_2440_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
lean_inc_ref(v___x_2435_);
v___x_2444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2435_);
lean_ctor_set(v___x_2444_, 1, v_startInclusive_2442_);
lean_ctor_set(v___x_2444_, 2, v_endExclusive_2443_);
v___x_2445_ = l_String_Slice_toString(v___x_2444_);
lean_dec_ref_known(v___x_2444_, 3);
v___x_2446_ = lean_array_push(v_b_2439_, v___x_2445_);
v_a_2438_ = v_it_2441_;
v_b_2439_ = v___x_2446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2479_, lean_object* v___x_2480_, lean_object* v___x_2481_, lean_object* v_a_2482_, lean_object* v_b_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2479_, v___x_2480_, v___x_2481_, v_a_2482_, v_b_2483_);
lean_dec_ref(v___x_2480_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2485_, lean_object* v___x_2486_, lean_object* v___x_2487_, lean_object* v_a_2488_, lean_object* v_b_2489_){
_start:
{
lean_object* v_it_2491_; lean_object* v_startInclusive_2492_; lean_object* v_endExclusive_2493_; 
if (lean_obj_tag(v_a_2488_) == 0)
{
lean_object* v_currPos_2498_; lean_object* v_searcher_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2528_; 
v_currPos_2498_ = lean_ctor_get(v_a_2488_, 0);
v_searcher_2499_ = lean_ctor_get(v_a_2488_, 1);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_a_2488_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2501_ = v_a_2488_;
v_isShared_2502_ = v_isSharedCheck_2528_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_searcher_2499_);
lean_inc(v_currPos_2498_);
lean_dec(v_a_2488_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2528_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_str_2503_; lean_object* v_startInclusive_2504_; lean_object* v_endExclusive_2505_; lean_object* v___x_2506_; uint8_t v_decide_2507_; 
v_str_2503_ = lean_ctor_get(v___x_2486_, 0);
v_startInclusive_2504_ = lean_ctor_get(v___x_2486_, 1);
v_endExclusive_2505_ = lean_ctor_get(v___x_2486_, 2);
v___x_2506_ = lean_nat_sub(v_endExclusive_2505_, v_startInclusive_2504_);
v_decide_2507_ = lean_nat_dec_eq(v_searcher_2499_, v___x_2506_);
lean_dec(v___x_2506_);
if (v_decide_2507_ == 0)
{
lean_object* v___x_2508_; uint32_t v___x_2509_; uint32_t v___x_2510_; uint8_t v___x_2511_; 
v___x_2508_ = lean_nat_add(v_startInclusive_2504_, v_searcher_2499_);
v___x_2509_ = lean_string_utf8_get_fast(v_str_2503_, v___x_2508_);
v___x_2510_ = 10;
v___x_2511_ = lean_uint32_dec_eq(v___x_2509_, v___x_2510_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
lean_dec(v_searcher_2499_);
v___x_2512_ = lean_string_utf8_next_fast(v_str_2503_, v___x_2508_);
lean_dec(v___x_2508_);
v___x_2513_ = lean_nat_sub(v___x_2512_, v_startInclusive_2504_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2513_);
v___x_2515_ = v___x_2501_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_currPos_2498_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2516_; 
v___x_2516_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2485_, v___x_2486_, v___x_2487_, v___x_2515_, v_b_2489_);
return v___x_2516_;
}
}
else
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v_slice_2521_; lean_object* v_nextIt_2523_; 
v___x_2518_ = lean_string_utf8_next_fast(v_str_2503_, v___x_2508_);
v___x_2519_ = lean_nat_sub(v___x_2518_, v___x_2508_);
lean_dec(v___x_2508_);
v___x_2520_ = lean_nat_add(v_searcher_2499_, v___x_2519_);
lean_dec(v___x_2519_);
v_slice_2521_ = l_String_Slice_subslice_x21(v___x_2486_, v_currPos_2498_, v_searcher_2499_);
lean_inc(v___x_2520_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2520_);
lean_ctor_set(v___x_2501_, 0, v___x_2520_);
v_nextIt_2523_ = v___x_2501_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v___x_2520_);
v_nextIt_2523_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v_startInclusive_2524_; lean_object* v_endExclusive_2525_; 
v_startInclusive_2524_ = lean_ctor_get(v_slice_2521_, 0);
lean_inc(v_startInclusive_2524_);
v_endExclusive_2525_ = lean_ctor_get(v_slice_2521_, 1);
lean_inc(v_endExclusive_2525_);
lean_dec_ref(v_slice_2521_);
v_it_2491_ = v_nextIt_2523_;
v_startInclusive_2492_ = v_startInclusive_2524_;
v_endExclusive_2493_ = v_endExclusive_2525_;
goto v___jp_2490_;
}
}
}
else
{
lean_object* v___x_2527_; 
lean_del_object(v___x_2501_);
lean_dec(v_searcher_2499_);
v___x_2527_ = lean_box(1);
lean_inc(v___x_2487_);
v_it_2491_ = v___x_2527_;
v_startInclusive_2492_ = v_currPos_2498_;
v_endExclusive_2493_ = v___x_2487_;
goto v___jp_2490_;
}
}
}
else
{
lean_dec(v___x_2487_);
lean_dec_ref(v___x_2485_);
return v_b_2489_;
}
v___jp_2490_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
lean_inc_ref(v___x_2485_);
v___x_2494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2485_);
lean_ctor_set(v___x_2494_, 1, v_startInclusive_2492_);
lean_ctor_set(v___x_2494_, 2, v_endExclusive_2493_);
v___x_2495_ = l_String_Slice_toString(v___x_2494_);
lean_dec_ref_known(v___x_2494_, 3);
v___x_2496_ = lean_array_push(v_b_2489_, v___x_2495_);
v___x_2497_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2485_, v___x_2486_, v___x_2487_, v_it_2491_, v___x_2496_);
return v___x_2497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2529_, lean_object* v___x_2530_, lean_object* v___x_2531_, lean_object* v_a_2532_, lean_object* v_b_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2529_, v___x_2530_, v___x_2531_, v_a_2532_, v_b_2533_);
lean_dec_ref(v___x_2530_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v___x_2538_; lean_object* v_infoState_2539_; uint8_t v_enabled_2540_; 
v___x_2538_ = lean_st_ref_get(v___y_2536_);
v_infoState_2539_ = lean_ctor_get(v___x_2538_, 8);
lean_inc_ref(v_infoState_2539_);
lean_dec(v___x_2538_);
v_enabled_2540_ = lean_ctor_get_uint8(v_infoState_2539_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2539_);
if (v_enabled_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec_ref(v_t_2535_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; lean_object* v_infoState_2544_; lean_object* v_env_2545_; lean_object* v_messages_2546_; lean_object* v_scopes_2547_; lean_object* v_usedQuotCtxts_2548_; lean_object* v_nextMacroScope_2549_; lean_object* v_maxRecDepth_2550_; lean_object* v_ngen_2551_; lean_object* v_auxDeclNGen_2552_; lean_object* v_traceState_2553_; lean_object* v_snapshotTasks_2554_; lean_object* v_prevLinterStates_2555_; lean_object* v_codeQualityEntryTasks_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2578_; 
v___x_2543_ = lean_st_ref_take(v___y_2536_);
v_infoState_2544_ = lean_ctor_get(v___x_2543_, 8);
v_env_2545_ = lean_ctor_get(v___x_2543_, 0);
v_messages_2546_ = lean_ctor_get(v___x_2543_, 1);
v_scopes_2547_ = lean_ctor_get(v___x_2543_, 2);
v_usedQuotCtxts_2548_ = lean_ctor_get(v___x_2543_, 3);
v_nextMacroScope_2549_ = lean_ctor_get(v___x_2543_, 4);
v_maxRecDepth_2550_ = lean_ctor_get(v___x_2543_, 5);
v_ngen_2551_ = lean_ctor_get(v___x_2543_, 6);
v_auxDeclNGen_2552_ = lean_ctor_get(v___x_2543_, 7);
v_traceState_2553_ = lean_ctor_get(v___x_2543_, 9);
v_snapshotTasks_2554_ = lean_ctor_get(v___x_2543_, 10);
v_prevLinterStates_2555_ = lean_ctor_get(v___x_2543_, 11);
v_codeQualityEntryTasks_2556_ = lean_ctor_get(v___x_2543_, 12);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2558_ = v___x_2543_;
v_isShared_2559_ = v_isSharedCheck_2578_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2556_);
lean_inc(v_prevLinterStates_2555_);
lean_inc(v_snapshotTasks_2554_);
lean_inc(v_traceState_2553_);
lean_inc(v_infoState_2544_);
lean_inc(v_auxDeclNGen_2552_);
lean_inc(v_ngen_2551_);
lean_inc(v_maxRecDepth_2550_);
lean_inc(v_nextMacroScope_2549_);
lean_inc(v_usedQuotCtxts_2548_);
lean_inc(v_scopes_2547_);
lean_inc(v_messages_2546_);
lean_inc(v_env_2545_);
lean_dec(v___x_2543_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2578_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
uint8_t v_enabled_2560_; lean_object* v_assignment_2561_; lean_object* v_lazyAssignment_2562_; lean_object* v_trees_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2577_; 
v_enabled_2560_ = lean_ctor_get_uint8(v_infoState_2544_, sizeof(void*)*3);
v_assignment_2561_ = lean_ctor_get(v_infoState_2544_, 0);
v_lazyAssignment_2562_ = lean_ctor_get(v_infoState_2544_, 1);
v_trees_2563_ = lean_ctor_get(v_infoState_2544_, 2);
v_isSharedCheck_2577_ = !lean_is_exclusive(v_infoState_2544_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2565_ = v_infoState_2544_;
v_isShared_2566_ = v_isSharedCheck_2577_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_trees_2563_);
lean_inc(v_lazyAssignment_2562_);
lean_inc(v_assignment_2561_);
lean_dec(v_infoState_2544_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2577_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2567_ = lean_box(0);
v___x_2568_ = l_Lean_PersistentArray_push___redArg(v_trees_2563_, v_t_2535_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 2, v___x_2568_);
v___x_2570_ = v___x_2565_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_assignment_2561_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_lazyAssignment_2562_);
lean_ctor_set(v_reuseFailAlloc_2576_, 2, v___x_2568_);
lean_ctor_set_uint8(v_reuseFailAlloc_2576_, sizeof(void*)*3, v_enabled_2560_);
v___x_2570_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2572_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 8, v___x_2570_);
v___x_2572_ = v___x_2558_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_env_2545_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_messages_2546_);
lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_scopes_2547_);
lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_usedQuotCtxts_2548_);
lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_nextMacroScope_2549_);
lean_ctor_set(v_reuseFailAlloc_2575_, 5, v_maxRecDepth_2550_);
lean_ctor_set(v_reuseFailAlloc_2575_, 6, v_ngen_2551_);
lean_ctor_set(v_reuseFailAlloc_2575_, 7, v_auxDeclNGen_2552_);
lean_ctor_set(v_reuseFailAlloc_2575_, 8, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2575_, 9, v_traceState_2553_);
lean_ctor_set(v_reuseFailAlloc_2575_, 10, v_snapshotTasks_2554_);
lean_ctor_set(v_reuseFailAlloc_2575_, 11, v_prevLinterStates_2555_);
lean_ctor_set(v_reuseFailAlloc_2575_, 12, v_codeQualityEntryTasks_2556_);
v___x_2572_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = lean_st_ref_put(v___y_2536_, v___x_2572_);
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2567_);
return v___x_2574_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2579_, v___y_2580_);
lean_dec(v___y_2580_);
return v_res_2582_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_unsigned_to_nat(32u);
v___x_2584_ = lean_mk_empty_array_with_capacity(v___x_2583_);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
return v___x_2585_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2586_ = ((size_t)5ULL);
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = lean_unsigned_to_nat(32u);
v___x_2589_ = lean_mk_empty_array_with_capacity(v___x_2588_);
v___x_2590_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2591_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v___x_2589_);
lean_ctor_set(v___x_2591_, 2, v___x_2587_);
lean_ctor_set(v___x_2591_, 3, v___x_2587_);
lean_ctor_set_usize(v___x_2591_, 4, v___x_2586_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; lean_object* v_infoState_2597_; uint8_t v_enabled_2598_; 
v___x_2596_ = lean_st_ref_get(v___y_2594_);
v_infoState_2597_ = lean_ctor_get(v___x_2596_, 8);
lean_inc_ref(v_infoState_2597_);
lean_dec(v___x_2596_);
v_enabled_2598_ = lean_ctor_get_uint8(v_infoState_2597_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2597_);
if (v_enabled_2598_ == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec_ref(v_t_2592_);
v___x_2599_ = lean_box(0);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
else
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2602_, 0, v_t_2592_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2602_, v___y_2594_);
return v___x_2603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2604_, v___y_2605_, v___y_2606_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v___x_2609_, lean_object* v_edited_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_){
_start:
{
lean_object* v_fst_2613_; lean_object* v_snd_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2638_; 
v_fst_2613_ = lean_ctor_get(v_a_2612_, 0);
v_snd_2614_ = lean_ctor_get(v_a_2612_, 1);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_a_2612_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2616_ = v_a_2612_;
v_isShared_2617_ = v_isSharedCheck_2638_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_snd_2614_);
lean_inc(v_fst_2613_);
lean_dec(v_a_2612_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2638_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
uint8_t v___x_2618_; 
v___x_2618_ = lean_nat_dec_lt(v_snd_2614_, v___x_2609_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2620_; 
if (v_isShared_2617_ == 0)
{
v___x_2620_ = v___x_2616_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_fst_2613_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_snd_2614_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2622_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2623_ = lean_array_get_borrowed(v___x_2622_, v_edited_2610_, v_snd_2614_);
v___x_2624_ = lean_string_dec_eq(v___x_2623_, v_a_2611_);
if (v___x_2624_ == 0)
{
uint8_t v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2625_ = 0;
v___x_2626_ = lean_box(v___x_2625_);
lean_inc(v___x_2623_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 1, v___x_2623_);
lean_ctor_set(v___x_2616_, 0, v___x_2626_);
v___x_2628_ = v___x_2616_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v___x_2623_);
v___x_2628_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2629_ = lean_array_push(v_fst_2613_, v___x_2628_);
v___x_2630_ = lean_unsigned_to_nat(1u);
v___x_2631_ = lean_nat_add(v_snd_2614_, v___x_2630_);
lean_dec(v_snd_2614_);
v___x_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2629_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v_a_2612_ = v___x_2632_;
goto _start;
}
}
else
{
lean_object* v___x_2636_; 
if (v_isShared_2617_ == 0)
{
v___x_2636_ = v___x_2616_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_fst_2613_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_snd_2614_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v___x_2639_, lean_object* v_edited_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2639_, v_edited_2640_, v_a_2641_, v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec_ref(v_edited_2640_);
lean_dec(v___x_2639_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(lean_object* v___x_2644_, lean_object* v_original_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_fst_2648_; lean_object* v_snd_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2673_; 
v_fst_2648_ = lean_ctor_get(v_a_2647_, 0);
v_snd_2649_ = lean_ctor_get(v_a_2647_, 1);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_a_2647_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2651_ = v_a_2647_;
v_isShared_2652_ = v_isSharedCheck_2673_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_snd_2649_);
lean_inc(v_fst_2648_);
lean_dec(v_a_2647_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2673_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
uint8_t v___x_2653_; 
v___x_2653_ = lean_nat_dec_lt(v_snd_2649_, v___x_2644_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2655_; 
if (v_isShared_2652_ == 0)
{
v___x_2655_ = v___x_2651_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_fst_2648_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_snd_2649_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v___x_2657_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2658_ = lean_array_get_borrowed(v___x_2657_, v_original_2645_, v_snd_2649_);
v___x_2659_ = lean_string_dec_eq(v___x_2658_, v_a_2646_);
if (v___x_2659_ == 0)
{
uint8_t v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2660_ = 1;
v___x_2661_ = lean_box(v___x_2660_);
lean_inc(v___x_2658_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2658_);
lean_ctor_set(v___x_2651_, 0, v___x_2661_);
v___x_2663_ = v___x_2651_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v___x_2658_);
v___x_2663_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2664_ = lean_array_push(v_fst_2648_, v___x_2663_);
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_nat_add(v_snd_2649_, v___x_2665_);
lean_dec(v_snd_2649_);
v___x_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2664_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v_a_2647_ = v___x_2667_;
goto _start;
}
}
else
{
lean_object* v___x_2671_; 
if (v_isShared_2652_ == 0)
{
v___x_2671_ = v___x_2651_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_fst_2648_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_snd_2649_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg___boxed(lean_object* v___x_2674_, lean_object* v_original_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2674_, v_original_2675_, v_a_2676_, v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec_ref(v_original_2675_);
lean_dec(v___x_2674_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v___x_2679_, lean_object* v_original_2680_, lean_object* v___x_2681_, lean_object* v_edited_2682_, lean_object* v_as_2683_, size_t v_sz_2684_, size_t v_i_2685_, lean_object* v_b_2686_){
_start:
{
uint8_t v___x_2687_; 
v___x_2687_ = lean_usize_dec_lt(v_i_2685_, v_sz_2684_);
if (v___x_2687_ == 0)
{
return v_b_2686_;
}
else
{
lean_object* v_snd_2688_; lean_object* v_fst_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2736_; 
v_snd_2688_ = lean_ctor_get(v_b_2686_, 1);
v_fst_2689_ = lean_ctor_get(v_b_2686_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_b_2686_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2691_ = v_b_2686_;
v_isShared_2692_ = v_isSharedCheck_2736_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_snd_2688_);
lean_inc(v_fst_2689_);
lean_dec(v_b_2686_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2736_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v_fst_2693_; lean_object* v_snd_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2735_; 
v_fst_2693_ = lean_ctor_get(v_snd_2688_, 0);
v_snd_2694_ = lean_ctor_get(v_snd_2688_, 1);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_snd_2688_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2696_ = v_snd_2688_;
v_isShared_2697_ = v_isSharedCheck_2735_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_snd_2694_);
lean_inc(v_fst_2693_);
lean_dec(v_snd_2688_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2735_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v_a_2698_; lean_object* v___x_2700_; 
v_a_2698_ = lean_array_uget_borrowed(v_as_2683_, v_i_2685_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 1, v_fst_2693_);
lean_ctor_set(v___x_2696_, 0, v_fst_2689_);
v___x_2700_ = v___x_2696_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_fst_2689_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_fst_2693_);
v___x_2700_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; lean_object* v_fst_2702_; lean_object* v_snd_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2733_; 
v___x_2701_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2679_, v_original_2680_, v_a_2698_, v___x_2700_);
v_fst_2702_ = lean_ctor_get(v___x_2701_, 0);
v_snd_2703_ = lean_ctor_get(v___x_2701_, 1);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2705_ = v___x_2701_;
v_isShared_2706_ = v_isSharedCheck_2733_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_snd_2703_);
lean_inc(v_fst_2702_);
lean_dec(v___x_2701_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2733_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 1, v_snd_2694_);
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_fst_2702_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_snd_2694_);
v___x_2708_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; lean_object* v_fst_2710_; lean_object* v_snd_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2731_; 
v___x_2709_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2681_, v_edited_2682_, v_a_2698_, v___x_2708_);
v_fst_2710_ = lean_ctor_get(v___x_2709_, 0);
v_snd_2711_ = lean_ctor_get(v___x_2709_, 1);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2713_ = v___x_2709_;
v_isShared_2714_ = v_isSharedCheck_2731_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_snd_2711_);
lean_inc(v_fst_2710_);
lean_dec(v___x_2709_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2731_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2715_ = 2;
v___x_2716_ = lean_box(v___x_2715_);
lean_inc(v_a_2698_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 1, v_a_2698_);
lean_ctor_set(v___x_2713_, 0, v___x_2716_);
v___x_2718_ = v___x_2713_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_a_2698_);
v___x_2718_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2719_ = lean_array_push(v_fst_2710_, v___x_2718_);
v___x_2720_ = lean_unsigned_to_nat(1u);
v___x_2721_ = lean_nat_add(v_snd_2703_, v___x_2720_);
lean_dec(v_snd_2703_);
v___x_2722_ = lean_nat_add(v_snd_2711_, v___x_2720_);
lean_dec(v_snd_2711_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 1, v___x_2722_);
lean_ctor_set(v___x_2691_, 0, v___x_2721_);
v___x_2724_ = v___x_2691_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; size_t v___x_2726_; size_t v___x_2727_; 
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2719_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = ((size_t)1ULL);
v___x_2727_ = lean_usize_add(v_i_2685_, v___x_2726_);
v_i_2685_ = v___x_2727_;
v_b_2686_ = v___x_2725_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v___x_2737_, lean_object* v_original_2738_, lean_object* v___x_2739_, lean_object* v_edited_2740_, lean_object* v_as_2741_, lean_object* v_sz_2742_, lean_object* v_i_2743_, lean_object* v_b_2744_){
_start:
{
size_t v_sz_boxed_2745_; size_t v_i_boxed_2746_; lean_object* v_res_2747_; 
v_sz_boxed_2745_ = lean_unbox_usize(v_sz_2742_);
lean_dec(v_sz_2742_);
v_i_boxed_2746_ = lean_unbox_usize(v_i_2743_);
lean_dec(v_i_2743_);
v_res_2747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2737_, v_original_2738_, v___x_2739_, v_edited_2740_, v_as_2741_, v_sz_boxed_2745_, v_i_boxed_2746_, v_b_2744_);
lean_dec_ref(v_as_2741_);
lean_dec_ref(v_edited_2740_);
lean_dec(v___x_2739_);
lean_dec_ref(v_original_2738_);
lean_dec(v___x_2737_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v___x_2748_, lean_object* v_edited_2749_, lean_object* v___x_2750_, lean_object* v_original_2751_, lean_object* v_as_2752_, size_t v_sz_2753_, size_t v_i_2754_, lean_object* v_b_2755_){
_start:
{
uint8_t v___x_2756_; 
v___x_2756_ = lean_usize_dec_lt(v_i_2754_, v_sz_2753_);
if (v___x_2756_ == 0)
{
return v_b_2755_;
}
else
{
lean_object* v_snd_2757_; lean_object* v_fst_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2805_; 
v_snd_2757_ = lean_ctor_get(v_b_2755_, 1);
v_fst_2758_ = lean_ctor_get(v_b_2755_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_b_2755_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2760_ = v_b_2755_;
v_isShared_2761_ = v_isSharedCheck_2805_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_snd_2757_);
lean_inc(v_fst_2758_);
lean_dec(v_b_2755_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2805_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v_fst_2762_; lean_object* v_snd_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2804_; 
v_fst_2762_ = lean_ctor_get(v_snd_2757_, 0);
v_snd_2763_ = lean_ctor_get(v_snd_2757_, 1);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_snd_2757_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2765_ = v_snd_2757_;
v_isShared_2766_ = v_isSharedCheck_2804_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_snd_2763_);
lean_inc(v_fst_2762_);
lean_dec(v_snd_2757_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2804_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v_a_2767_; lean_object* v___x_2769_; 
v_a_2767_ = lean_array_uget_borrowed(v_as_2752_, v_i_2754_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v_fst_2762_);
lean_ctor_set(v___x_2765_, 0, v_fst_2758_);
v___x_2769_ = v___x_2765_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_fst_2758_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_fst_2762_);
v___x_2769_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2770_; lean_object* v_fst_2771_; lean_object* v_snd_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2802_; 
v___x_2770_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2750_, v_original_2751_, v_a_2767_, v___x_2769_);
v_fst_2771_ = lean_ctor_get(v___x_2770_, 0);
v_snd_2772_ = lean_ctor_get(v___x_2770_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2774_ = v___x_2770_;
v_isShared_2775_ = v_isSharedCheck_2802_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_snd_2772_);
lean_inc(v_fst_2771_);
lean_dec(v___x_2770_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2802_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 1, v_snd_2763_);
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_fst_2771_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_snd_2763_);
v___x_2777_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; lean_object* v_fst_2779_; lean_object* v_snd_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2800_; 
v___x_2778_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2748_, v_edited_2749_, v_a_2767_, v___x_2777_);
v_fst_2779_ = lean_ctor_get(v___x_2778_, 0);
v_snd_2780_ = lean_ctor_get(v___x_2778_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2782_ = v___x_2778_;
v_isShared_2783_ = v_isSharedCheck_2800_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_snd_2780_);
lean_inc(v_fst_2779_);
lean_dec(v___x_2778_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2800_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
uint8_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2784_ = 2;
v___x_2785_ = lean_box(v___x_2784_);
lean_inc(v_a_2767_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 1, v_a_2767_);
lean_ctor_set(v___x_2782_, 0, v___x_2785_);
v___x_2787_ = v___x_2782_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_a_2767_);
v___x_2787_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2788_ = lean_array_push(v_fst_2779_, v___x_2787_);
v___x_2789_ = lean_unsigned_to_nat(1u);
v___x_2790_ = lean_nat_add(v_snd_2772_, v___x_2789_);
lean_dec(v_snd_2772_);
v___x_2791_ = lean_nat_add(v_snd_2780_, v___x_2789_);
lean_dec(v_snd_2780_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 1, v___x_2791_);
lean_ctor_set(v___x_2760_, 0, v___x_2790_);
v___x_2793_ = v___x_2760_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; size_t v___x_2795_; size_t v___x_2796_; lean_object* v___x_2797_; 
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2788_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = ((size_t)1ULL);
v___x_2796_ = lean_usize_add(v_i_2754_, v___x_2795_);
v___x_2797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2750_, v_original_2751_, v___x_2748_, v_edited_2749_, v_as_2752_, v_sz_2753_, v___x_2796_, v___x_2794_);
return v___x_2797_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v___x_2806_, lean_object* v_edited_2807_, lean_object* v___x_2808_, lean_object* v_original_2809_, lean_object* v_as_2810_, lean_object* v_sz_2811_, lean_object* v_i_2812_, lean_object* v_b_2813_){
_start:
{
size_t v_sz_boxed_2814_; size_t v_i_boxed_2815_; lean_object* v_res_2816_; 
v_sz_boxed_2814_ = lean_unbox_usize(v_sz_2811_);
lean_dec(v_sz_2811_);
v_i_boxed_2815_ = lean_unbox_usize(v_i_2812_);
lean_dec(v_i_2812_);
v_res_2816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_2806_, v_edited_2807_, v___x_2808_, v_original_2809_, v_as_2810_, v_sz_boxed_2814_, v_i_boxed_2815_, v_b_2813_);
lean_dec_ref(v_as_2810_);
lean_dec_ref(v_original_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v_edited_2807_);
lean_dec(v___x_2806_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_2817_, lean_object* v_original_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_fst_2820_; lean_object* v_snd_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2840_; 
v_fst_2820_ = lean_ctor_get(v_a_2819_, 0);
v_snd_2821_ = lean_ctor_get(v_a_2819_, 1);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2823_ = v_a_2819_;
v_isShared_2824_ = v_isSharedCheck_2840_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_snd_2821_);
lean_inc(v_fst_2820_);
lean_dec(v_a_2819_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2840_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
uint8_t v___x_2825_; 
v___x_2825_ = lean_nat_dec_lt(v_snd_2821_, v___x_2817_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2827_; 
if (v_isShared_2824_ == 0)
{
v___x_2827_ = v___x_2823_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_fst_2820_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_snd_2821_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
else
{
uint8_t v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2829_ = 1;
v___x_2830_ = lean_array_fget_borrowed(v_original_2818_, v_snd_2821_);
v___x_2831_ = lean_box(v___x_2829_);
lean_inc(v___x_2830_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v___x_2830_);
lean_ctor_set(v___x_2823_, 0, v___x_2831_);
v___x_2833_ = v___x_2823_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2831_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___x_2830_);
v___x_2833_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2834_ = lean_array_push(v_fst_2820_, v___x_2833_);
v___x_2835_ = lean_unsigned_to_nat(1u);
v___x_2836_ = lean_nat_add(v_snd_2821_, v___x_2835_);
lean_dec(v_snd_2821_);
v___x_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2834_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v_a_2819_ = v___x_2837_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_2841_, lean_object* v_original_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_2841_, v_original_2842_, v_a_2843_);
lean_dec_ref(v_original_2842_);
lean_dec(v___x_2841_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_2845_, size_t v_i_2846_, lean_object* v_bs_2847_){
_start:
{
uint8_t v___x_2848_; 
v___x_2848_ = lean_usize_dec_lt(v_i_2846_, v_sz_2845_);
if (v___x_2848_ == 0)
{
return v_bs_2847_;
}
else
{
lean_object* v_v_2849_; lean_object* v___x_2850_; lean_object* v_bs_x27_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; size_t v___x_2855_; size_t v___x_2856_; lean_object* v___x_2857_; 
v_v_2849_ = lean_array_uget(v_bs_2847_, v_i_2846_);
v___x_2850_ = lean_unsigned_to_nat(0u);
v_bs_x27_2851_ = lean_array_uset(v_bs_2847_, v_i_2846_, v___x_2850_);
v___x_2852_ = 0;
v___x_2853_ = lean_box(v___x_2852_);
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v_v_2849_);
v___x_2855_ = ((size_t)1ULL);
v___x_2856_ = lean_usize_add(v_i_2846_, v___x_2855_);
v___x_2857_ = lean_array_uset(v_bs_x27_2851_, v_i_2846_, v___x_2854_);
v_i_2846_ = v___x_2856_;
v_bs_2847_ = v___x_2857_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_2859_, lean_object* v_i_2860_, lean_object* v_bs_2861_){
_start:
{
size_t v_sz_boxed_2862_; size_t v_i_boxed_2863_; lean_object* v_res_2864_; 
v_sz_boxed_2862_ = lean_unbox_usize(v_sz_2859_);
lean_dec(v_sz_2859_);
v_i_boxed_2863_ = lean_unbox_usize(v_i_2860_);
lean_dec(v_i_2860_);
v_res_2864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_2862_, v_i_boxed_2863_, v_bs_2861_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_2865_, lean_object* v_edited_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v_fst_2868_; lean_object* v_snd_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2888_; 
v_fst_2868_ = lean_ctor_get(v_a_2867_, 0);
v_snd_2869_ = lean_ctor_get(v_a_2867_, 1);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_a_2867_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2871_ = v_a_2867_;
v_isShared_2872_ = v_isSharedCheck_2888_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_snd_2869_);
lean_inc(v_fst_2868_);
lean_dec(v_a_2867_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2888_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
uint8_t v___x_2873_; 
v___x_2873_ = lean_nat_dec_lt(v_snd_2869_, v___x_2865_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2875_; 
if (v_isShared_2872_ == 0)
{
v___x_2875_ = v___x_2871_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_fst_2868_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_snd_2869_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
else
{
uint8_t v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2877_ = 0;
v___x_2878_ = lean_array_fget_borrowed(v_edited_2866_, v_snd_2869_);
v___x_2879_ = lean_box(v___x_2877_);
lean_inc(v___x_2878_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 1, v___x_2878_);
lean_ctor_set(v___x_2871_, 0, v___x_2879_);
v___x_2881_ = v___x_2871_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2879_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v___x_2878_);
v___x_2881_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2882_ = lean_array_push(v_fst_2868_, v___x_2881_);
v___x_2883_ = lean_unsigned_to_nat(1u);
v___x_2884_ = lean_nat_add(v_snd_2869_, v___x_2883_);
lean_dec(v_snd_2869_);
v___x_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2882_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v_a_2867_ = v___x_2885_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_2889_, lean_object* v_edited_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_2889_, v_edited_2890_, v_a_2891_);
lean_dec_ref(v_edited_2890_);
lean_dec(v___x_2889_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(lean_object* v_x_2893_, lean_object* v_x_2894_){
_start:
{
if (lean_obj_tag(v_x_2894_) == 0)
{
lean_inc(v_x_2893_);
return v_x_2893_;
}
else
{
lean_object* v_key_2895_; lean_object* v_value_2896_; lean_object* v_tail_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v_key_2895_ = lean_ctor_get(v_x_2894_, 0);
v_value_2896_ = lean_ctor_get(v_x_2894_, 1);
v_tail_2897_ = lean_ctor_get(v_x_2894_, 2);
v___x_2898_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2893_, v_tail_2897_);
lean_inc(v_value_2896_);
lean_inc(v_key_2895_);
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v_key_2895_);
lean_ctor_set(v___x_2899_, 1, v_value_2896_);
v___x_2900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v___x_2898_);
return v___x_2900_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17___boxed(lean_object* v_x_2901_, lean_object* v_x_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2901_, v_x_2902_);
lean_dec(v_x_2902_);
lean_dec(v_x_2901_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(lean_object* v_as_2904_, size_t v_i_2905_, size_t v_stop_2906_, lean_object* v_b_2907_){
_start:
{
uint8_t v___x_2908_; 
v___x_2908_ = lean_usize_dec_eq(v_i_2905_, v_stop_2906_);
if (v___x_2908_ == 0)
{
size_t v___x_2909_; size_t v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2909_ = ((size_t)1ULL);
v___x_2910_ = lean_usize_sub(v_i_2905_, v___x_2909_);
v___x_2911_ = lean_array_uget_borrowed(v_as_2904_, v___x_2910_);
v___x_2912_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_b_2907_, v___x_2911_);
lean_dec(v_b_2907_);
v_i_2905_ = v___x_2910_;
v_b_2907_ = v___x_2912_;
goto _start;
}
else
{
return v_b_2907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18___boxed(lean_object* v_as_2914_, lean_object* v_i_2915_, lean_object* v_stop_2916_, lean_object* v_b_2917_){
_start:
{
size_t v_i_boxed_2918_; size_t v_stop_boxed_2919_; lean_object* v_res_2920_; 
v_i_boxed_2918_ = lean_unbox_usize(v_i_2915_);
lean_dec(v_i_2915_);
v_stop_boxed_2919_ = lean_unbox_usize(v_stop_2916_);
lean_dec(v_stop_2916_);
v_res_2920_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_as_2914_, v_i_boxed_2918_, v_stop_boxed_2919_, v_b_2917_);
lean_dec_ref(v_as_2914_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(lean_object* v_left_2921_, lean_object* v_right_2922_, lean_object* v_pref_2923_){
_start:
{
lean_object* v_start_2924_; lean_object* v_stop_2925_; lean_object* v_start_2926_; lean_object* v_stop_2927_; lean_object* v_i_2928_; uint8_t v___y_2930_; lean_object* v___x_2944_; uint8_t v___x_2945_; 
v_start_2924_ = lean_ctor_get(v_left_2921_, 1);
v_stop_2925_ = lean_ctor_get(v_left_2921_, 2);
v_start_2926_ = lean_ctor_get(v_right_2922_, 1);
v_stop_2927_ = lean_ctor_get(v_right_2922_, 2);
v_i_2928_ = lean_array_get_size(v_pref_2923_);
v___x_2944_ = lean_nat_sub(v_stop_2925_, v_start_2924_);
v___x_2945_ = lean_nat_dec_lt(v_i_2928_, v___x_2944_);
lean_dec(v___x_2944_);
if (v___x_2945_ == 0)
{
v___y_2930_ = v___x_2945_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2946_ = lean_nat_sub(v_stop_2927_, v_start_2926_);
v___x_2947_ = lean_nat_dec_lt(v_i_2928_, v___x_2946_);
lean_dec(v___x_2946_);
v___y_2930_ = v___x_2947_;
goto v___jp_2929_;
}
v___jp_2929_:
{
if (v___y_2930_ == 0)
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2931_ = l_Subarray_drop___redArg(v_left_2921_, v_i_2928_);
v___x_2932_ = l_Subarray_drop___redArg(v_right_2922_, v_i_2928_);
v___x_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2931_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2934_, 0, v_pref_2923_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
return v___x_2934_;
}
else
{
lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v___x_2935_ = l_Subarray_get___redArg(v_left_2921_, v_i_2928_);
v___x_2936_ = l_Subarray_get___redArg(v_right_2922_, v_i_2928_);
v___x_2937_ = lean_string_dec_eq(v___x_2935_, v___x_2936_);
lean_dec(v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec(v___x_2935_);
v___x_2938_ = l_Subarray_drop___redArg(v_left_2921_, v_i_2928_);
v___x_2939_ = l_Subarray_drop___redArg(v_right_2922_, v_i_2928_);
v___x_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2938_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2941_, 0, v_pref_2923_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
return v___x_2941_;
}
else
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_array_push(v_pref_2923_, v___x_2935_);
v_pref_2923_ = v___x_2942_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(lean_object* v_left_2950_, lean_object* v_right_2951_){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_2953_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(v_left_2950_, v_right_2951_, v___x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(lean_object* v_a_2954_, lean_object* v_b_2955_, lean_object* v_x_2956_){
_start:
{
if (lean_obj_tag(v_x_2956_) == 0)
{
lean_dec(v_b_2955_);
lean_dec_ref(v_a_2954_);
return v_x_2956_;
}
else
{
lean_object* v_key_2957_; lean_object* v_value_2958_; lean_object* v_tail_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2971_; 
v_key_2957_ = lean_ctor_get(v_x_2956_, 0);
v_value_2958_ = lean_ctor_get(v_x_2956_, 1);
v_tail_2959_ = lean_ctor_get(v_x_2956_, 2);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_x_2956_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2961_ = v_x_2956_;
v_isShared_2962_ = v_isSharedCheck_2971_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_tail_2959_);
lean_inc(v_value_2958_);
lean_inc(v_key_2957_);
lean_dec(v_x_2956_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2971_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
uint8_t v___x_2963_; 
v___x_2963_ = lean_string_dec_eq(v_key_2957_, v_a_2954_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2964_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_2954_, v_b_2955_, v_tail_2959_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 2, v___x_2964_);
v___x_2966_ = v___x_2961_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_key_2957_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_value_2958_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
else
{
lean_object* v___x_2969_; 
lean_dec(v_value_2958_);
lean_dec(v_key_2957_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v_b_2955_);
lean_ctor_set(v___x_2961_, 0, v_a_2954_);
v___x_2969_ = v___x_2961_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2954_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_b_2955_);
lean_ctor_set(v_reuseFailAlloc_2970_, 2, v_tail_2959_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2972_, lean_object* v_x_2973_){
_start:
{
if (lean_obj_tag(v_x_2973_) == 0)
{
return v_x_2972_;
}
else
{
lean_object* v_key_2974_; lean_object* v_value_2975_; lean_object* v_tail_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2999_; 
v_key_2974_ = lean_ctor_get(v_x_2973_, 0);
v_value_2975_ = lean_ctor_get(v_x_2973_, 1);
v_tail_2976_ = lean_ctor_get(v_x_2973_, 2);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_x_2973_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2978_ = v_x_2973_;
v_isShared_2979_ = v_isSharedCheck_2999_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_tail_2976_);
lean_inc(v_value_2975_);
lean_inc(v_key_2974_);
lean_dec(v_x_2973_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2999_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; uint64_t v___x_2981_; uint64_t v___x_2982_; uint64_t v___x_2983_; uint64_t v_fold_2984_; uint64_t v___x_2985_; uint64_t v___x_2986_; uint64_t v___x_2987_; size_t v___x_2988_; size_t v___x_2989_; size_t v___x_2990_; size_t v___x_2991_; size_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2980_ = lean_array_get_size(v_x_2972_);
v___x_2981_ = lean_string_hash(v_key_2974_);
v___x_2982_ = 32ULL;
v___x_2983_ = lean_uint64_shift_right(v___x_2981_, v___x_2982_);
v_fold_2984_ = lean_uint64_xor(v___x_2981_, v___x_2983_);
v___x_2985_ = 16ULL;
v___x_2986_ = lean_uint64_shift_right(v_fold_2984_, v___x_2985_);
v___x_2987_ = lean_uint64_xor(v_fold_2984_, v___x_2986_);
v___x_2988_ = lean_uint64_to_usize(v___x_2987_);
v___x_2989_ = lean_usize_of_nat(v___x_2980_);
v___x_2990_ = ((size_t)1ULL);
v___x_2991_ = lean_usize_sub(v___x_2989_, v___x_2990_);
v___x_2992_ = lean_usize_land(v___x_2988_, v___x_2991_);
v___x_2993_ = lean_array_uget_borrowed(v_x_2972_, v___x_2992_);
lean_inc(v___x_2993_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 2, v___x_2993_);
v___x_2995_ = v___x_2978_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_key_2974_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_value_2975_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v___x_2993_);
v___x_2995_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_array_uset(v_x_2972_, v___x_2992_, v___x_2995_);
v_x_2972_ = v___x_2996_;
v_x_2973_ = v_tail_2976_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(lean_object* v_i_3000_, lean_object* v_source_3001_, lean_object* v_target_3002_){
_start:
{
lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3003_ = lean_array_get_size(v_source_3001_);
v___x_3004_ = lean_nat_dec_lt(v_i_3000_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_dec_ref(v_source_3001_);
lean_dec(v_i_3000_);
return v_target_3002_;
}
else
{
lean_object* v_es_3005_; lean_object* v___x_3006_; lean_object* v_source_3007_; lean_object* v_target_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v_es_3005_ = lean_array_fget(v_source_3001_, v_i_3000_);
v___x_3006_ = lean_box(0);
v_source_3007_ = lean_array_fset(v_source_3001_, v_i_3000_, v___x_3006_);
v_target_3008_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_target_3002_, v_es_3005_);
v___x_3009_ = lean_unsigned_to_nat(1u);
v___x_3010_ = lean_nat_add(v_i_3000_, v___x_3009_);
lean_dec(v_i_3000_);
v_i_3000_ = v___x_3010_;
v_source_3001_ = v_source_3007_;
v_target_3002_ = v_target_3008_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(lean_object* v_data_3012_){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v_nbuckets_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3013_ = lean_array_get_size(v_data_3012_);
v___x_3014_ = lean_unsigned_to_nat(2u);
v_nbuckets_3015_ = lean_nat_mul(v___x_3013_, v___x_3014_);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_box(0);
v___x_3018_ = lean_mk_array(v_nbuckets_3015_, v___x_3017_);
v___x_3019_ = lean_array_propagate_mark(v_data_3012_, v___x_3018_);
v___x_3020_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v___x_3016_, v_data_3012_, v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(lean_object* v_a_3021_, lean_object* v_x_3022_){
_start:
{
if (lean_obj_tag(v_x_3022_) == 0)
{
uint8_t v___x_3023_; 
v___x_3023_ = 0;
return v___x_3023_;
}
else
{
lean_object* v_key_3024_; lean_object* v_tail_3025_; uint8_t v___x_3026_; 
v_key_3024_ = lean_ctor_get(v_x_3022_, 0);
v_tail_3025_ = lean_ctor_get(v_x_3022_, 2);
v___x_3026_ = lean_string_dec_eq(v_key_3024_, v_a_3021_);
if (v___x_3026_ == 0)
{
v_x_3022_ = v_tail_3025_;
goto _start;
}
else
{
return v___x_3026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg___boxed(lean_object* v_a_3028_, lean_object* v_x_3029_){
_start:
{
uint8_t v_res_3030_; lean_object* v_r_3031_; 
v_res_3030_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_3028_, v_x_3029_);
lean_dec(v_x_3029_);
lean_dec_ref(v_a_3028_);
v_r_3031_ = lean_box(v_res_3030_);
return v_r_3031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(lean_object* v_m_3032_, lean_object* v_a_3033_, lean_object* v_b_3034_){
_start:
{
lean_object* v_size_3035_; lean_object* v_buckets_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3079_; 
v_size_3035_ = lean_ctor_get(v_m_3032_, 0);
v_buckets_3036_ = lean_ctor_get(v_m_3032_, 1);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_m_3032_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3038_ = v_m_3032_;
v_isShared_3039_ = v_isSharedCheck_3079_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_buckets_3036_);
lean_inc(v_size_3035_);
lean_dec(v_m_3032_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3079_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; uint64_t v___x_3041_; uint64_t v___x_3042_; uint64_t v___x_3043_; uint64_t v_fold_3044_; uint64_t v___x_3045_; uint64_t v___x_3046_; uint64_t v___x_3047_; size_t v___x_3048_; size_t v___x_3049_; size_t v___x_3050_; size_t v___x_3051_; size_t v___x_3052_; lean_object* v_bkt_3053_; uint8_t v___x_3054_; 
v___x_3040_ = lean_array_get_size(v_buckets_3036_);
v___x_3041_ = lean_string_hash(v_a_3033_);
v___x_3042_ = 32ULL;
v___x_3043_ = lean_uint64_shift_right(v___x_3041_, v___x_3042_);
v_fold_3044_ = lean_uint64_xor(v___x_3041_, v___x_3043_);
v___x_3045_ = 16ULL;
v___x_3046_ = lean_uint64_shift_right(v_fold_3044_, v___x_3045_);
v___x_3047_ = lean_uint64_xor(v_fold_3044_, v___x_3046_);
v___x_3048_ = lean_uint64_to_usize(v___x_3047_);
v___x_3049_ = lean_usize_of_nat(v___x_3040_);
v___x_3050_ = ((size_t)1ULL);
v___x_3051_ = lean_usize_sub(v___x_3049_, v___x_3050_);
v___x_3052_ = lean_usize_land(v___x_3048_, v___x_3051_);
v_bkt_3053_ = lean_array_uget_borrowed(v_buckets_3036_, v___x_3052_);
v___x_3054_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_3033_, v_bkt_3053_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; lean_object* v_size_x27_3056_; lean_object* v___x_3057_; lean_object* v_buckets_x27_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3055_ = lean_unsigned_to_nat(1u);
v_size_x27_3056_ = lean_nat_add(v_size_3035_, v___x_3055_);
lean_dec(v_size_3035_);
lean_inc(v_bkt_3053_);
v___x_3057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3057_, 0, v_a_3033_);
lean_ctor_set(v___x_3057_, 1, v_b_3034_);
lean_ctor_set(v___x_3057_, 2, v_bkt_3053_);
v_buckets_x27_3058_ = lean_array_uset(v_buckets_3036_, v___x_3052_, v___x_3057_);
v___x_3059_ = lean_unsigned_to_nat(4u);
v___x_3060_ = lean_nat_mul(v_size_x27_3056_, v___x_3059_);
v___x_3061_ = lean_unsigned_to_nat(3u);
v___x_3062_ = lean_nat_div(v___x_3060_, v___x_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_array_get_size(v_buckets_x27_3058_);
v___x_3064_ = lean_nat_dec_le(v___x_3062_, v___x_3063_);
lean_dec(v___x_3062_);
if (v___x_3064_ == 0)
{
lean_object* v_val_3065_; lean_object* v___x_3067_; 
v_val_3065_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_buckets_x27_3058_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 1, v_val_3065_);
lean_ctor_set(v___x_3038_, 0, v_size_x27_3056_);
v___x_3067_ = v___x_3038_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_size_x27_3056_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_val_3065_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
else
{
lean_object* v___x_3070_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 1, v_buckets_x27_3058_);
lean_ctor_set(v___x_3038_, 0, v_size_x27_3056_);
v___x_3070_ = v___x_3038_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_size_x27_3056_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v_buckets_x27_3058_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
else
{
lean_object* v___x_3072_; lean_object* v_buckets_x27_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
lean_inc(v_bkt_3053_);
v___x_3072_ = lean_box(0);
v_buckets_x27_3073_ = lean_array_uset(v_buckets_3036_, v___x_3052_, v___x_3072_);
v___x_3074_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_3033_, v_b_3034_, v_bkt_3053_);
v___x_3075_ = lean_array_uset(v_buckets_x27_3073_, v___x_3052_, v___x_3074_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 1, v___x_3075_);
v___x_3077_ = v___x_3038_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_size_3035_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(lean_object* v_a_3080_, lean_object* v_x_3081_){
_start:
{
if (lean_obj_tag(v_x_3081_) == 0)
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_box(0);
return v___x_3082_;
}
else
{
lean_object* v_key_3083_; lean_object* v_value_3084_; lean_object* v_tail_3085_; uint8_t v___x_3086_; 
v_key_3083_ = lean_ctor_get(v_x_3081_, 0);
v_value_3084_ = lean_ctor_get(v_x_3081_, 1);
v_tail_3085_ = lean_ctor_get(v_x_3081_, 2);
v___x_3086_ = lean_string_dec_eq(v_key_3083_, v_a_3080_);
if (v___x_3086_ == 0)
{
v_x_3081_ = v_tail_3085_;
goto _start;
}
else
{
lean_object* v___x_3088_; 
lean_inc(v_value_3084_);
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v_value_3084_);
return v___x_3088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg___boxed(lean_object* v_a_3089_, lean_object* v_x_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3089_, v_x_3090_);
lean_dec(v_x_3090_);
lean_dec_ref(v_a_3089_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(lean_object* v_m_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v_buckets_3094_; lean_object* v___x_3095_; uint64_t v___x_3096_; uint64_t v___x_3097_; uint64_t v___x_3098_; uint64_t v_fold_3099_; uint64_t v___x_3100_; uint64_t v___x_3101_; uint64_t v___x_3102_; size_t v___x_3103_; size_t v___x_3104_; size_t v___x_3105_; size_t v___x_3106_; size_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_buckets_3094_ = lean_ctor_get(v_m_3092_, 1);
v___x_3095_ = lean_array_get_size(v_buckets_3094_);
v___x_3096_ = lean_string_hash(v_a_3093_);
v___x_3097_ = 32ULL;
v___x_3098_ = lean_uint64_shift_right(v___x_3096_, v___x_3097_);
v_fold_3099_ = lean_uint64_xor(v___x_3096_, v___x_3098_);
v___x_3100_ = 16ULL;
v___x_3101_ = lean_uint64_shift_right(v_fold_3099_, v___x_3100_);
v___x_3102_ = lean_uint64_xor(v_fold_3099_, v___x_3101_);
v___x_3103_ = lean_uint64_to_usize(v___x_3102_);
v___x_3104_ = lean_usize_of_nat(v___x_3095_);
v___x_3105_ = ((size_t)1ULL);
v___x_3106_ = lean_usize_sub(v___x_3104_, v___x_3105_);
v___x_3107_ = lean_usize_land(v___x_3103_, v___x_3106_);
v___x_3108_ = lean_array_uget_borrowed(v_buckets_3094_, v___x_3107_);
v___x_3109_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3093_, v___x_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg___boxed(lean_object* v_m_3110_, lean_object* v_a_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_3110_, v_a_3111_);
lean_dec_ref(v_a_3111_);
lean_dec_ref(v_m_3110_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(lean_object* v_histogram_3113_, lean_object* v_index_3114_, lean_object* v_val_3115_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3113_, v_val_3115_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3117_ = lean_unsigned_to_nat(1u);
v___x_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3118_, 0, v_index_3114_);
v___x_3119_ = lean_unsigned_to_nat(0u);
v___x_3120_ = lean_box(0);
v___x_3121_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3117_);
lean_ctor_set(v___x_3121_, 1, v___x_3118_);
lean_ctor_set(v___x_3121_, 2, v___x_3119_);
lean_ctor_set(v___x_3121_, 3, v___x_3120_);
v___x_3122_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3113_, v_val_3115_, v___x_3121_);
return v___x_3122_;
}
else
{
lean_object* v_val_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3144_; 
v_val_3123_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3125_ = v___x_3116_;
v_isShared_3126_ = v_isSharedCheck_3144_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_val_3123_);
lean_dec(v___x_3116_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3144_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v_leftCount_3127_; lean_object* v_rightCount_3128_; lean_object* v_rightIndex_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3142_; 
v_leftCount_3127_ = lean_ctor_get(v_val_3123_, 0);
v_rightCount_3128_ = lean_ctor_get(v_val_3123_, 2);
v_rightIndex_3129_ = lean_ctor_get(v_val_3123_, 3);
v_isSharedCheck_3142_ = !lean_is_exclusive(v_val_3123_);
if (v_isSharedCheck_3142_ == 0)
{
lean_object* v_unused_3143_; 
v_unused_3143_ = lean_ctor_get(v_val_3123_, 1);
lean_dec(v_unused_3143_);
v___x_3131_ = v_val_3123_;
v_isShared_3132_ = v_isSharedCheck_3142_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_rightIndex_3129_);
lean_inc(v_rightCount_3128_);
lean_inc(v_leftCount_3127_);
lean_dec(v_val_3123_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3142_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3133_ = lean_unsigned_to_nat(1u);
v___x_3134_ = lean_nat_add(v_leftCount_3127_, v___x_3133_);
lean_dec(v_leftCount_3127_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v_index_3114_);
v___x_3136_ = v___x_3125_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_index_3114_);
v___x_3136_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 1, v___x_3136_);
lean_ctor_set(v___x_3131_, 0, v___x_3134_);
v___x_3138_ = v___x_3131_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3140_, 2, v_rightCount_3128_);
lean_ctor_set(v_reuseFailAlloc_3140_, 3, v_rightIndex_3129_);
v___x_3138_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3139_; 
v___x_3139_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3113_, v_val_3115_, v___x_3138_);
return v___x_3139_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(lean_object* v_upperBound_3145_, lean_object* v_fst_3146_, lean_object* v___x_3147_, lean_object* v_fst_3148_, lean_object* v_a_3149_, lean_object* v_b_3150_){
_start:
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_nat_dec_lt(v_a_3149_, v_upperBound_3145_);
if (v___x_3151_ == 0)
{
lean_dec(v_a_3149_);
return v_b_3150_;
}
else
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3152_ = l_Subarray_get___redArg(v_fst_3148_, v_a_3149_);
lean_inc(v_a_3149_);
v___x_3153_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_b_3150_, v_a_3149_, v___x_3152_);
v___x_3154_ = lean_unsigned_to_nat(1u);
v___x_3155_ = lean_nat_add(v_a_3149_, v___x_3154_);
lean_dec(v_a_3149_);
v_a_3149_ = v___x_3155_;
v_b_3150_ = v___x_3153_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_upperBound_3157_, lean_object* v_fst_3158_, lean_object* v___x_3159_, lean_object* v_fst_3160_, lean_object* v_a_3161_, lean_object* v_b_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3157_, v_fst_3158_, v___x_3159_, v_fst_3160_, v_a_3161_, v_b_3162_);
lean_dec_ref(v_fst_3160_);
lean_dec(v___x_3159_);
lean_dec_ref(v_fst_3158_);
lean_dec(v_upperBound_3157_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(lean_object* v_as_x27_3164_, lean_object* v_b_3165_){
_start:
{
if (lean_obj_tag(v_as_x27_3164_) == 0)
{
return v_b_3165_;
}
else
{
lean_object* v_head_3166_; lean_object* v_snd_3167_; lean_object* v_leftIndex_3168_; 
v_head_3166_ = lean_ctor_get(v_as_x27_3164_, 0);
v_snd_3167_ = lean_ctor_get(v_head_3166_, 1);
v_leftIndex_3168_ = lean_ctor_get(v_snd_3167_, 1);
if (lean_obj_tag(v_leftIndex_3168_) == 1)
{
lean_object* v_rightIndex_3169_; 
v_rightIndex_3169_ = lean_ctor_get(v_snd_3167_, 3);
if (lean_obj_tag(v_rightIndex_3169_) == 1)
{
if (lean_obj_tag(v_b_3165_) == 0)
{
lean_object* v_tail_3170_; lean_object* v_fst_3171_; lean_object* v_leftCount_3172_; lean_object* v_rightCount_3173_; lean_object* v_val_3174_; lean_object* v_val_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v_tail_3170_ = lean_ctor_get(v_as_x27_3164_, 1);
v_fst_3171_ = lean_ctor_get(v_head_3166_, 0);
v_leftCount_3172_ = lean_ctor_get(v_snd_3167_, 0);
v_rightCount_3173_ = lean_ctor_get(v_snd_3167_, 2);
v_val_3174_ = lean_ctor_get(v_leftIndex_3168_, 0);
v_val_3175_ = lean_ctor_get(v_rightIndex_3169_, 0);
v___x_3176_ = lean_nat_add(v_leftCount_3172_, v_rightCount_3173_);
lean_inc(v_val_3175_);
lean_inc(v_val_3174_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v_val_3174_);
lean_ctor_set(v___x_3177_, 1, v_val_3175_);
lean_inc(v_fst_3171_);
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v_fst_3171_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3176_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
v_as_x27_3164_ = v_tail_3170_;
v_b_3165_ = v___x_3180_;
goto _start;
}
else
{
lean_object* v_val_3182_; lean_object* v_tail_3183_; lean_object* v_fst_3184_; lean_object* v_leftCount_3185_; lean_object* v_rightCount_3186_; lean_object* v_val_3187_; lean_object* v_val_3188_; lean_object* v_fst_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3210_; 
v_val_3182_ = lean_ctor_get(v_b_3165_, 0);
lean_inc(v_val_3182_);
v_tail_3183_ = lean_ctor_get(v_as_x27_3164_, 1);
v_fst_3184_ = lean_ctor_get(v_head_3166_, 0);
v_leftCount_3185_ = lean_ctor_get(v_snd_3167_, 0);
v_rightCount_3186_ = lean_ctor_get(v_snd_3167_, 2);
v_val_3187_ = lean_ctor_get(v_leftIndex_3168_, 0);
v_val_3188_ = lean_ctor_get(v_rightIndex_3169_, 0);
v_fst_3189_ = lean_ctor_get(v_val_3182_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_val_3182_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v_val_3182_, 1);
lean_dec(v_unused_3211_);
v___x_3191_ = v_val_3182_;
v_isShared_3192_ = v_isSharedCheck_3210_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_fst_3189_);
lean_dec(v_val_3182_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3210_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; uint8_t v___x_3194_; 
v___x_3193_ = lean_nat_add(v_leftCount_3185_, v_rightCount_3186_);
v___x_3194_ = lean_nat_dec_lt(v___x_3193_, v_fst_3189_);
lean_dec(v_fst_3189_);
if (v___x_3194_ == 0)
{
lean_dec(v___x_3193_);
lean_del_object(v___x_3191_);
v_as_x27_3164_ = v_tail_3183_;
goto _start;
}
else
{
lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3208_; 
v_isSharedCheck_3208_ = !lean_is_exclusive(v_b_3165_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v_b_3165_, 0);
lean_dec(v_unused_3209_);
v___x_3197_ = v_b_3165_;
v_isShared_3198_ = v_isSharedCheck_3208_;
goto v_resetjp_3196_;
}
else
{
lean_dec(v_b_3165_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3208_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
lean_inc(v_val_3188_);
lean_inc(v_val_3187_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v_val_3188_);
lean_ctor_set(v___x_3191_, 0, v_val_3187_);
v___x_3200_ = v___x_3191_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_val_3187_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_val_3188_);
v___x_3200_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
lean_inc(v_fst_3184_);
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_fst_3184_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3193_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3202_);
v___x_3204_ = v___x_3197_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
v_as_x27_3164_ = v_tail_3183_;
v_b_3165_ = v___x_3204_;
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
lean_object* v_tail_3212_; 
v_tail_3212_ = lean_ctor_get(v_as_x27_3164_, 1);
v_as_x27_3164_ = v_tail_3212_;
goto _start;
}
}
else
{
lean_object* v_tail_3214_; 
v_tail_3214_ = lean_ctor_get(v_as_x27_3164_, 1);
v_as_x27_3164_ = v_tail_3214_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg___boxed(lean_object* v_as_x27_3216_, lean_object* v_b_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3216_, v_b_3217_);
lean_dec(v_as_x27_3216_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(lean_object* v_histogram_3219_, lean_object* v_index_3220_, lean_object* v_val_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3219_, v_val_3221_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3223_ = lean_unsigned_to_nat(0u);
v___x_3224_ = lean_box(0);
v___x_3225_ = lean_unsigned_to_nat(1u);
v___x_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3226_, 0, v_index_3220_);
v___x_3227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3223_);
lean_ctor_set(v___x_3227_, 1, v___x_3224_);
lean_ctor_set(v___x_3227_, 2, v___x_3225_);
lean_ctor_set(v___x_3227_, 3, v___x_3226_);
v___x_3228_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3219_, v_val_3221_, v___x_3227_);
return v___x_3228_;
}
else
{
lean_object* v_val_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3250_; 
v_val_3229_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3231_ = v___x_3222_;
v_isShared_3232_ = v_isSharedCheck_3250_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_val_3229_);
lean_dec(v___x_3222_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3250_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v_leftCount_3233_; lean_object* v_leftIndex_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3247_; 
v_leftCount_3233_ = lean_ctor_get(v_val_3229_, 0);
v_leftIndex_3234_ = lean_ctor_get(v_val_3229_, 1);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_val_3229_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; lean_object* v_unused_3249_; 
v_unused_3248_ = lean_ctor_get(v_val_3229_, 3);
lean_dec(v_unused_3248_);
v_unused_3249_ = lean_ctor_get(v_val_3229_, 2);
lean_dec(v_unused_3249_);
v___x_3236_ = v_val_3229_;
v_isShared_3237_ = v_isSharedCheck_3247_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_leftIndex_3234_);
lean_inc(v_leftCount_3233_);
lean_dec(v_val_3229_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3247_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3238_ = lean_unsigned_to_nat(1u);
v___x_3239_ = lean_nat_add(v_leftCount_3233_, v___x_3238_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v_index_3220_);
v___x_3241_ = v___x_3231_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_index_3220_);
v___x_3241_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3243_; 
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 3, v___x_3241_);
lean_ctor_set(v___x_3236_, 2, v___x_3239_);
v___x_3243_ = v___x_3236_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_leftCount_3233_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_leftIndex_3234_);
lean_ctor_set(v_reuseFailAlloc_3245_, 2, v___x_3239_);
lean_ctor_set(v_reuseFailAlloc_3245_, 3, v___x_3241_);
v___x_3243_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3244_; 
v___x_3244_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3219_, v_val_3221_, v___x_3243_);
return v___x_3244_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(lean_object* v_upperBound_3251_, lean_object* v___x_3252_, lean_object* v_fst_3253_, lean_object* v___x_3254_, lean_object* v_a_3255_, lean_object* v_b_3256_){
_start:
{
uint8_t v___x_3257_; 
v___x_3257_ = lean_nat_dec_lt(v_a_3255_, v_upperBound_3251_);
if (v___x_3257_ == 0)
{
lean_dec(v_a_3255_);
return v_b_3256_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3258_ = l_Subarray_get___redArg(v_fst_3253_, v_a_3255_);
lean_inc(v_a_3255_);
v___x_3259_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_b_3256_, v_a_3255_, v___x_3258_);
v___x_3260_ = lean_unsigned_to_nat(1u);
v___x_3261_ = lean_nat_add(v_a_3255_, v___x_3260_);
lean_dec(v_a_3255_);
v_a_3255_ = v___x_3261_;
v_b_3256_ = v___x_3259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg___boxed(lean_object* v_upperBound_3263_, lean_object* v___x_3264_, lean_object* v_fst_3265_, lean_object* v___x_3266_, lean_object* v_a_3267_, lean_object* v_b_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3263_, v___x_3264_, v_fst_3265_, v___x_3266_, v_a_3267_, v_b_3268_);
lean_dec(v___x_3266_);
lean_dec_ref(v_fst_3265_);
lean_dec(v___x_3264_);
lean_dec(v_upperBound_3263_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(lean_object* v_a_3270_, lean_object* v_b_3271_){
_start:
{
lean_object* v_array_3272_; lean_object* v_start_3273_; lean_object* v_stop_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3287_; 
v_array_3272_ = lean_ctor_get(v_a_3270_, 0);
v_start_3273_ = lean_ctor_get(v_a_3270_, 1);
v_stop_3274_ = lean_ctor_get(v_a_3270_, 2);
v_isSharedCheck_3287_ = !lean_is_exclusive(v_a_3270_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3276_ = v_a_3270_;
v_isShared_3277_ = v_isSharedCheck_3287_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_stop_3274_);
lean_inc(v_start_3273_);
lean_inc(v_array_3272_);
lean_dec(v_a_3270_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3287_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
uint8_t v___x_3278_; 
v___x_3278_ = lean_nat_dec_lt(v_start_3273_, v_stop_3274_);
if (v___x_3278_ == 0)
{
lean_del_object(v___x_3276_);
lean_dec(v_stop_3274_);
lean_dec(v_start_3273_);
lean_dec_ref(v_array_3272_);
return v_b_3271_;
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3279_ = lean_unsigned_to_nat(1u);
v___x_3280_ = lean_nat_add(v_start_3273_, v___x_3279_);
lean_inc_ref(v_array_3272_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 1, v___x_3280_);
v___x_3282_ = v___x_3276_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_array_3272_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v_stop_3274_);
v___x_3282_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_array_fget(v_array_3272_, v_start_3273_);
lean_dec(v_start_3273_);
lean_dec_ref(v_array_3272_);
v___x_3284_ = lean_array_push(v_b_3271_, v___x_3283_);
v_a_3270_ = v___x_3282_;
v_b_3271_ = v___x_3284_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(lean_object* v_left_3288_, lean_object* v_right_3289_, lean_object* v_i_3290_){
_start:
{
lean_object* v_start_3291_; lean_object* v_stop_3292_; lean_object* v_start_3293_; lean_object* v_stop_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; uint8_t v___y_3299_; 
v_start_3291_ = lean_ctor_get(v_left_3288_, 1);
v_stop_3292_ = lean_ctor_get(v_left_3288_, 2);
v_start_3293_ = lean_ctor_get(v_right_3289_, 1);
v_stop_3294_ = lean_ctor_get(v_right_3289_, 2);
v___x_3295_ = lean_nat_sub(v_stop_3292_, v_start_3291_);
v___x_3296_ = lean_nat_dec_lt(v_i_3290_, v___x_3295_);
v___x_3297_ = lean_nat_sub(v_stop_3294_, v_start_3293_);
if (v___x_3296_ == 0)
{
v___y_3299_ = v___x_3296_;
goto v___jp_3298_;
}
else
{
uint8_t v___x_3326_; 
v___x_3326_ = lean_nat_dec_lt(v_i_3290_, v___x_3297_);
v___y_3299_ = v___x_3326_;
goto v___jp_3298_;
}
v___jp_3298_:
{
if (v___y_3299_ == 0)
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3300_ = lean_nat_sub(v___x_3295_, v_i_3290_);
lean_dec(v___x_3295_);
lean_inc_ref(v_left_3288_);
v___x_3301_ = l_Subarray_take___redArg(v_left_3288_, v___x_3300_);
v___x_3302_ = lean_nat_sub(v___x_3297_, v_i_3290_);
lean_dec(v_i_3290_);
lean_dec(v___x_3297_);
v___x_3303_ = l_Subarray_take___redArg(v_right_3289_, v___x_3302_);
lean_dec(v___x_3302_);
v___x_3304_ = l_Subarray_drop___redArg(v_left_3288_, v___x_3300_);
lean_dec(v___x_3300_);
v___x_3305_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3306_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3304_, v___x_3305_);
v___x_3307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3303_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3301_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
return v___x_3308_;
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3309_ = lean_nat_sub(v___x_3295_, v_i_3290_);
lean_dec(v___x_3295_);
v___x_3310_ = lean_unsigned_to_nat(1u);
v___x_3311_ = lean_nat_sub(v___x_3309_, v___x_3310_);
v___x_3312_ = l_Subarray_get___redArg(v_left_3288_, v___x_3311_);
lean_dec(v___x_3311_);
v___x_3313_ = lean_nat_sub(v___x_3297_, v_i_3290_);
lean_dec(v___x_3297_);
v___x_3314_ = lean_nat_sub(v___x_3313_, v___x_3310_);
v___x_3315_ = l_Subarray_get___redArg(v_right_3289_, v___x_3314_);
lean_dec(v___x_3314_);
v___x_3316_ = lean_string_dec_eq(v___x_3312_, v___x_3315_);
lean_dec(v___x_3315_);
lean_dec(v___x_3312_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_dec(v_i_3290_);
lean_inc_ref(v_left_3288_);
v___x_3317_ = l_Subarray_take___redArg(v_left_3288_, v___x_3309_);
v___x_3318_ = l_Subarray_take___redArg(v_right_3289_, v___x_3313_);
lean_dec(v___x_3313_);
v___x_3319_ = l_Subarray_drop___redArg(v_left_3288_, v___x_3309_);
lean_dec(v___x_3309_);
v___x_3320_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3321_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3319_, v___x_3320_);
v___x_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3318_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3317_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
return v___x_3323_;
}
else
{
lean_object* v___x_3324_; 
lean_dec(v___x_3313_);
lean_dec(v___x_3309_);
v___x_3324_ = lean_nat_add(v_i_3290_, v___x_3310_);
lean_dec(v_i_3290_);
v_i_3290_ = v___x_3324_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(lean_object* v_left_3327_, lean_object* v_right_3328_){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = lean_unsigned_to_nat(0u);
v___x_3330_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(v_left_3327_, v_right_3328_, v___x_3329_);
return v___x_3330_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3331_ = lean_box(0);
v___x_3332_ = lean_unsigned_to_nat(16u);
v___x_3333_ = lean_mk_array(v___x_3332_, v___x_3331_);
return v___x_3333_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v_hist_3336_; 
v___x_3334_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0);
v___x_3335_ = lean_unsigned_to_nat(0u);
v_hist_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3336_, 0, v___x_3335_);
lean_ctor_set(v_hist_3336_, 1, v___x_3334_);
return v_hist_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_left_3337_, lean_object* v_right_3338_){
_start:
{
lean_object* v___x_3339_; lean_object* v_snd_3340_; lean_object* v_fst_3341_; lean_object* v_fst_3342_; lean_object* v_snd_3343_; lean_object* v___x_3344_; lean_object* v_snd_3345_; lean_object* v_fst_3346_; lean_object* v_fst_3347_; lean_object* v_snd_3348_; lean_object* v_start_3349_; lean_object* v_stop_3350_; lean_object* v___x_3351_; lean_object* v_hist_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v_start_3355_; lean_object* v_stop_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v_buckets_3359_; lean_object* v___x_3360_; lean_object* v___y_3362_; lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3339_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(v_left_3337_, v_right_3338_);
v_snd_3340_ = lean_ctor_get(v___x_3339_, 1);
lean_inc(v_snd_3340_);
v_fst_3341_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_fst_3341_);
lean_dec_ref(v___x_3339_);
v_fst_3342_ = lean_ctor_get(v_snd_3340_, 0);
lean_inc(v_fst_3342_);
v_snd_3343_ = lean_ctor_get(v_snd_3340_, 1);
lean_inc(v_snd_3343_);
lean_dec(v_snd_3340_);
v___x_3344_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(v_fst_3342_, v_snd_3343_);
v_snd_3345_ = lean_ctor_get(v___x_3344_, 1);
lean_inc(v_snd_3345_);
v_fst_3346_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_fst_3346_);
lean_dec_ref(v___x_3344_);
v_fst_3347_ = lean_ctor_get(v_snd_3345_, 0);
lean_inc(v_fst_3347_);
v_snd_3348_ = lean_ctor_get(v_snd_3345_, 1);
lean_inc(v_snd_3348_);
lean_dec(v_snd_3345_);
v_start_3349_ = lean_ctor_get(v_fst_3346_, 1);
v_stop_3350_ = lean_ctor_get(v_fst_3346_, 2);
v___x_3351_ = lean_unsigned_to_nat(0u);
v_hist_3352_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1);
v___x_3353_ = lean_nat_sub(v_stop_3350_, v_start_3349_);
v___x_3354_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v___x_3353_, v_fst_3347_, v___x_3353_, v_fst_3346_, v___x_3351_, v_hist_3352_);
v_start_3355_ = lean_ctor_get(v_fst_3347_, 1);
v_stop_3356_ = lean_ctor_get(v_fst_3347_, 2);
v___x_3357_ = lean_nat_sub(v_stop_3356_, v_start_3355_);
v___x_3358_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v___x_3357_, v___x_3357_, v_fst_3347_, v___x_3353_, v___x_3351_, v___x_3354_);
lean_dec(v___x_3353_);
lean_dec(v___x_3357_);
v_buckets_3359_ = lean_ctor_get(v___x_3358_, 1);
lean_inc_ref(v_buckets_3359_);
lean_dec_ref(v___x_3358_);
v___x_3360_ = lean_box(0);
v___x_3388_ = lean_box(0);
v___x_3389_ = lean_array_get_size(v_buckets_3359_);
v___x_3390_ = lean_nat_dec_lt(v___x_3351_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_dec_ref(v_buckets_3359_);
v___y_3362_ = v___x_3388_;
goto v___jp_3361_;
}
else
{
size_t v___x_3391_; size_t v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = lean_usize_of_nat(v___x_3389_);
v___x_3392_ = ((size_t)0ULL);
v___x_3393_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_buckets_3359_, v___x_3391_, v___x_3392_, v___x_3388_);
lean_dec_ref(v_buckets_3359_);
v___y_3362_ = v___x_3393_;
goto v___jp_3361_;
}
v___jp_3361_:
{
lean_object* v___x_3363_; 
v___x_3363_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v___y_3362_, v___x_3360_);
lean_dec(v___y_3362_);
if (lean_obj_tag(v___x_3363_) == 1)
{
lean_object* v_val_3364_; lean_object* v_snd_3365_; lean_object* v_snd_3366_; lean_object* v_fst_3367_; lean_object* v_fst_3368_; lean_object* v_snd_3369_; lean_object* v___x_3370_; lean_object* v_fst_3371_; lean_object* v_snd_3372_; lean_object* v___x_3373_; lean_object* v_fst_3374_; lean_object* v_snd_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v_val_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_val_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v_snd_3365_ = lean_ctor_get(v_val_3364_, 1);
lean_inc(v_snd_3365_);
lean_dec(v_val_3364_);
v_snd_3366_ = lean_ctor_get(v_snd_3365_, 1);
lean_inc(v_snd_3366_);
v_fst_3367_ = lean_ctor_get(v_snd_3365_, 0);
lean_inc(v_fst_3367_);
lean_dec(v_snd_3365_);
v_fst_3368_ = lean_ctor_get(v_snd_3366_, 0);
lean_inc(v_fst_3368_);
v_snd_3369_ = lean_ctor_get(v_snd_3366_, 1);
lean_inc(v_snd_3369_);
lean_dec(v_snd_3366_);
v___x_3370_ = l_Subarray_split___redArg(v_fst_3346_, v_fst_3368_);
lean_dec(v_fst_3368_);
v_fst_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_fst_3371_);
v_snd_3372_ = lean_ctor_get(v___x_3370_, 1);
lean_inc(v_snd_3372_);
lean_dec_ref(v___x_3370_);
v___x_3373_ = l_Subarray_split___redArg(v_fst_3347_, v_snd_3369_);
lean_dec(v_snd_3369_);
v_fst_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_fst_3374_);
v_snd_3375_ = lean_ctor_get(v___x_3373_, 1);
lean_inc(v_snd_3375_);
lean_dec_ref(v___x_3373_);
v___x_3376_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_fst_3371_, v_fst_3374_);
v___x_3377_ = l_Array_append___redArg(v_fst_3341_, v___x_3376_);
lean_dec_ref(v___x_3376_);
v___x_3378_ = lean_unsigned_to_nat(1u);
v___x_3379_ = lean_mk_empty_array_with_capacity(v___x_3378_);
v___x_3380_ = lean_array_push(v___x_3379_, v_fst_3367_);
v___x_3381_ = l_Array_append___redArg(v___x_3377_, v___x_3380_);
lean_dec_ref(v___x_3380_);
v___x_3382_ = l_Subarray_drop___redArg(v_snd_3372_, v___x_3378_);
v___x_3383_ = l_Subarray_drop___redArg(v_snd_3375_, v___x_3378_);
v___x_3384_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3382_, v___x_3383_);
v___x_3385_ = l_Array_append___redArg(v___x_3381_, v___x_3384_);
lean_dec_ref(v___x_3384_);
v___x_3386_ = l_Array_append___redArg(v___x_3385_, v_snd_3348_);
lean_dec(v_snd_3348_);
return v___x_3386_;
}
else
{
lean_object* v___x_3387_; 
lean_dec(v___x_3363_);
lean_dec(v_fst_3347_);
lean_dec(v_fst_3346_);
v___x_3387_ = l_Array_append___redArg(v_fst_3341_, v_snd_3348_);
lean_dec(v_snd_3348_);
return v___x_3387_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3394_, size_t v_i_3395_, lean_object* v_bs_3396_){
_start:
{
uint8_t v___x_3397_; 
v___x_3397_ = lean_usize_dec_lt(v_i_3395_, v_sz_3394_);
if (v___x_3397_ == 0)
{
return v_bs_3396_;
}
else
{
lean_object* v_v_3398_; lean_object* v___x_3399_; lean_object* v_bs_x27_3400_; uint8_t v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; size_t v___x_3404_; size_t v___x_3405_; lean_object* v___x_3406_; 
v_v_3398_ = lean_array_uget(v_bs_3396_, v_i_3395_);
v___x_3399_ = lean_unsigned_to_nat(0u);
v_bs_x27_3400_ = lean_array_uset(v_bs_3396_, v_i_3395_, v___x_3399_);
v___x_3401_ = 1;
v___x_3402_ = lean_box(v___x_3401_);
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
lean_ctor_set(v___x_3403_, 1, v_v_3398_);
v___x_3404_ = ((size_t)1ULL);
v___x_3405_ = lean_usize_add(v_i_3395_, v___x_3404_);
v___x_3406_ = lean_array_uset(v_bs_x27_3400_, v_i_3395_, v___x_3403_);
v_i_3395_ = v___x_3405_;
v_bs_3396_ = v___x_3406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3408_, lean_object* v_i_3409_, lean_object* v_bs_3410_){
_start:
{
size_t v_sz_boxed_3411_; size_t v_i_boxed_3412_; lean_object* v_res_3413_; 
v_sz_boxed_3411_ = lean_unbox_usize(v_sz_3408_);
lean_dec(v_sz_3408_);
v_i_boxed_3412_ = lean_unbox_usize(v_i_3409_);
lean_dec(v_i_3409_);
v_res_3413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3411_, v_i_boxed_3412_, v_bs_3410_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3421_, lean_object* v_edited_3422_){
_start:
{
lean_object* v_i_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v_i_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_array_get_size(v_original_3421_);
v___x_3425_ = lean_nat_dec_lt(v_i_3423_, v___x_3424_);
if (v___x_3425_ == 0)
{
size_t v_sz_3426_; size_t v___x_3427_; lean_object* v___x_3428_; 
lean_dec_ref(v_original_3421_);
v_sz_3426_ = lean_array_size(v_edited_3422_);
v___x_3427_ = ((size_t)0ULL);
v___x_3428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3426_, v___x_3427_, v_edited_3422_);
return v___x_3428_;
}
else
{
lean_object* v___x_3429_; uint8_t v___x_3430_; 
v___x_3429_ = lean_array_get_size(v_edited_3422_);
v___x_3430_ = lean_nat_dec_lt(v_i_3423_, v___x_3429_);
if (v___x_3430_ == 0)
{
size_t v_sz_3431_; size_t v___x_3432_; lean_object* v___x_3433_; 
lean_dec_ref(v_edited_3422_);
v_sz_3431_ = lean_array_size(v_original_3421_);
v___x_3432_ = ((size_t)0ULL);
v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3431_, v___x_3432_, v_original_3421_);
return v___x_3433_;
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v_ds_3436_; lean_object* v___x_3437_; size_t v_sz_3438_; size_t v___x_3439_; lean_object* v___x_3440_; lean_object* v_snd_3441_; lean_object* v_fst_3442_; lean_object* v_fst_3443_; lean_object* v_snd_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3463_; 
lean_inc_ref(v_original_3421_);
v___x_3434_ = l_Array_toSubarray___redArg(v_original_3421_, v_i_3423_, v___x_3424_);
lean_inc_ref(v_edited_3422_);
v___x_3435_ = l_Array_toSubarray___redArg(v_edited_3422_, v_i_3423_, v___x_3429_);
v_ds_3436_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3434_, v___x_3435_);
v___x_3437_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3438_ = lean_array_size(v_ds_3436_);
v___x_3439_ = ((size_t)0ULL);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_3429_, v_edited_3422_, v___x_3424_, v_original_3421_, v_ds_3436_, v_sz_3438_, v___x_3439_, v___x_3437_);
lean_dec_ref(v_ds_3436_);
v_snd_3441_ = lean_ctor_get(v___x_3440_, 1);
lean_inc(v_snd_3441_);
v_fst_3442_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_fst_3442_);
lean_dec_ref(v___x_3440_);
v_fst_3443_ = lean_ctor_get(v_snd_3441_, 0);
v_snd_3444_ = lean_ctor_get(v_snd_3441_, 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_snd_3441_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3446_ = v_snd_3441_;
v_isShared_3447_ = v_isSharedCheck_3463_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_snd_3444_);
lean_inc(v_fst_3443_);
lean_dec(v_snd_3441_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3463_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v_fst_3443_);
lean_ctor_set(v___x_3446_, 0, v_fst_3442_);
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_fst_3442_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_fst_3443_);
v___x_3449_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3450_; lean_object* v_fst_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3460_; 
v___x_3450_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3424_, v_original_3421_, v___x_3449_);
lean_dec_ref(v_original_3421_);
v_fst_3451_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v___x_3450_, 1);
lean_dec(v_unused_3461_);
v___x_3453_ = v___x_3450_;
v_isShared_3454_ = v_isSharedCheck_3460_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_fst_3451_);
lean_dec(v___x_3450_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3460_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v_snd_3444_);
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_fst_3451_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_snd_3444_);
v___x_3456_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3457_; lean_object* v_fst_3458_; 
v___x_3457_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3429_, v_edited_3422_, v___x_3456_);
lean_dec_ref(v_edited_3422_);
v_fst_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_fst_3458_);
lean_dec_ref(v___x_3457_);
return v_fst_3458_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3464_, lean_object* v_x_3465_, lean_object* v_x_3466_){
_start:
{
if (lean_obj_tag(v_x_3465_) == 0)
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = l_List_reverse___redArg(v_x_3466_);
v___x_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
return v___x_3469_;
}
else
{
lean_object* v_head_3470_; lean_object* v_tail_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3480_; 
v_head_3470_ = lean_ctor_get(v_x_3465_, 0);
v_tail_3471_ = lean_ctor_get(v_x_3465_, 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_x_3465_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3473_ = v_x_3465_;
v_isShared_3474_ = v_isSharedCheck_3480_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_tail_3471_);
lean_inc(v_head_3470_);
lean_dec(v_x_3465_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3480_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3475_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3470_, v___y_3464_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 1, v_x_3466_);
lean_ctor_set(v___x_3473_, 0, v___x_3475_);
v___x_3477_ = v___x_3473_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_x_3466_);
v___x_3477_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
v_x_3465_ = v_tail_3471_;
v_x_3466_ = v___x_3477_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3481_, lean_object* v_x_3482_, lean_object* v_x_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3481_, v_x_3482_, v_x_3483_);
lean_dec(v___y_3481_);
return v_res_3485_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3492_ = l_Lean_stringToMessageData(v___x_3491_);
return v___x_3492_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = l_Lean_MessageLog_empty;
v___x_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v___x_3506_; uint8_t v___x_3507_; 
v___x_3506_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
lean_inc(v_x_3502_);
v___x_3507_ = l_Lean_Syntax_isOfKind(v_x_3502_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
lean_dec(v_x_3502_);
v___x_3508_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3508_;
}
else
{
lean_object* v___x_3509_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; uint8_t v___y_3550_; lean_object* v___y_3615_; uint8_t v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; uint8_t v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; uint8_t v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v_dc_x3f_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___x_3758_; lean_object* v___x_3759_; uint8_t v___x_3760_; 
v___x_3509_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3758_ = lean_unsigned_to_nat(0u);
v___x_3759_ = l_Lean_Syntax_getArg(v_x_3502_, v___x_3758_);
v___x_3760_ = l_Lean_Syntax_isNone(v___x_3759_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3761_; uint8_t v___x_3762_; 
v___x_3761_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3759_);
v___x_3762_ = l_Lean_Syntax_matchesNull(v___x_3759_, v___x_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
lean_dec(v___x_3759_);
lean_dec(v_x_3502_);
v___x_3763_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3763_;
}
else
{
lean_object* v_dc_x3f_3764_; 
v_dc_x3f_3764_ = l_Lean_Syntax_getArg(v___x_3759_, v___x_3758_);
lean_dec(v___x_3759_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3767_; uint8_t v___x_3768_; 
v___x_3767_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3764_);
v___x_3768_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3764_, v___x_3767_);
if (v___x_3768_ == 0)
{
lean_object* v___x_3769_; 
lean_dec(v_dc_x3f_3764_);
lean_dec(v_x_3502_);
v___x_3769_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3769_;
}
else
{
goto v___jp_3765_;
}
}
else
{
goto v___jp_3765_;
}
v___jp_3765_:
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3766_, 0, v_dc_x3f_3764_);
v_dc_x3f_3739_ = v___x_3766_;
v___y_3740_ = v_a_3503_;
v___y_3741_ = v_a_3504_;
goto v___jp_3738_;
}
}
}
else
{
lean_object* v___x_3770_; 
lean_dec(v___x_3759_);
v___x_3770_ = lean_box(0);
v_dc_x3f_3739_ = v___x_3770_;
v___y_3740_ = v_a_3503_;
v___y_3741_ = v_a_3504_;
goto v___jp_3738_;
}
v___jp_3510_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3516_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3517_ = l_Lean_stringToMessageData(v___y_3515_);
v___x_3518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3516_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
v___x_3519_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3511_, v___x_3518_, v___y_3512_, v___y_3514_);
lean_dec(v___y_3511_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3539_; 
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; 
v_unused_3540_ = lean_ctor_get(v___x_3519_, 0);
lean_dec(v_unused_3540_);
v___x_3521_ = v___x_3519_;
v_isShared_3522_ = v_isSharedCheck_3539_;
goto v_resetjp_3520_;
}
else
{
lean_dec(v___x_3519_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3539_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_Elab_Command_getRef___redArg(v___y_3512_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3509_);
lean_ctor_set(v___x_3525_, 1, v___y_3513_);
v___x_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3526_, 0, v_a_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set_tag(v___x_3521_, 10);
lean_ctor_set(v___x_3521_, 0, v___x_3526_);
v___x_3528_ = v___x_3521_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3528_, v___y_3512_, v___y_3514_);
return v___x_3529_;
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_del_object(v___x_3521_);
lean_dec_ref(v___y_3513_);
v_a_3531_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3523_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3523_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3513_);
return v___x_3519_;
}
}
v___jp_3541_:
{
if (v___y_3550_ == 0)
{
lean_object* v___x_3551_; lean_object* v_env_3552_; lean_object* v_scopes_3553_; lean_object* v_usedQuotCtxts_3554_; lean_object* v_nextMacroScope_3555_; lean_object* v_maxRecDepth_3556_; lean_object* v_ngen_3557_; lean_object* v_auxDeclNGen_3558_; lean_object* v_infoState_3559_; lean_object* v_traceState_3560_; lean_object* v_snapshotTasks_3561_; lean_object* v_prevLinterStates_3562_; lean_object* v_codeQualityEntryTasks_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v___y_3544_);
v___x_3551_ = lean_st_ref_take(v___y_3548_);
v_env_3552_ = lean_ctor_get(v___x_3551_, 0);
v_scopes_3553_ = lean_ctor_get(v___x_3551_, 2);
v_usedQuotCtxts_3554_ = lean_ctor_get(v___x_3551_, 3);
v_nextMacroScope_3555_ = lean_ctor_get(v___x_3551_, 4);
v_maxRecDepth_3556_ = lean_ctor_get(v___x_3551_, 5);
v_ngen_3557_ = lean_ctor_get(v___x_3551_, 6);
v_auxDeclNGen_3558_ = lean_ctor_get(v___x_3551_, 7);
v_infoState_3559_ = lean_ctor_get(v___x_3551_, 8);
v_traceState_3560_ = lean_ctor_get(v___x_3551_, 9);
v_snapshotTasks_3561_ = lean_ctor_get(v___x_3551_, 10);
v_prevLinterStates_3562_ = lean_ctor_get(v___x_3551_, 11);
v_codeQualityEntryTasks_3563_ = lean_ctor_get(v___x_3551_, 12);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3588_ == 0)
{
lean_object* v_unused_3589_; 
v_unused_3589_ = lean_ctor_get(v___x_3551_, 1);
lean_dec(v_unused_3589_);
v___x_3565_ = v___x_3551_;
v_isShared_3566_ = v_isSharedCheck_3588_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3563_);
lean_inc(v_prevLinterStates_3562_);
lean_inc(v_snapshotTasks_3561_);
lean_inc(v_traceState_3560_);
lean_inc(v_infoState_3559_);
lean_inc(v_auxDeclNGen_3558_);
lean_inc(v_ngen_3557_);
lean_inc(v_maxRecDepth_3556_);
lean_inc(v_nextMacroScope_3555_);
lean_inc(v_usedQuotCtxts_3554_);
lean_inc(v_scopes_3553_);
lean_inc(v_env_3552_);
lean_dec(v___x_3551_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3588_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 1, v___y_3549_);
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_env_3552_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v___y_3549_);
lean_ctor_set(v_reuseFailAlloc_3587_, 2, v_scopes_3553_);
lean_ctor_set(v_reuseFailAlloc_3587_, 3, v_usedQuotCtxts_3554_);
lean_ctor_set(v_reuseFailAlloc_3587_, 4, v_nextMacroScope_3555_);
lean_ctor_set(v_reuseFailAlloc_3587_, 5, v_maxRecDepth_3556_);
lean_ctor_set(v_reuseFailAlloc_3587_, 6, v_ngen_3557_);
lean_ctor_set(v_reuseFailAlloc_3587_, 7, v_auxDeclNGen_3558_);
lean_ctor_set(v_reuseFailAlloc_3587_, 8, v_infoState_3559_);
lean_ctor_set(v_reuseFailAlloc_3587_, 9, v_traceState_3560_);
lean_ctor_set(v_reuseFailAlloc_3587_, 10, v_snapshotTasks_3561_);
lean_ctor_set(v_reuseFailAlloc_3587_, 11, v_prevLinterStates_3562_);
lean_ctor_set(v_reuseFailAlloc_3587_, 12, v_codeQualityEntryTasks_3563_);
v___x_3568_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v_scopes_3572_; lean_object* v___x_3573_; lean_object* v_opts_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3569_ = lean_st_ref_put(v___y_3548_, v___x_3568_);
v___x_3570_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3571_ = lean_st_ref_get(v___y_3548_);
v_scopes_3572_ = lean_ctor_get(v___x_3571_, 2);
lean_inc(v_scopes_3572_);
lean_dec(v___x_3571_);
v___x_3573_ = l_List_head_x21___redArg(v___x_3570_, v_scopes_3572_);
lean_dec(v_scopes_3572_);
v_opts_3574_ = lean_ctor_get(v___x_3573_, 1);
lean_inc_ref(v_opts_3574_);
lean_dec(v___x_3573_);
v___x_3575_ = l_Lean_guard__msgs_diff;
v___x_3576_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3574_, v___x_3575_);
lean_dec_ref(v_opts_3574_);
if (v___x_3576_ == 0)
{
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3545_);
lean_inc_ref(v___y_3546_);
v___y_3511_ = v___y_3542_;
v___y_3512_ = v___y_3543_;
v___y_3513_ = v___y_3546_;
v___y_3514_ = v___y_3548_;
v___y_3515_ = v___y_3546_;
goto v___jp_3510_;
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3577_ = lean_string_utf8_byte_size(v___y_3545_);
lean_inc(v___y_3547_);
lean_inc_ref(v___y_3545_);
v___x_3578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3578_, 0, v___y_3545_);
lean_ctor_set(v___x_3578_, 1, v___y_3547_);
lean_ctor_set(v___x_3578_, 2, v___x_3577_);
v___x_3579_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
v___x_3580_ = lean_mk_empty_array_with_capacity(v___y_3547_);
lean_inc_ref(v___x_3580_);
v___x_3581_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3545_, v___x_3578_, v___x_3577_, v___x_3579_, v___x_3580_);
lean_dec_ref_known(v___x_3578_, 3);
v___x_3582_ = lean_string_utf8_byte_size(v___y_3546_);
lean_inc_ref_n(v___y_3546_, 2);
v___x_3583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3583_, 0, v___y_3546_);
lean_ctor_set(v___x_3583_, 1, v___y_3547_);
lean_ctor_set(v___x_3583_, 2, v___x_3582_);
v___x_3584_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3546_, v___x_3583_, v___x_3582_, v___x_3579_, v___x_3580_);
lean_dec_ref_known(v___x_3583_, 3);
v___x_3585_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3581_, v___x_3584_);
v___x_3586_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3585_);
lean_dec_ref(v___x_3585_);
v___y_3511_ = v___y_3542_;
v___y_3512_ = v___y_3543_;
v___y_3513_ = v___y_3546_;
v___y_3514_ = v___y_3548_;
v___y_3515_ = v___x_3586_;
goto v___jp_3510_;
}
}
}
}
else
{
lean_object* v___x_3590_; lean_object* v_env_3591_; lean_object* v_scopes_3592_; lean_object* v_usedQuotCtxts_3593_; lean_object* v_nextMacroScope_3594_; lean_object* v_maxRecDepth_3595_; lean_object* v_ngen_3596_; lean_object* v_auxDeclNGen_3597_; lean_object* v_infoState_3598_; lean_object* v_traceState_3599_; lean_object* v_snapshotTasks_3600_; lean_object* v_prevLinterStates_3601_; lean_object* v_codeQualityEntryTasks_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3612_; 
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3542_);
v___x_3590_ = lean_st_ref_take(v___y_3548_);
v_env_3591_ = lean_ctor_get(v___x_3590_, 0);
v_scopes_3592_ = lean_ctor_get(v___x_3590_, 2);
v_usedQuotCtxts_3593_ = lean_ctor_get(v___x_3590_, 3);
v_nextMacroScope_3594_ = lean_ctor_get(v___x_3590_, 4);
v_maxRecDepth_3595_ = lean_ctor_get(v___x_3590_, 5);
v_ngen_3596_ = lean_ctor_get(v___x_3590_, 6);
v_auxDeclNGen_3597_ = lean_ctor_get(v___x_3590_, 7);
v_infoState_3598_ = lean_ctor_get(v___x_3590_, 8);
v_traceState_3599_ = lean_ctor_get(v___x_3590_, 9);
v_snapshotTasks_3600_ = lean_ctor_get(v___x_3590_, 10);
v_prevLinterStates_3601_ = lean_ctor_get(v___x_3590_, 11);
v_codeQualityEntryTasks_3602_ = lean_ctor_get(v___x_3590_, 12);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; 
v_unused_3613_ = lean_ctor_get(v___x_3590_, 1);
lean_dec(v_unused_3613_);
v___x_3604_ = v___x_3590_;
v_isShared_3605_ = v_isSharedCheck_3612_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3602_);
lean_inc(v_prevLinterStates_3601_);
lean_inc(v_snapshotTasks_3600_);
lean_inc(v_traceState_3599_);
lean_inc(v_infoState_3598_);
lean_inc(v_auxDeclNGen_3597_);
lean_inc(v_ngen_3596_);
lean_inc(v_maxRecDepth_3595_);
lean_inc(v_nextMacroScope_3594_);
lean_inc(v_usedQuotCtxts_3593_);
lean_inc(v_scopes_3592_);
lean_inc(v_env_3591_);
lean_dec(v___x_3590_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3612_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3606_ = lean_box(0);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 1, v___y_3544_);
v___x_3608_ = v___x_3604_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_env_3591_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v___y_3544_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_scopes_3592_);
lean_ctor_set(v_reuseFailAlloc_3611_, 3, v_usedQuotCtxts_3593_);
lean_ctor_set(v_reuseFailAlloc_3611_, 4, v_nextMacroScope_3594_);
lean_ctor_set(v_reuseFailAlloc_3611_, 5, v_maxRecDepth_3595_);
lean_ctor_set(v_reuseFailAlloc_3611_, 6, v_ngen_3596_);
lean_ctor_set(v_reuseFailAlloc_3611_, 7, v_auxDeclNGen_3597_);
lean_ctor_set(v_reuseFailAlloc_3611_, 8, v_infoState_3598_);
lean_ctor_set(v_reuseFailAlloc_3611_, 9, v_traceState_3599_);
lean_ctor_set(v_reuseFailAlloc_3611_, 10, v_snapshotTasks_3600_);
lean_ctor_set(v_reuseFailAlloc_3611_, 11, v_prevLinterStates_3601_);
lean_ctor_set(v_reuseFailAlloc_3611_, 12, v_codeQualityEntryTasks_3602_);
v___x_3608_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = lean_st_ref_put(v___y_3548_, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3606_);
return v___x_3610_;
}
}
}
}
v___jp_3614_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v_a_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v_str_3637_; lean_object* v_startInclusive_3638_; lean_object* v_endExclusive_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3654_; 
v___x_3627_ = l_Lean_MessageLog_toList(v___y_3618_);
lean_dec(v___y_3618_);
v___x_3628_ = lean_box(0);
v___x_3629_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3626_, v___x_3627_, v___x_3628_);
lean_dec(v___y_3626_);
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref(v___x_3629_);
v___x_3631_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3616_, v_a_3630_);
v___x_3632_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4));
v___x_3633_ = l_String_intercalate(v___x_3632_, v___x_3631_);
v___x_3634_ = lean_string_utf8_byte_size(v___x_3633_);
lean_inc(v___y_3622_);
v___x_3635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3633_);
lean_ctor_set(v___x_3635_, 1, v___y_3622_);
lean_ctor_set(v___x_3635_, 2, v___x_3634_);
v___x_3636_ = l_String_Slice_trimAscii(v___x_3635_);
v_str_3637_ = lean_ctor_get(v___x_3636_, 0);
v_startInclusive_3638_ = lean_ctor_get(v___x_3636_, 1);
v_endExclusive_3639_ = lean_ctor_get(v___x_3636_, 2);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3641_ = v___x_3636_;
v_isShared_3642_ = v_isSharedCheck_3654_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_endExclusive_3639_);
lean_inc(v_startInclusive_3638_);
lean_inc(v_str_3637_);
lean_dec(v___x_3636_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3654_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; 
v___x_3643_ = lean_string_utf8_extract_fast(v_str_3637_, v_startInclusive_3638_, v_endExclusive_3639_);
lean_dec(v_endExclusive_3639_);
lean_dec(v_startInclusive_3638_);
lean_dec_ref(v_str_3637_);
if (v___y_3624_ == 0)
{
lean_object* v___x_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
lean_del_object(v___x_3641_);
lean_inc_ref(v___y_3621_);
v___x_3644_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3620_, v___y_3621_);
lean_inc_ref(v___x_3643_);
v___x_3645_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3620_, v___x_3643_);
v___x_3646_ = lean_string_dec_eq(v___x_3644_, v___x_3645_);
lean_dec_ref(v___x_3645_);
lean_dec_ref(v___x_3644_);
v___y_3542_ = v___y_3615_;
v___y_3543_ = v___y_3617_;
v___y_3544_ = v___y_3619_;
v___y_3545_ = v___y_3621_;
v___y_3546_ = v___x_3643_;
v___y_3547_ = v___y_3622_;
v___y_3548_ = v___y_3623_;
v___y_3549_ = v___y_3625_;
v___y_3550_ = v___x_3646_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3651_; 
lean_inc_ref(v___x_3643_);
v___x_3647_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3620_, v___x_3643_);
lean_inc_ref(v___y_3621_);
v___x_3648_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3620_, v___y_3621_);
v___x_3649_ = lean_string_utf8_byte_size(v___x_3647_);
lean_inc(v___y_3622_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 2, v___x_3649_);
lean_ctor_set(v___x_3641_, 1, v___y_3622_);
lean_ctor_set(v___x_3641_, 0, v___x_3647_);
v___x_3651_ = v___x_3641_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___y_3622_);
lean_ctor_set(v_reuseFailAlloc_3653_, 2, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
uint8_t v___x_3652_; 
v___x_3652_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3648_, v___x_3651_);
lean_dec_ref(v___x_3651_);
v___y_3542_ = v___y_3615_;
v___y_3543_ = v___y_3617_;
v___y_3544_ = v___y_3619_;
v___y_3545_ = v___y_3621_;
v___y_3546_ = v___x_3643_;
v___y_3547_ = v___y_3622_;
v___y_3548_ = v___y_3623_;
v___y_3549_ = v___y_3625_;
v___y_3550_ = v___x_3652_;
goto v___jp_3541_;
}
}
}
}
v___jp_3655_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v_str_3666_; lean_object* v_startInclusive_3667_; lean_object* v_endExclusive_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3662_ = lean_unsigned_to_nat(0u);
v___x_3663_ = lean_string_utf8_byte_size(v___y_3661_);
v___x_3664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3664_, 0, v___y_3661_);
lean_ctor_set(v___x_3664_, 1, v___x_3662_);
lean_ctor_set(v___x_3664_, 2, v___x_3663_);
v___x_3665_ = l_String_Slice_trimAscii(v___x_3664_);
v_str_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc_ref(v_str_3666_);
v_startInclusive_3667_ = lean_ctor_get(v___x_3665_, 1);
lean_inc(v_startInclusive_3667_);
v_endExclusive_3668_ = lean_ctor_get(v___x_3665_, 2);
lean_inc(v_endExclusive_3668_);
lean_dec_ref(v___x_3665_);
v___x_3669_ = lean_string_utf8_extract_fast(v_str_3666_, v_startInclusive_3667_, v_endExclusive_3668_);
lean_dec(v_endExclusive_3668_);
lean_dec(v_startInclusive_3667_);
lean_dec_ref(v_str_3666_);
v___x_3670_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3669_);
v___x_3671_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3659_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v_filterFn_3673_; uint8_t v_whitespace_3674_; uint8_t v_ordering_3675_; uint8_t v_reportPositions_3676_; uint8_t v_substring_3677_; lean_object* v___x_3678_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___x_3671_, 1);
v_filterFn_3673_ = lean_ctor_get(v_a_3672_, 0);
lean_inc_ref(v_filterFn_3673_);
v_whitespace_3674_ = lean_ctor_get_uint8(v_a_3672_, sizeof(void*)*1);
v_ordering_3675_ = lean_ctor_get_uint8(v_a_3672_, sizeof(void*)*1 + 1);
v_reportPositions_3676_ = lean_ctor_get_uint8(v_a_3672_, sizeof(void*)*1 + 2);
v_substring_3677_ = lean_ctor_get_uint8(v_a_3672_, sizeof(void*)*1 + 3);
lean_dec(v_a_3672_);
v___x_3678_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3660_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v_a_3683_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3678_, 1);
v___x_3680_ = l_Lean_MessageLog_toList(v_a_3679_);
v___x_3681_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5);
v___x_3682_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3673_, v___x_3680_, v___x_3681_);
lean_dec(v___x_3680_);
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
lean_dec_ref(v___x_3682_);
if (v_reportPositions_3676_ == 0)
{
lean_object* v_fst_3684_; lean_object* v_snd_3685_; lean_object* v___x_3686_; 
v_fst_3684_ = lean_ctor_get(v_a_3683_, 0);
lean_inc(v_fst_3684_);
v_snd_3685_ = lean_ctor_get(v_a_3683_, 1);
lean_inc(v_snd_3685_);
lean_dec(v_a_3683_);
v___x_3686_ = lean_box(0);
v___y_3615_ = v___y_3656_;
v___y_3616_ = v_ordering_3675_;
v___y_3617_ = v___y_3657_;
v___y_3618_ = v_fst_3684_;
v___y_3619_ = v_snd_3685_;
v___y_3620_ = v_whitespace_3674_;
v___y_3621_ = v___x_3670_;
v___y_3622_ = v___x_3662_;
v___y_3623_ = v___y_3658_;
v___y_3624_ = v_substring_3677_;
v___y_3625_ = v_a_3679_;
v___y_3626_ = v___x_3686_;
goto v___jp_3614_;
}
else
{
lean_object* v_fst_3687_; lean_object* v_snd_3688_; uint8_t v___x_3689_; lean_object* v___x_3690_; 
v_fst_3687_ = lean_ctor_get(v_a_3683_, 0);
lean_inc(v_fst_3687_);
v_snd_3688_ = lean_ctor_get(v_a_3683_, 1);
lean_inc(v_snd_3688_);
lean_dec(v_a_3683_);
v___x_3689_ = 0;
v___x_3690_ = l_Lean_Syntax_getPos_x3f(v___y_3656_, v___x_3689_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v___x_3691_; 
v___x_3691_ = lean_box(0);
v___y_3615_ = v___y_3656_;
v___y_3616_ = v_ordering_3675_;
v___y_3617_ = v___y_3657_;
v___y_3618_ = v_fst_3687_;
v___y_3619_ = v_snd_3688_;
v___y_3620_ = v_whitespace_3674_;
v___y_3621_ = v___x_3670_;
v___y_3622_ = v___x_3662_;
v___y_3623_ = v___y_3658_;
v___y_3624_ = v_substring_3677_;
v___y_3625_ = v_a_3679_;
v___y_3626_ = v___x_3691_;
goto v___jp_3614_;
}
else
{
lean_object* v_val_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3702_; 
v_val_3692_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3694_ = v___x_3690_;
v_isShared_3695_ = v_isSharedCheck_3702_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_val_3692_);
lean_dec(v___x_3690_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3702_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v_fileMap_3696_; lean_object* v___x_3697_; lean_object* v_line_3698_; lean_object* v___x_3700_; 
v_fileMap_3696_ = lean_ctor_get(v___y_3657_, 1);
lean_inc_ref(v_fileMap_3696_);
v___x_3697_ = l_Lean_FileMap_toPosition(v_fileMap_3696_, v_val_3692_);
lean_dec(v_val_3692_);
v_line_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_line_3698_);
lean_dec_ref(v___x_3697_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v_line_3698_);
v___x_3700_ = v___x_3694_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_line_3698_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
v___y_3615_ = v___y_3656_;
v___y_3616_ = v_ordering_3675_;
v___y_3617_ = v___y_3657_;
v___y_3618_ = v_fst_3687_;
v___y_3619_ = v_snd_3688_;
v___y_3620_ = v_whitespace_3674_;
v___y_3621_ = v___x_3670_;
v___y_3622_ = v___x_3662_;
v___y_3623_ = v___y_3658_;
v___y_3624_ = v_substring_3677_;
v___y_3625_ = v_a_3679_;
v___y_3626_ = v___x_3700_;
goto v___jp_3614_;
}
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec_ref(v_filterFn_3673_);
lean_dec_ref(v___x_3670_);
lean_dec(v___y_3656_);
v_a_3703_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3678_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3678_);
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
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec_ref(v___x_3670_);
lean_dec(v___y_3660_);
lean_dec(v___y_3656_);
v_a_3711_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3671_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3671_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
v___jp_3719_:
{
if (lean_obj_tag(v___y_3722_) == 0)
{
lean_object* v___x_3726_; 
v___x_3726_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_3656_ = v___y_3720_;
v___y_3657_ = v___y_3721_;
v___y_3658_ = v___y_3723_;
v___y_3659_ = v___y_3725_;
v___y_3660_ = v___y_3724_;
v___y_3661_ = v___x_3726_;
goto v___jp_3655_;
}
else
{
lean_object* v_val_3727_; lean_object* v___x_3728_; 
v_val_3727_ = lean_ctor_get(v___y_3722_, 0);
lean_inc(v_val_3727_);
lean_dec_ref_known(v___y_3722_, 1);
v___x_3728_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3727_, v___y_3721_, v___y_3723_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_a_3729_; 
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_a_3729_);
lean_dec_ref_known(v___x_3728_, 1);
v___y_3656_ = v___y_3720_;
v___y_3657_ = v___y_3721_;
v___y_3658_ = v___y_3723_;
v___y_3659_ = v___y_3725_;
v___y_3660_ = v___y_3724_;
v___y_3661_ = v_a_3729_;
goto v___jp_3655_;
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec(v___y_3720_);
v_a_3730_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3728_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
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
}
v___jp_3738_:
{
lean_object* v___x_3742_; lean_object* v_tk_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3742_ = lean_unsigned_to_nat(1u);
v_tk_3743_ = l_Lean_Syntax_getArg(v_x_3502_, v___x_3742_);
v___x_3744_ = lean_unsigned_to_nat(2u);
v___x_3745_ = l_Lean_Syntax_getArg(v_x_3502_, v___x_3744_);
v___x_3746_ = lean_unsigned_to_nat(4u);
v___x_3747_ = l_Lean_Syntax_getArg(v_x_3502_, v___x_3746_);
lean_dec(v_x_3502_);
v___x_3748_ = l_Lean_Syntax_getOptional_x3f(v___x_3745_);
lean_dec(v___x_3745_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v___x_3749_; 
v___x_3749_ = lean_box(0);
v___y_3720_ = v_tk_3743_;
v___y_3721_ = v___y_3740_;
v___y_3722_ = v_dc_x3f_3739_;
v___y_3723_ = v___y_3741_;
v___y_3724_ = v___x_3747_;
v___y_3725_ = v___x_3749_;
goto v___jp_3719_;
}
else
{
lean_object* v_val_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
v_val_3750_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3748_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_val_3750_);
lean_dec(v___x_3748_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_val_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
v___y_3720_ = v_tk_3743_;
v___y_3721_ = v___y_3740_;
v___y_3722_ = v_dc_x3f_3739_;
v___y_3723_ = v___y_3741_;
v___y_3724_ = v___x_3747_;
v___y_3725_ = v___x_3755_;
goto v___jp_3719_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3771_, v_a_3772_, v_a_3773_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3776_, lean_object* v_as_3777_, lean_object* v_as_x27_3778_, lean_object* v_b_3779_, lean_object* v_a_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3776_, v_as_x27_3778_, v_b_3779_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3785_, lean_object* v_as_3786_, lean_object* v_as_x27_3787_, lean_object* v_b_3788_, lean_object* v_a_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3785_, v_as_3786_, v_as_x27_3787_, v_b_3788_, v_a_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v_as_x27_3787_);
lean_dec(v_as_3786_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3794_, lean_object* v_x_3795_, lean_object* v_x_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3794_, v_x_3795_, v_x_3796_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3801_, lean_object* v_x_3802_, lean_object* v_x_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3801_, v_x_3802_, v_x_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3801_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3808_, v___y_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3818_, lean_object* v___x_3819_, lean_object* v___x_3820_, lean_object* v_inst_3821_, lean_object* v_R_3822_, lean_object* v_a_3823_, lean_object* v_b_3824_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3818_, v___x_3819_, v___x_3820_, v_a_3823_, v_b_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3826_, lean_object* v___x_3827_, lean_object* v___x_3828_, lean_object* v_inst_3829_, lean_object* v_R_3830_, lean_object* v_a_3831_, lean_object* v_b_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3826_, v___x_3827_, v___x_3828_, v_inst_3829_, v_R_3830_, v_a_3831_, v_b_3832_);
lean_dec_ref(v___x_3827_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3834_, v___y_3836_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3844_, lean_object* v___x_3845_, lean_object* v___x_3846_, lean_object* v_inst_3847_, lean_object* v_R_3848_, lean_object* v_a_3849_, lean_object* v_b_3850_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3844_, v___x_3845_, v___x_3846_, v_a_3849_, v_b_3850_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3852_, lean_object* v___x_3853_, lean_object* v___x_3854_, lean_object* v_inst_3855_, lean_object* v_R_3856_, lean_object* v_a_3857_, lean_object* v_b_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3852_, v___x_3853_, v___x_3854_, v_inst_3855_, v_R_3856_, v_a_3857_, v_b_3858_);
lean_dec_ref(v___x_3853_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v___x_3860_, lean_object* v_original_3861_, lean_object* v_a_3862_, lean_object* v_inst_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v___x_3865_; 
v___x_3865_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_3860_, v_original_3861_, v_a_3862_, v_a_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___boxed(lean_object* v___x_3866_, lean_object* v_original_3867_, lean_object* v_a_3868_, lean_object* v_inst_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3866_, v_original_3867_, v_a_3868_, v_inst_3869_, v_a_3870_);
lean_dec_ref(v_a_3868_);
lean_dec_ref(v_original_3867_);
lean_dec(v___x_3866_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v___x_3872_, lean_object* v_edited_3873_, lean_object* v_a_3874_, lean_object* v_inst_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_3872_, v_edited_3873_, v_a_3874_, v_a_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v___x_3878_, lean_object* v_edited_3879_, lean_object* v_a_3880_, lean_object* v_inst_3881_, lean_object* v_a_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v___x_3878_, v_edited_3879_, v_a_3880_, v_inst_3881_, v_a_3882_);
lean_dec_ref(v_a_3880_);
lean_dec_ref(v_edited_3879_);
lean_dec(v___x_3878_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3884_, lean_object* v_original_3885_, lean_object* v_inst_3886_, lean_object* v_a_3887_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3884_, v_original_3885_, v_a_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3889_, lean_object* v_original_3890_, lean_object* v_inst_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3889_, v_original_3890_, v_inst_3891_, v_a_3892_);
lean_dec_ref(v_original_3890_);
lean_dec(v___x_3889_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3894_, lean_object* v_edited_3895_, lean_object* v_inst_3896_, lean_object* v_a_3897_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3894_, v_edited_3895_, v_a_3897_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3899_, lean_object* v_edited_3900_, lean_object* v_inst_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3899_, v_edited_3900_, v_inst_3901_, v_a_3902_);
lean_dec_ref(v_edited_3900_);
lean_dec(v___x_3899_);
return v_res_3903_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3904_, lean_object* v_inst_3905_, lean_object* v_R_3906_, lean_object* v_a_3907_, uint8_t v_b_3908_, lean_object* v_c_3909_){
_start:
{
uint8_t v___x_3910_; 
v___x_3910_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3904_, v_a_3907_, v_b_3908_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3911_, lean_object* v_inst_3912_, lean_object* v_R_3913_, lean_object* v_a_3914_, lean_object* v_b_3915_, lean_object* v_c_3916_){
_start:
{
uint8_t v_b_boxed_3917_; uint8_t v_res_3918_; lean_object* v_r_3919_; 
v_b_boxed_3917_ = lean_unbox(v_b_3915_);
v_res_3918_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3911_, v_inst_3912_, v_R_3913_, v_a_3914_, v_b_boxed_3917_, v_c_3916_);
lean_dec_ref(v_s_3911_);
v_r_3919_ = lean_box(v_res_3918_);
return v_r_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3920_, lean_object* v_ref_3921_, lean_object* v_msg_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3921_, v_msg_3922_, v___y_3923_, v___y_3924_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3927_, lean_object* v_ref_3928_, lean_object* v_msg_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3927_, v_ref_3928_, v_msg_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v_ref_3928_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(lean_object* v_as_3934_, lean_object* v_as_x27_3935_, lean_object* v_b_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3935_, v_b_3936_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___boxed(lean_object* v_as_3939_, lean_object* v_as_x27_3940_, lean_object* v_b_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(v_as_3939_, v_as_x27_3940_, v_b_3941_, v_a_3942_);
lean_dec(v_as_x27_3940_);
lean_dec(v_as_3939_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(lean_object* v_lsize_3944_, lean_object* v_rsize_3945_, lean_object* v_histogram_3946_, lean_object* v_index_3947_, lean_object* v_val_3948_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_histogram_3946_, v_index_3947_, v_val_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___boxed(lean_object* v_lsize_3950_, lean_object* v_rsize_3951_, lean_object* v_histogram_3952_, lean_object* v_index_3953_, lean_object* v_val_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(v_lsize_3950_, v_rsize_3951_, v_histogram_3952_, v_index_3953_, v_val_3954_);
lean_dec(v_rsize_3951_);
lean_dec(v_lsize_3950_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(lean_object* v_upperBound_3956_, lean_object* v___x_3957_, lean_object* v_fst_3958_, lean_object* v___x_3959_, lean_object* v_inst_3960_, lean_object* v_R_3961_, lean_object* v_a_3962_, lean_object* v_b_3963_, lean_object* v_c_3964_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3956_, v___x_3957_, v_fst_3958_, v___x_3959_, v_a_3962_, v_b_3963_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___boxed(lean_object* v_upperBound_3966_, lean_object* v___x_3967_, lean_object* v_fst_3968_, lean_object* v___x_3969_, lean_object* v_inst_3970_, lean_object* v_R_3971_, lean_object* v_a_3972_, lean_object* v_b_3973_, lean_object* v_c_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(v_upperBound_3966_, v___x_3967_, v_fst_3968_, v___x_3969_, v_inst_3970_, v_R_3971_, v_a_3972_, v_b_3973_, v_c_3974_);
lean_dec(v___x_3969_);
lean_dec_ref(v_fst_3968_);
lean_dec(v___x_3967_);
lean_dec(v_upperBound_3966_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(lean_object* v_lsize_3976_, lean_object* v_rsize_3977_, lean_object* v_histogram_3978_, lean_object* v_index_3979_, lean_object* v_val_3980_){
_start:
{
lean_object* v___x_3981_; 
v___x_3981_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_histogram_3978_, v_index_3979_, v_val_3980_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___boxed(lean_object* v_lsize_3982_, lean_object* v_rsize_3983_, lean_object* v_histogram_3984_, lean_object* v_index_3985_, lean_object* v_val_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(v_lsize_3982_, v_rsize_3983_, v_histogram_3984_, v_index_3985_, v_val_3986_);
lean_dec(v_rsize_3983_);
lean_dec(v_lsize_3982_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(lean_object* v_upperBound_3988_, lean_object* v_fst_3989_, lean_object* v___x_3990_, lean_object* v_fst_3991_, lean_object* v_inst_3992_, lean_object* v_R_3993_, lean_object* v_a_3994_, lean_object* v_b_3995_, lean_object* v_c_3996_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3988_, v_fst_3989_, v___x_3990_, v_fst_3991_, v_a_3994_, v_b_3995_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___boxed(lean_object* v_upperBound_3998_, lean_object* v_fst_3999_, lean_object* v___x_4000_, lean_object* v_fst_4001_, lean_object* v_inst_4002_, lean_object* v_R_4003_, lean_object* v_a_4004_, lean_object* v_b_4005_, lean_object* v_c_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(v_upperBound_3998_, v_fst_3999_, v___x_4000_, v_fst_4001_, v_inst_4002_, v_R_4003_, v_a_4004_, v_b_4005_, v_c_4006_);
lean_dec_ref(v_fst_4001_);
lean_dec(v___x_4000_);
lean_dec_ref(v_fst_3999_);
lean_dec(v_upperBound_3998_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_4008_, lean_object* v_msg_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_4009_, v___y_4010_, v___y_4011_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_4014_, lean_object* v_msg_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_4014_, v_msg_4015_, v___y_4016_, v___y_4017_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(lean_object* v_00_u03b2_4020_, lean_object* v_m_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_4021_, v_a_4022_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___boxed(lean_object* v_00_u03b2_4024_, lean_object* v_m_4025_, lean_object* v_a_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(v_00_u03b2_4024_, v_m_4025_, v_a_4026_);
lean_dec_ref(v_a_4026_);
lean_dec_ref(v_m_4025_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26(lean_object* v_00_u03b2_4028_, lean_object* v_m_4029_, lean_object* v_a_4030_, lean_object* v_b_4031_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_m_4029_, v_a_4030_, v_b_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_4033_, lean_object* v_macroStack_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_4033_, v_macroStack_4034_, v___y_4036_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4039_, lean_object* v_macroStack_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4039_, v_macroStack_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29(lean_object* v_inst_4045_, lean_object* v_R_4046_, lean_object* v_a_4047_, lean_object* v_b_4048_){
_start:
{
lean_object* v___x_4049_; 
v___x_4049_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v_a_4047_, v_b_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(lean_object* v_00_u03b2_4050_, lean_object* v_a_4051_, lean_object* v_x_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_4051_, v_x_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___boxed(lean_object* v_00_u03b2_4054_, lean_object* v_a_4055_, lean_object* v_x_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(v_00_u03b2_4054_, v_a_4055_, v_x_4056_);
lean_dec(v_x_4056_);
lean_dec_ref(v_a_4055_);
return v_res_4057_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(lean_object* v_00_u03b2_4058_, lean_object* v_a_4059_, lean_object* v_x_4060_){
_start:
{
uint8_t v___x_4061_; 
v___x_4061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_4059_, v_x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___boxed(lean_object* v_00_u03b2_4062_, lean_object* v_a_4063_, lean_object* v_x_4064_){
_start:
{
uint8_t v_res_4065_; lean_object* v_r_4066_; 
v_res_4065_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(v_00_u03b2_4062_, v_a_4063_, v_x_4064_);
lean_dec(v_x_4064_);
lean_dec_ref(v_a_4063_);
v_r_4066_ = lean_box(v_res_4065_);
return v_r_4066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38(lean_object* v_00_u03b2_4067_, lean_object* v_data_4068_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_data_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39(lean_object* v_00_u03b2_4070_, lean_object* v_a_4071_, lean_object* v_b_4072_, lean_object* v_x_4073_){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_4071_, v_b_4072_, v_x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44(lean_object* v_00_u03b2_4075_, lean_object* v_i_4076_, lean_object* v_source_4077_, lean_object* v_target_4078_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v_i_4076_, v_source_4077_, v_target_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4080_, lean_object* v_x_4081_, lean_object* v_x_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_x_4081_, v_x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4092_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4093_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
v___x_4094_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4095_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4096_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4092_, v___x_4093_, v___x_4094_, v___x_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4097_){
_start:
{
lean_object* v_res_4098_; 
v_res_4098_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4125_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4126_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4127_ = l_Lean_addBuiltinDeclarationRanges(v___x_4125_, v___x_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4130_){
_start:
{
lean_object* v_doc_4132_; lean_object* v___x_4133_; 
v_doc_4132_ = lean_ctor_get(v___y_4130_, 1);
lean_inc_ref(v_doc_4132_);
v___x_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4133_, 0, v_doc_4132_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4134_);
lean_dec_ref(v___y_4134_);
return v_res_4136_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4137_, lean_object* v_a_4138_, uint8_t v_b_4139_){
_start:
{
lean_object* v_str_4140_; lean_object* v_startInclusive_4141_; lean_object* v_endExclusive_4142_; lean_object* v___x_4143_; uint8_t v_decide_4144_; 
v_str_4140_ = lean_ctor_get(v_s_4137_, 0);
v_startInclusive_4141_ = lean_ctor_get(v_s_4137_, 1);
v_endExclusive_4142_ = lean_ctor_get(v_s_4137_, 2);
v___x_4143_ = lean_nat_sub(v_endExclusive_4142_, v_startInclusive_4141_);
v_decide_4144_ = lean_nat_dec_eq(v_a_4138_, v___x_4143_);
lean_dec(v___x_4143_);
if (v_decide_4144_ == 0)
{
lean_object* v___x_4145_; uint32_t v___x_4146_; uint32_t v___x_4147_; uint8_t v___x_4148_; 
v___x_4145_ = lean_nat_add(v_startInclusive_4141_, v_a_4138_);
lean_dec(v_a_4138_);
v___x_4146_ = lean_string_utf8_get_fast(v_str_4140_, v___x_4145_);
v___x_4147_ = 10;
v___x_4148_ = lean_uint32_dec_eq(v___x_4146_, v___x_4147_);
if (v___x_4148_ == 0)
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = lean_string_utf8_next_fast(v_str_4140_, v___x_4145_);
lean_dec(v___x_4145_);
v___x_4150_ = lean_nat_sub(v___x_4149_, v_startInclusive_4141_);
v_a_4138_ = v___x_4150_;
v_b_4139_ = v___x_4148_;
goto _start;
}
else
{
lean_dec(v___x_4145_);
return v___x_4148_;
}
}
else
{
lean_dec(v_a_4138_);
return v_b_4139_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4152_, lean_object* v_a_4153_, lean_object* v_b_4154_){
_start:
{
uint8_t v_b_boxed_4155_; uint8_t v_res_4156_; lean_object* v_r_4157_; 
v_b_boxed_4155_ = lean_unbox(v_b_4154_);
v_res_4156_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4152_, v_a_4153_, v_b_boxed_4155_);
lean_dec_ref(v_s_4152_);
v_r_4157_ = lean_box(v_res_4156_);
return v_r_4157_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4158_){
_start:
{
lean_object* v_searcher_4159_; uint8_t v___x_4160_; uint8_t v___x_4161_; 
v_searcher_4159_ = lean_unsigned_to_nat(0u);
v___x_4160_ = 0;
v___x_4161_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4158_, v_searcher_4159_, v___x_4160_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4162_){
_start:
{
uint8_t v_res_4163_; lean_object* v_r_4164_; 
v_res_4163_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4162_);
lean_dec_ref(v_s_4162_);
v_r_4164_ = lean_box(v_res_4163_);
return v_r_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4176_, lean_object* v_fst_4177_, uint8_t v___x_4178_, lean_object* v_a_4179_, lean_object* v___x_4180_, lean_object* v___x_4181_, lean_object* v___x_4182_, lean_object* v___x_4183_, lean_object* v___x_4184_, lean_object* v___x_4185_, lean_object* v___x_4186_, lean_object* v___x_4187_, lean_object* v_snd_4188_, lean_object* v___x_4189_){
_start:
{
if (lean_obj_tag(v___x_4176_) == 1)
{
lean_object* v_val_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4252_; 
v_val_4191_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4193_ = v___x_4176_;
v_isShared_4194_ = v_isSharedCheck_4252_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_val_4191_);
lean_dec(v___x_4176_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4252_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4195_ = lean_unsigned_to_nat(0u);
v___x_4196_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4197_ = l_Lean_Syntax_setArg(v_fst_4177_, v___x_4195_, v___x_4196_);
v___x_4198_ = l_Lean_Syntax_getPos_x3f(v___x_4197_, v___x_4178_);
lean_dec(v___x_4197_);
if (lean_obj_tag(v___x_4198_) == 1)
{
lean_object* v_val_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v___x_4189_);
v_val_4199_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4201_ = v___x_4198_;
v_isShared_4202_ = v_isSharedCheck_4248_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_val_4199_);
lean_dec(v___x_4198_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4248_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___y_4204_; lean_object* v___x_4230_; lean_object* v___x_4236_; uint8_t v___x_4237_; 
v___x_4230_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4188_);
v___x_4236_ = lean_string_utf8_byte_size(v___x_4230_);
v___x_4237_ = lean_nat_dec_eq(v___x_4236_, v___x_4195_);
if (v___x_4237_ == 0)
{
lean_object* v___x_4238_; lean_object* v___x_4239_; uint8_t v___x_4240_; 
v___x_4238_ = lean_string_length(v___x_4230_);
v___x_4239_ = lean_unsigned_to_nat(93u);
v___x_4240_ = lean_nat_dec_le(v___x_4238_, v___x_4239_);
if (v___x_4240_ == 0)
{
goto v___jp_4231_;
}
else
{
lean_object* v___x_4241_; uint8_t v___x_4242_; 
lean_inc_ref(v___x_4230_);
v___x_4241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4230_);
lean_ctor_set(v___x_4241_, 1, v___x_4195_);
lean_ctor_set(v___x_4241_, 2, v___x_4236_);
v___x_4242_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4241_);
lean_dec_ref_known(v___x_4241_, 3);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4243_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4244_ = lean_string_append(v___x_4243_, v___x_4230_);
lean_dec_ref(v___x_4230_);
v___x_4245_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4246_ = lean_string_append(v___x_4244_, v___x_4245_);
v___y_4204_ = v___x_4246_;
goto v___jp_4203_;
}
else
{
goto v___jp_4231_;
}
}
}
else
{
lean_object* v___x_4247_; 
lean_dec_ref(v___x_4230_);
v___x_4247_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_4204_ = v___x_4247_;
goto v___jp_4203_;
}
v___jp_4203_:
{
lean_object* v_toEditableDocumentCore_4205_; lean_object* v_meta_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4226_; 
v_toEditableDocumentCore_4205_ = lean_ctor_get(v_a_4179_, 0);
lean_inc_ref(v_toEditableDocumentCore_4205_);
v_meta_4206_ = lean_ctor_get(v_toEditableDocumentCore_4205_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v_toEditableDocumentCore_4205_);
if (v_isSharedCheck_4226_ == 0)
{
lean_object* v_unused_4227_; lean_object* v_unused_4228_; lean_object* v_unused_4229_; 
v_unused_4227_ = lean_ctor_get(v_toEditableDocumentCore_4205_, 3);
lean_dec(v_unused_4227_);
v_unused_4228_ = lean_ctor_get(v_toEditableDocumentCore_4205_, 2);
lean_dec(v_unused_4228_);
v_unused_4229_ = lean_ctor_get(v_toEditableDocumentCore_4205_, 1);
lean_dec(v_unused_4229_);
v___x_4208_ = v_toEditableDocumentCore_4205_;
v_isShared_4209_ = v_isSharedCheck_4226_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_meta_4206_);
lean_dec(v_toEditableDocumentCore_4205_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4226_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v_text_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4216_; 
v_text_4210_ = lean_ctor_get(v_meta_4206_, 3);
lean_inc_ref(v_text_4210_);
lean_dec_ref(v_meta_4206_);
v___x_4211_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4179_);
v___x_4212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4212_, 0, v_val_4191_);
lean_ctor_set(v___x_4212_, 1, v_val_4199_);
v___x_4213_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4210_, v___x_4212_);
v___x_4214_ = lean_box(0);
lean_inc(v___x_4180_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 3, v___x_4180_);
lean_ctor_set(v___x_4208_, 2, v___x_4214_);
lean_ctor_set(v___x_4208_, 1, v___y_4204_);
lean_ctor_set(v___x_4208_, 0, v___x_4213_);
v___x_4216_ = v___x_4208_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4213_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v___y_4204_);
lean_ctor_set(v_reuseFailAlloc_4225_, 2, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4225_, 3, v___x_4180_);
v___x_4216_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
lean_object* v___x_4217_; lean_object* v___x_4219_; 
v___x_4217_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4211_, v___x_4216_);
if (v_isShared_4202_ == 0)
{
lean_ctor_set(v___x_4201_, 0, v___x_4217_);
v___x_4219_ = v___x_4201_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
lean_object* v___x_4220_; lean_object* v___x_4222_; 
lean_inc(v___x_4180_);
v___x_4220_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4180_);
lean_ctor_set(v___x_4220_, 1, v___x_4180_);
lean_ctor_set(v___x_4220_, 2, v___x_4181_);
lean_ctor_set(v___x_4220_, 3, v___x_4182_);
lean_ctor_set(v___x_4220_, 4, v___x_4183_);
lean_ctor_set(v___x_4220_, 5, v___x_4184_);
lean_ctor_set(v___x_4220_, 6, v___x_4185_);
lean_ctor_set(v___x_4220_, 7, v___x_4219_);
lean_ctor_set(v___x_4220_, 8, v___x_4186_);
lean_ctor_set(v___x_4220_, 9, v___x_4187_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set_tag(v___x_4193_, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4220_);
v___x_4222_ = v___x_4193_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4220_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
}
v___jp_4231_:
{
lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4232_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4233_ = lean_string_append(v___x_4232_, v___x_4230_);
lean_dec_ref(v___x_4230_);
v___x_4234_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4235_ = lean_string_append(v___x_4233_, v___x_4234_);
v___y_4204_ = v___x_4235_;
goto v___jp_4203_;
}
}
}
else
{
lean_object* v___x_4250_; 
lean_dec(v___x_4198_);
lean_dec(v_val_4191_);
lean_dec_ref(v_snd_4188_);
lean_dec(v___x_4187_);
lean_dec(v___x_4186_);
lean_dec(v___x_4185_);
lean_dec(v___x_4184_);
lean_dec(v___x_4183_);
lean_dec(v___x_4182_);
lean_dec_ref(v___x_4181_);
lean_dec(v___x_4180_);
lean_dec_ref(v_a_4179_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set_tag(v___x_4193_, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4189_);
v___x_4250_ = v___x_4193_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4189_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
else
{
lean_object* v___x_4253_; 
lean_dec_ref(v_snd_4188_);
lean_dec(v___x_4187_);
lean_dec(v___x_4186_);
lean_dec(v___x_4185_);
lean_dec(v___x_4184_);
lean_dec(v___x_4183_);
lean_dec(v___x_4182_);
lean_dec_ref(v___x_4181_);
lean_dec(v___x_4180_);
lean_dec_ref(v_a_4179_);
lean_dec(v_fst_4177_);
lean_dec(v___x_4176_);
v___x_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4189_);
return v___x_4253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4254_, lean_object* v_fst_4255_, lean_object* v___x_4256_, lean_object* v_a_4257_, lean_object* v___x_4258_, lean_object* v___x_4259_, lean_object* v___x_4260_, lean_object* v___x_4261_, lean_object* v___x_4262_, lean_object* v___x_4263_, lean_object* v___x_4264_, lean_object* v___x_4265_, lean_object* v_snd_4266_, lean_object* v___x_4267_, lean_object* v___y_4268_){
_start:
{
uint8_t v___x_4527__boxed_4269_; lean_object* v_res_4270_; 
v___x_4527__boxed_4269_ = lean_unbox(v___x_4256_);
v_res_4270_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4254_, v_fst_4255_, v___x_4527__boxed_4269_, v_a_4257_, v___x_4258_, v___x_4259_, v___x_4260_, v___x_4261_, v___x_4262_, v___x_4263_, v___x_4264_, v___x_4265_, v_snd_4266_, v___x_4267_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4274_, size_t v_sz_4275_, size_t v_i_4276_, lean_object* v_b_4277_){
_start:
{
lean_object* v_a_4279_; uint8_t v___x_4283_; 
v___x_4283_ = lean_usize_dec_lt(v_i_4276_, v_sz_4275_);
if (v___x_4283_ == 0)
{
lean_inc_ref(v_b_4277_);
return v_b_4277_;
}
else
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v_a_4286_; 
v___x_4284_ = lean_box(0);
v___x_4285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4286_ = lean_array_uget(v_as_4274_, v_i_4276_);
if (lean_obj_tag(v_a_4286_) == 1)
{
lean_object* v_i_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4321_; 
v_i_4287_ = lean_ctor_get(v_a_4286_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v_a_4286_);
if (v_isSharedCheck_4321_ == 0)
{
lean_object* v_unused_4322_; 
v_unused_4322_ = lean_ctor_get(v_a_4286_, 1);
lean_dec(v_unused_4322_);
v___x_4289_ = v_a_4286_;
v_isShared_4290_ = v_isSharedCheck_4321_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_i_4287_);
lean_dec(v_a_4286_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4321_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
if (lean_obj_tag(v_i_4287_) == 10)
{
lean_object* v_i_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4320_; 
v_i_4291_ = lean_ctor_get(v_i_4287_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v_i_4287_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4293_ = v_i_4287_;
v_isShared_4294_ = v_isSharedCheck_4320_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_i_4291_);
lean_dec(v_i_4287_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4320_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v_stx_4295_; lean_object* v_value_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4319_; 
v_stx_4295_ = lean_ctor_get(v_i_4291_, 0);
v_value_4296_ = lean_ctor_get(v_i_4291_, 1);
v_isSharedCheck_4319_ = !lean_is_exclusive(v_i_4291_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4298_ = v_i_4291_;
v_isShared_4299_ = v_isSharedCheck_4319_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_value_4296_);
lean_inc(v_stx_4295_);
lean_dec(v_i_4291_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4319_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4300_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4301_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4296_, v___x_4300_);
lean_dec(v_value_4296_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_del_object(v___x_4298_);
lean_dec(v_stx_4295_);
lean_del_object(v___x_4293_);
lean_del_object(v___x_4289_);
v_a_4279_ = v___x_4285_;
goto v___jp_4278_;
}
else
{
lean_object* v_val_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4318_; 
v_val_4302_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4304_ = v___x_4301_;
v_isShared_4305_ = v_isSharedCheck_4318_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_val_4302_);
lean_dec(v___x_4301_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4318_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 1, v_val_4302_);
v___x_4307_ = v___x_4298_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_stx_4295_);
lean_ctor_set(v_reuseFailAlloc_4317_, 1, v_val_4302_);
v___x_4307_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
lean_object* v___x_4309_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v___x_4307_);
v___x_4309_ = v___x_4304_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4307_);
v___x_4309_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
lean_object* v___x_4311_; 
if (v_isShared_4294_ == 0)
{
lean_ctor_set_tag(v___x_4293_, 1);
lean_ctor_set(v___x_4293_, 0, v___x_4309_);
v___x_4311_ = v___x_4293_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4309_);
v___x_4311_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
lean_object* v___x_4313_; 
if (v_isShared_4290_ == 0)
{
lean_ctor_set_tag(v___x_4289_, 0);
lean_ctor_set(v___x_4289_, 1, v___x_4284_);
lean_ctor_set(v___x_4289_, 0, v___x_4311_);
v___x_4313_ = v___x_4289_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v___x_4311_);
lean_ctor_set(v_reuseFailAlloc_4314_, 1, v___x_4284_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
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
lean_del_object(v___x_4289_);
lean_dec_ref(v_i_4287_);
v_a_4279_ = v___x_4285_;
goto v___jp_4278_;
}
}
}
else
{
lean_dec(v_a_4286_);
v_a_4279_ = v___x_4285_;
goto v___jp_4278_;
}
}
v___jp_4278_:
{
size_t v___x_4280_; size_t v___x_4281_; 
v___x_4280_ = ((size_t)1ULL);
v___x_4281_ = lean_usize_add(v_i_4276_, v___x_4280_);
v_i_4276_ = v___x_4281_;
v_b_4277_ = v_a_4279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4323_, lean_object* v_sz_4324_, lean_object* v_i_4325_, lean_object* v_b_4326_){
_start:
{
size_t v_sz_boxed_4327_; size_t v_i_boxed_4328_; lean_object* v_res_4329_; 
v_sz_boxed_4327_ = lean_unbox_usize(v_sz_4324_);
lean_dec(v_sz_4324_);
v_i_boxed_4328_ = lean_unbox_usize(v_i_4325_);
lean_dec(v_i_4325_);
v_res_4329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4323_, v_sz_boxed_4327_, v_i_boxed_4328_, v_b_4326_);
lean_dec_ref(v_b_4326_);
lean_dec_ref(v_as_4323_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4330_, size_t v_sz_4331_, size_t v_i_4332_, lean_object* v_b_4333_){
_start:
{
lean_object* v_a_4335_; uint8_t v___x_4339_; 
v___x_4339_ = lean_usize_dec_lt(v_i_4332_, v_sz_4331_);
if (v___x_4339_ == 0)
{
lean_inc_ref(v_b_4333_);
return v_b_4333_;
}
else
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v_a_4342_; 
v___x_4340_ = lean_box(0);
v___x_4341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4342_ = lean_array_uget(v_as_4330_, v_i_4332_);
if (lean_obj_tag(v_a_4342_) == 1)
{
lean_object* v_i_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4377_; 
v_i_4343_ = lean_ctor_get(v_a_4342_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v_a_4342_);
if (v_isSharedCheck_4377_ == 0)
{
lean_object* v_unused_4378_; 
v_unused_4378_ = lean_ctor_get(v_a_4342_, 1);
lean_dec(v_unused_4378_);
v___x_4345_ = v_a_4342_;
v_isShared_4346_ = v_isSharedCheck_4377_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_i_4343_);
lean_dec(v_a_4342_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4377_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
if (lean_obj_tag(v_i_4343_) == 10)
{
lean_object* v_i_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4376_; 
v_i_4347_ = lean_ctor_get(v_i_4343_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v_i_4343_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4349_ = v_i_4343_;
v_isShared_4350_ = v_isSharedCheck_4376_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_i_4347_);
lean_dec(v_i_4343_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4376_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v_stx_4351_; lean_object* v_value_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4375_; 
v_stx_4351_ = lean_ctor_get(v_i_4347_, 0);
v_value_4352_ = lean_ctor_get(v_i_4347_, 1);
v_isSharedCheck_4375_ = !lean_is_exclusive(v_i_4347_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4354_ = v_i_4347_;
v_isShared_4355_ = v_isSharedCheck_4375_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_value_4352_);
lean_inc(v_stx_4351_);
lean_dec(v_i_4347_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4375_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4356_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4357_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4352_, v___x_4356_);
lean_dec(v_value_4352_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_del_object(v___x_4354_);
lean_dec(v_stx_4351_);
lean_del_object(v___x_4349_);
lean_del_object(v___x_4345_);
v_a_4335_ = v___x_4341_;
goto v___jp_4334_;
}
else
{
lean_object* v_val_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4374_; 
v_val_4358_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4360_ = v___x_4357_;
v_isShared_4361_ = v_isSharedCheck_4374_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_val_4358_);
lean_dec(v___x_4357_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4374_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 1, v_val_4358_);
v___x_4363_ = v___x_4354_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_stx_4351_);
lean_ctor_set(v_reuseFailAlloc_4373_, 1, v_val_4358_);
v___x_4363_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4365_; 
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 0, v___x_4363_);
v___x_4365_ = v___x_4360_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4363_);
v___x_4365_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
lean_object* v___x_4367_; 
if (v_isShared_4350_ == 0)
{
lean_ctor_set_tag(v___x_4349_, 1);
lean_ctor_set(v___x_4349_, 0, v___x_4365_);
v___x_4367_ = v___x_4349_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4365_);
v___x_4367_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
lean_object* v___x_4369_; 
if (v_isShared_4346_ == 0)
{
lean_ctor_set_tag(v___x_4345_, 0);
lean_ctor_set(v___x_4345_, 1, v___x_4340_);
lean_ctor_set(v___x_4345_, 0, v___x_4367_);
v___x_4369_ = v___x_4345_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v___x_4340_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
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
lean_del_object(v___x_4345_);
lean_dec_ref(v_i_4343_);
v_a_4335_ = v___x_4341_;
goto v___jp_4334_;
}
}
}
else
{
lean_dec(v_a_4342_);
v_a_4335_ = v___x_4341_;
goto v___jp_4334_;
}
}
v___jp_4334_:
{
size_t v___x_4336_; size_t v___x_4337_; lean_object* v___x_4338_; 
v___x_4336_ = ((size_t)1ULL);
v___x_4337_ = lean_usize_add(v_i_4332_, v___x_4336_);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4330_, v_sz_4331_, v___x_4337_, v_a_4335_);
return v___x_4338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4379_, lean_object* v_sz_4380_, lean_object* v_i_4381_, lean_object* v_b_4382_){
_start:
{
size_t v_sz_boxed_4383_; size_t v_i_boxed_4384_; lean_object* v_res_4385_; 
v_sz_boxed_4383_ = lean_unbox_usize(v_sz_4380_);
lean_dec(v_sz_4380_);
v_i_boxed_4384_ = lean_unbox_usize(v_i_4381_);
lean_dec(v_i_4381_);
v_res_4385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4379_, v_sz_boxed_4383_, v_i_boxed_4384_, v_b_4382_);
lean_dec_ref(v_b_4382_);
lean_dec_ref(v_as_4379_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4386_){
_start:
{
if (lean_obj_tag(v_x_4386_) == 0)
{
lean_object* v_cs_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; size_t v_sz_4390_; size_t v___x_4391_; lean_object* v___x_4392_; lean_object* v_fst_4393_; 
v_cs_4387_ = lean_ctor_get(v_x_4386_, 0);
v___x_4388_ = lean_box(0);
v___x_4389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4390_ = lean_array_size(v_cs_4387_);
v___x_4391_ = ((size_t)0ULL);
v___x_4392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4387_, v_sz_4390_, v___x_4391_, v___x_4389_);
v_fst_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_fst_4393_);
lean_dec_ref(v___x_4392_);
if (lean_obj_tag(v_fst_4393_) == 0)
{
return v___x_4388_;
}
else
{
lean_object* v_val_4394_; 
v_val_4394_ = lean_ctor_get(v_fst_4393_, 0);
lean_inc(v_val_4394_);
lean_dec_ref_known(v_fst_4393_, 1);
return v_val_4394_;
}
}
else
{
lean_object* v_vs_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; size_t v_sz_4398_; size_t v___x_4399_; lean_object* v___x_4400_; lean_object* v_fst_4401_; 
v_vs_4395_ = lean_ctor_get(v_x_4386_, 0);
v___x_4396_ = lean_box(0);
v___x_4397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4398_ = lean_array_size(v_vs_4395_);
v___x_4399_ = ((size_t)0ULL);
v___x_4400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4395_, v_sz_4398_, v___x_4399_, v___x_4397_);
v_fst_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc(v_fst_4401_);
lean_dec_ref(v___x_4400_);
if (lean_obj_tag(v_fst_4401_) == 0)
{
return v___x_4396_;
}
else
{
lean_object* v_val_4402_; 
v_val_4402_ = lean_ctor_get(v_fst_4401_, 0);
lean_inc(v_val_4402_);
lean_dec_ref_known(v_fst_4401_, 1);
return v_val_4402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4403_, size_t v_sz_4404_, size_t v_i_4405_, lean_object* v_b_4406_){
_start:
{
uint8_t v___x_4407_; 
v___x_4407_ = lean_usize_dec_lt(v_i_4405_, v_sz_4404_);
if (v___x_4407_ == 0)
{
lean_inc_ref(v_b_4406_);
return v_b_4406_;
}
else
{
lean_object* v___x_4408_; lean_object* v_a_4409_; lean_object* v___x_4410_; 
v___x_4408_ = lean_box(0);
v_a_4409_ = lean_array_uget_borrowed(v_as_4403_, v_i_4405_);
v___x_4410_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4409_);
if (lean_obj_tag(v___x_4410_) == 1)
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4410_);
v___x_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
lean_ctor_set(v___x_4412_, 1, v___x_4408_);
return v___x_4412_;
}
else
{
lean_object* v___x_4413_; size_t v___x_4414_; size_t v___x_4415_; 
lean_dec(v___x_4410_);
v___x_4413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4414_ = ((size_t)1ULL);
v___x_4415_ = lean_usize_add(v_i_4405_, v___x_4414_);
v_i_4405_ = v___x_4415_;
v_b_4406_ = v___x_4413_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4417_, lean_object* v_sz_4418_, lean_object* v_i_4419_, lean_object* v_b_4420_){
_start:
{
size_t v_sz_boxed_4421_; size_t v_i_boxed_4422_; lean_object* v_res_4423_; 
v_sz_boxed_4421_ = lean_unbox_usize(v_sz_4418_);
lean_dec(v_sz_4418_);
v_i_boxed_4422_ = lean_unbox_usize(v_i_4419_);
lean_dec(v_i_4419_);
v_res_4423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4417_, v_sz_boxed_4421_, v_i_boxed_4422_, v_b_4420_);
lean_dec_ref(v_b_4420_);
lean_dec_ref(v_as_4417_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4424_);
lean_dec_ref(v_x_4424_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4426_){
_start:
{
lean_object* v_root_4427_; lean_object* v_tail_4428_; lean_object* v___x_4429_; 
v_root_4427_ = lean_ctor_get(v_t_4426_, 0);
v_tail_4428_ = lean_ctor_get(v_t_4426_, 1);
v___x_4429_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4427_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v___x_4430_; size_t v_sz_4431_; size_t v___x_4432_; lean_object* v___x_4433_; lean_object* v_fst_4434_; 
v___x_4430_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4431_ = lean_array_size(v_tail_4428_);
v___x_4432_ = ((size_t)0ULL);
v___x_4433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4428_, v_sz_4431_, v___x_4432_, v___x_4430_);
v_fst_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_fst_4434_);
lean_dec_ref(v___x_4433_);
if (lean_obj_tag(v_fst_4434_) == 0)
{
return v___x_4429_;
}
else
{
lean_object* v_val_4435_; 
v_val_4435_ = lean_ctor_get(v_fst_4434_, 0);
lean_inc(v_val_4435_);
lean_dec_ref_known(v_fst_4434_, 1);
return v_val_4435_;
}
}
else
{
return v___x_4429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4436_);
lean_dec_ref(v_t_4436_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4452_, lean_object* v_a_4453_){
_start:
{
if (lean_obj_tag(v_node_4452_) == 1)
{
lean_object* v_children_4455_; lean_object* v_res_4456_; 
v_children_4455_ = lean_ctor_get(v_node_4452_, 1);
v_res_4456_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4455_);
if (lean_obj_tag(v_res_4456_) == 1)
{
lean_object* v_val_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4494_; 
v_val_4457_ = lean_ctor_get(v_res_4456_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v_res_4456_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4459_ = v_res_4456_;
v_isShared_4460_ = v_isSharedCheck_4494_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_val_4457_);
lean_dec(v_res_4456_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4494_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v_fst_4461_; lean_object* v_snd_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4493_; 
v_fst_4461_ = lean_ctor_get(v_val_4457_, 0);
v_snd_4462_ = lean_ctor_get(v_val_4457_, 1);
v_isSharedCheck_4493_ = !lean_is_exclusive(v_val_4457_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4464_ = v_val_4457_;
v_isShared_4465_ = v_isSharedCheck_4493_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_snd_4462_);
lean_inc(v_fst_4461_);
lean_dec(v_val_4457_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4493_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4466_; lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4492_; 
v___x_4466_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4453_);
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4469_ = v___x_4466_;
v_isShared_4470_ = v_isSharedCheck_4492_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4466_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4492_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; uint8_t v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___y_4479_; lean_object* v___x_4481_; 
v___x_4471_ = lean_box(0);
v___x_4472_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4473_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4474_ = 1;
v___x_4475_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4476_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4477_ = l_Lean_Syntax_getPos_x3f(v_fst_4461_, v___x_4474_);
v___x_4478_ = lean_box(v___x_4474_);
v___y_4479_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4479_, 0, v___x_4477_);
lean_closure_set(v___y_4479_, 1, v_fst_4461_);
lean_closure_set(v___y_4479_, 2, v___x_4478_);
lean_closure_set(v___y_4479_, 3, v_a_4467_);
lean_closure_set(v___y_4479_, 4, v___x_4471_);
lean_closure_set(v___y_4479_, 5, v___x_4472_);
lean_closure_set(v___y_4479_, 6, v___x_4473_);
lean_closure_set(v___y_4479_, 7, v___x_4471_);
lean_closure_set(v___y_4479_, 8, v___x_4475_);
lean_closure_set(v___y_4479_, 9, v___x_4471_);
lean_closure_set(v___y_4479_, 10, v___x_4471_);
lean_closure_set(v___y_4479_, 11, v___x_4471_);
lean_closure_set(v___y_4479_, 12, v_snd_4462_);
lean_closure_set(v___y_4479_, 13, v___x_4476_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___y_4479_);
v___x_4481_ = v___x_4459_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___y_4479_);
v___x_4481_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
lean_object* v___x_4483_; 
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 1, v___x_4481_);
lean_ctor_set(v___x_4464_, 0, v___x_4476_);
v___x_4483_ = v___x_4464_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4476_);
lean_ctor_set(v_reuseFailAlloc_4490_, 1, v___x_4481_);
v___x_4483_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4488_; 
v___x_4484_ = lean_unsigned_to_nat(1u);
v___x_4485_ = lean_mk_empty_array_with_capacity(v___x_4484_);
v___x_4486_ = lean_array_push(v___x_4485_, v___x_4483_);
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 0, v___x_4486_);
v___x_4488_ = v___x_4469_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4486_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
lean_dec(v_res_4456_);
v___x_4495_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
return v___x_4496_;
}
}
else
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4497_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
return v___x_4498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4499_, v_a_4500_);
lean_dec_ref(v_a_4500_);
lean_dec_ref(v_node_4499_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4503_, lean_object* v_x_4504_, lean_object* v_x_4505_, lean_object* v_node_4506_, lean_object* v_a_4507_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4506_, v_a_4507_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4510_, lean_object* v_x_4511_, lean_object* v_x_4512_, lean_object* v_node_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4510_, v_x_4511_, v_x_4512_, v_node_4513_, v_a_4514_);
lean_dec_ref(v_a_4514_);
lean_dec_ref(v_node_4513_);
lean_dec_ref(v_x_4512_);
lean_dec_ref(v_x_4511_);
lean_dec_ref(v_x_4510_);
return v_res_4516_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4517_, lean_object* v_inst_4518_, lean_object* v_R_4519_, lean_object* v_a_4520_, uint8_t v_b_4521_, lean_object* v_c_4522_){
_start:
{
uint8_t v___x_4523_; 
v___x_4523_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4517_, v_a_4520_, v_b_4521_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4524_, lean_object* v_inst_4525_, lean_object* v_R_4526_, lean_object* v_a_4527_, lean_object* v_b_4528_, lean_object* v_c_4529_){
_start:
{
uint8_t v_b_boxed_4530_; uint8_t v_res_4531_; lean_object* v_r_4532_; 
v_b_boxed_4530_ = lean_unbox(v_b_4528_);
v_res_4531_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4524_, v_inst_4525_, v_R_4526_, v_a_4527_, v_b_boxed_4530_, v_c_4529_);
lean_dec_ref(v_s_4524_);
v_r_4532_ = lean_box(v_res_4531_);
return v_r_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_(){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4538_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_));
v___x_4539_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4540_ = l_Lean_CodeAction_insertBuiltin(v___x_4538_, v___x_4539_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354____boxed(lean_object* v_a_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_();
return v_res_4542_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4548_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4549_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4548_);
return v___x_4549_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4550_ = lean_unsigned_to_nat(0u);
v___x_4551_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
v___x_4552_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4553_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
lean_ctor_set(v___x_4553_, 1, v___x_4551_);
lean_ctor_set(v___x_4553_, 2, v___x_4550_);
lean_ctor_set(v___x_4553_, 3, v___x_4550_);
return v___x_4553_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4554_){
_start:
{
lean_object* v___x_4555_; uint8_t v___x_4556_; uint8_t v___x_4557_; 
v___x_4555_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4556_ = 0;
v___x_4557_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4554_, v___x_4555_, v___x_4556_);
return v___x_4557_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4558_){
_start:
{
uint8_t v_res_4559_; lean_object* v_r_4560_; 
v_res_4559_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4558_);
lean_dec_ref(v_s_4558_);
v_r_4560_ = lean_box(v_res_4559_);
return v_r_4560_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4561_, lean_object* v_as_x27_4562_, uint8_t v_b_4563_){
_start:
{
if (lean_obj_tag(v_as_x27_4562_) == 0)
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4565_ = lean_box(v_b_4563_);
v___x_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4565_);
return v___x_4566_;
}
else
{
lean_object* v_head_4567_; uint8_t v_isSilent_4568_; 
v_head_4567_ = lean_ctor_get(v_as_x27_4562_, 0);
v_isSilent_4568_ = lean_ctor_get_uint8(v_head_4567_, sizeof(void*)*5 + 2);
if (v_isSilent_4568_ == 0)
{
lean_object* v_tail_4569_; lean_object* v_data_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; uint8_t v___x_4575_; 
v_tail_4569_ = lean_ctor_get(v_as_x27_4562_, 1);
v_data_4570_ = lean_ctor_get(v_head_4567_, 4);
lean_inc(v_data_4570_);
v___x_4571_ = l_Lean_MessageData_toString(v_data_4570_);
v___x_4572_ = lean_unsigned_to_nat(0u);
v___x_4573_ = lean_string_utf8_byte_size(v___x_4571_);
v___x_4574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4571_);
lean_ctor_set(v___x_4574_, 1, v___x_4572_);
lean_ctor_set(v___x_4574_, 2, v___x_4573_);
v___x_4575_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4574_);
lean_dec_ref_known(v___x_4574_, 3);
if (v___x_4575_ == 0)
{
v_as_x27_4562_ = v_tail_4569_;
goto _start;
}
else
{
lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4577_ = lean_box(v_foundPanic_4561_);
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
return v___x_4578_;
}
}
else
{
lean_object* v_tail_4579_; 
v_tail_4579_ = lean_ctor_get(v_as_x27_4562_, 1);
v_as_x27_4562_ = v_tail_4579_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4581_, lean_object* v_as_x27_4582_, lean_object* v_b_4583_, lean_object* v___y_4584_){
_start:
{
uint8_t v_foundPanic_boxed_4585_; uint8_t v_b_boxed_4586_; lean_object* v_res_4587_; 
v_foundPanic_boxed_4585_ = lean_unbox(v_foundPanic_4581_);
v_b_boxed_4586_ = lean_unbox(v_b_4583_);
v_res_4587_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4585_, v_as_x27_4582_, v_b_boxed_4586_);
lean_dec(v_as_x27_4582_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4588_, uint8_t v_severity_4589_, uint8_t v_isSilent_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_){
_start:
{
lean_object* v___x_4594_; 
v___x_4594_ = l_Lean_Elab_Command_getRef___redArg(v___y_4591_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; lean_object* v___x_4596_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
lean_inc(v_a_4595_);
lean_dec_ref_known(v___x_4594_, 1);
v___x_4596_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4595_, v_msgData_4588_, v_severity_4589_, v_isSilent_4590_, v___y_4591_, v___y_4592_);
lean_dec(v_a_4595_);
return v___x_4596_;
}
else
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
lean_dec_ref(v_msgData_4588_);
v_a_4597_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___x_4594_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4594_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4605_, lean_object* v_severity_4606_, lean_object* v_isSilent_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_){
_start:
{
uint8_t v_severity_boxed_4611_; uint8_t v_isSilent_boxed_4612_; lean_object* v_res_4613_; 
v_severity_boxed_4611_ = lean_unbox(v_severity_4606_);
v_isSilent_boxed_4612_ = lean_unbox(v_isSilent_4607_);
v_res_4613_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4605_, v_severity_boxed_4611_, v_isSilent_boxed_4612_, v___y_4608_, v___y_4609_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_){
_start:
{
uint8_t v___x_4618_; uint8_t v___x_4619_; lean_object* v___x_4620_; 
v___x_4618_ = 2;
v___x_4619_ = 0;
v___x_4620_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4614_, v___x_4618_, v___x_4619_, v___y_4615_, v___y_4616_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4621_, v___y_4622_, v___y_4623_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
return v_res_4625_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4633_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4634_ = l_Lean_MessageData_ofFormat(v___x_4633_);
return v___x_4634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_){
_start:
{
lean_object* v___x_4639_; uint8_t v_foundPanic_4640_; 
v___x_4639_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4635_);
v_foundPanic_4640_ = l_Lean_Syntax_isOfKind(v_x_4635_, v___x_4639_);
if (v_foundPanic_4640_ == 0)
{
lean_object* v___x_4641_; 
lean_dec(v_x_4635_);
v___x_4641_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4641_;
}
else
{
lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4642_ = lean_unsigned_to_nat(2u);
v___x_4643_ = l_Lean_Syntax_getArg(v_x_4635_, v___x_4642_);
lean_dec(v_x_4635_);
v___x_4644_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4643_, v_a_4636_, v_a_4637_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; uint8_t v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4705_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref_known(v___x_4644_, 1);
v___x_4646_ = 0;
v___x_4647_ = l_Lean_MessageLog_toList(v_a_4645_);
v___x_4648_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4640_, v___x_4647_, v___x_4646_);
lean_dec(v___x_4647_);
v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4651_ = v___x_4648_;
v_isShared_4652_ = v_isSharedCheck_4705_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4648_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4705_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
uint8_t v___x_4653_; 
v___x_4653_ = lean_unbox(v_a_4649_);
lean_dec(v_a_4649_);
if (v___x_4653_ == 0)
{
lean_object* v___x_4654_; lean_object* v_env_4655_; lean_object* v_scopes_4656_; lean_object* v_usedQuotCtxts_4657_; lean_object* v_nextMacroScope_4658_; lean_object* v_maxRecDepth_4659_; lean_object* v_ngen_4660_; lean_object* v_auxDeclNGen_4661_; lean_object* v_infoState_4662_; lean_object* v_traceState_4663_; lean_object* v_snapshotTasks_4664_; lean_object* v_prevLinterStates_4665_; lean_object* v_codeQualityEntryTasks_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4676_; 
lean_del_object(v___x_4651_);
v___x_4654_ = lean_st_ref_take(v_a_4637_);
v_env_4655_ = lean_ctor_get(v___x_4654_, 0);
v_scopes_4656_ = lean_ctor_get(v___x_4654_, 2);
v_usedQuotCtxts_4657_ = lean_ctor_get(v___x_4654_, 3);
v_nextMacroScope_4658_ = lean_ctor_get(v___x_4654_, 4);
v_maxRecDepth_4659_ = lean_ctor_get(v___x_4654_, 5);
v_ngen_4660_ = lean_ctor_get(v___x_4654_, 6);
v_auxDeclNGen_4661_ = lean_ctor_get(v___x_4654_, 7);
v_infoState_4662_ = lean_ctor_get(v___x_4654_, 8);
v_traceState_4663_ = lean_ctor_get(v___x_4654_, 9);
v_snapshotTasks_4664_ = lean_ctor_get(v___x_4654_, 10);
v_prevLinterStates_4665_ = lean_ctor_get(v___x_4654_, 11);
v_codeQualityEntryTasks_4666_ = lean_ctor_get(v___x_4654_, 12);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4654_);
if (v_isSharedCheck_4676_ == 0)
{
lean_object* v_unused_4677_; 
v_unused_4677_ = lean_ctor_get(v___x_4654_, 1);
lean_dec(v_unused_4677_);
v___x_4668_ = v___x_4654_;
v_isShared_4669_ = v_isSharedCheck_4676_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4666_);
lean_inc(v_prevLinterStates_4665_);
lean_inc(v_snapshotTasks_4664_);
lean_inc(v_traceState_4663_);
lean_inc(v_infoState_4662_);
lean_inc(v_auxDeclNGen_4661_);
lean_inc(v_ngen_4660_);
lean_inc(v_maxRecDepth_4659_);
lean_inc(v_nextMacroScope_4658_);
lean_inc(v_usedQuotCtxts_4657_);
lean_inc(v_scopes_4656_);
lean_inc(v_env_4655_);
lean_dec(v___x_4654_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4676_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 1, v_a_4645_);
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_env_4655_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v_a_4645_);
lean_ctor_set(v_reuseFailAlloc_4675_, 2, v_scopes_4656_);
lean_ctor_set(v_reuseFailAlloc_4675_, 3, v_usedQuotCtxts_4657_);
lean_ctor_set(v_reuseFailAlloc_4675_, 4, v_nextMacroScope_4658_);
lean_ctor_set(v_reuseFailAlloc_4675_, 5, v_maxRecDepth_4659_);
lean_ctor_set(v_reuseFailAlloc_4675_, 6, v_ngen_4660_);
lean_ctor_set(v_reuseFailAlloc_4675_, 7, v_auxDeclNGen_4661_);
lean_ctor_set(v_reuseFailAlloc_4675_, 8, v_infoState_4662_);
lean_ctor_set(v_reuseFailAlloc_4675_, 9, v_traceState_4663_);
lean_ctor_set(v_reuseFailAlloc_4675_, 10, v_snapshotTasks_4664_);
lean_ctor_set(v_reuseFailAlloc_4675_, 11, v_prevLinterStates_4665_);
lean_ctor_set(v_reuseFailAlloc_4675_, 12, v_codeQualityEntryTasks_4666_);
v___x_4671_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = lean_st_ref_put(v_a_4637_, v___x_4671_);
v___x_4673_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4674_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4673_, v_a_4636_, v_a_4637_);
return v___x_4674_;
}
}
}
else
{
lean_object* v___x_4678_; lean_object* v_env_4679_; lean_object* v_scopes_4680_; lean_object* v_usedQuotCtxts_4681_; lean_object* v_nextMacroScope_4682_; lean_object* v_maxRecDepth_4683_; lean_object* v_ngen_4684_; lean_object* v_auxDeclNGen_4685_; lean_object* v_infoState_4686_; lean_object* v_traceState_4687_; lean_object* v_snapshotTasks_4688_; lean_object* v_prevLinterStates_4689_; lean_object* v_codeQualityEntryTasks_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4703_; 
lean_dec(v_a_4645_);
v___x_4678_ = lean_st_ref_take(v_a_4637_);
v_env_4679_ = lean_ctor_get(v___x_4678_, 0);
v_scopes_4680_ = lean_ctor_get(v___x_4678_, 2);
v_usedQuotCtxts_4681_ = lean_ctor_get(v___x_4678_, 3);
v_nextMacroScope_4682_ = lean_ctor_get(v___x_4678_, 4);
v_maxRecDepth_4683_ = lean_ctor_get(v___x_4678_, 5);
v_ngen_4684_ = lean_ctor_get(v___x_4678_, 6);
v_auxDeclNGen_4685_ = lean_ctor_get(v___x_4678_, 7);
v_infoState_4686_ = lean_ctor_get(v___x_4678_, 8);
v_traceState_4687_ = lean_ctor_get(v___x_4678_, 9);
v_snapshotTasks_4688_ = lean_ctor_get(v___x_4678_, 10);
v_prevLinterStates_4689_ = lean_ctor_get(v___x_4678_, 11);
v_codeQualityEntryTasks_4690_ = lean_ctor_get(v___x_4678_, 12);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4703_ == 0)
{
lean_object* v_unused_4704_; 
v_unused_4704_ = lean_ctor_get(v___x_4678_, 1);
lean_dec(v_unused_4704_);
v___x_4692_ = v___x_4678_;
v_isShared_4693_ = v_isSharedCheck_4703_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4690_);
lean_inc(v_prevLinterStates_4689_);
lean_inc(v_snapshotTasks_4688_);
lean_inc(v_traceState_4687_);
lean_inc(v_infoState_4686_);
lean_inc(v_auxDeclNGen_4685_);
lean_inc(v_ngen_4684_);
lean_inc(v_maxRecDepth_4683_);
lean_inc(v_nextMacroScope_4682_);
lean_inc(v_usedQuotCtxts_4681_);
lean_inc(v_scopes_4680_);
lean_inc(v_env_4679_);
lean_dec(v___x_4678_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4703_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4697_; 
v___x_4694_ = lean_box(0);
v___x_4695_ = l_Lean_MessageLog_empty;
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 1, v___x_4695_);
v___x_4697_ = v___x_4692_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_env_4679_);
lean_ctor_set(v_reuseFailAlloc_4702_, 1, v___x_4695_);
lean_ctor_set(v_reuseFailAlloc_4702_, 2, v_scopes_4680_);
lean_ctor_set(v_reuseFailAlloc_4702_, 3, v_usedQuotCtxts_4681_);
lean_ctor_set(v_reuseFailAlloc_4702_, 4, v_nextMacroScope_4682_);
lean_ctor_set(v_reuseFailAlloc_4702_, 5, v_maxRecDepth_4683_);
lean_ctor_set(v_reuseFailAlloc_4702_, 6, v_ngen_4684_);
lean_ctor_set(v_reuseFailAlloc_4702_, 7, v_auxDeclNGen_4685_);
lean_ctor_set(v_reuseFailAlloc_4702_, 8, v_infoState_4686_);
lean_ctor_set(v_reuseFailAlloc_4702_, 9, v_traceState_4687_);
lean_ctor_set(v_reuseFailAlloc_4702_, 10, v_snapshotTasks_4688_);
lean_ctor_set(v_reuseFailAlloc_4702_, 11, v_prevLinterStates_4689_);
lean_ctor_set(v_reuseFailAlloc_4702_, 12, v_codeQualityEntryTasks_4690_);
v___x_4697_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
lean_object* v___x_4698_; lean_object* v___x_4700_; 
v___x_4698_ = lean_st_ref_put(v_a_4637_, v___x_4697_);
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 0, v___x_4694_);
v___x_4700_ = v___x_4651_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v___x_4694_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
}
}
}
else
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4713_; 
v_a_4706_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4708_ = v___x_4644_;
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4644_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4711_; 
if (v_isShared_4709_ == 0)
{
v___x_4711_ = v___x_4708_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4706_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4714_, v_a_4715_, v_a_4716_);
lean_dec(v_a_4716_);
lean_dec_ref(v_a_4715_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4719_, lean_object* v_as_4720_, lean_object* v_as_x27_4721_, uint8_t v_b_4722_, lean_object* v_a_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4719_, v_as_x27_4721_, v_b_4722_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4728_, lean_object* v_as_4729_, lean_object* v_as_x27_4730_, lean_object* v_b_4731_, lean_object* v_a_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
uint8_t v_foundPanic_boxed_4736_; uint8_t v_b_boxed_4737_; lean_object* v_res_4738_; 
v_foundPanic_boxed_4736_ = lean_unbox(v_foundPanic_4728_);
v_b_boxed_4737_ = lean_unbox(v_b_4731_);
v_res_4738_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4736_, v_as_4729_, v_as_x27_4730_, v_b_boxed_4737_, v_a_4732_, v___y_4733_, v___y_4734_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v_as_x27_4730_);
lean_dec(v_as_4729_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4747_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4748_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4749_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4750_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4751_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4747_, v___x_4748_, v___x_4749_, v___x_4750_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4753_;
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
res = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_();
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
