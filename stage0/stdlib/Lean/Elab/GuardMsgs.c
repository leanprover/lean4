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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_Lean_CodeAction_insertBuiltin(lean_object*, lean_object*);
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
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Diff_Action_linePrefix(uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0;
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
static const lean_array_object l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_value)}};
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
lean_object* v___y_91_; lean_object* v___y_95_; uint32_t v___y_96_; lean_object* v_str_100_; lean_object* v_pos_112_; lean_object* v_endPos_113_; uint8_t v_severity_114_; lean_object* v_caption_115_; lean_object* v_data_116_; lean_object* v___y_118_; lean_object* v___y_119_; lean_object* v___y_120_; lean_object* v_str_131_; lean_object* v_str_143_; lean_object* v___y_154_; lean_object* v_str_158_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_pos_112_ = lean_ctor_get(v_msg_87_, 1);
lean_inc_ref(v_pos_112_);
v_endPos_113_ = lean_ctor_get(v_msg_87_, 2);
lean_inc(v_endPos_113_);
v_severity_114_ = lean_ctor_get_uint8(v_msg_87_, sizeof(void*)*5 + 1);
v_caption_115_ = lean_ctor_get(v_msg_87_, 3);
v_data_116_ = lean_ctor_get(v_msg_87_, 4);
lean_inc(v_data_116_);
v___x_165_ = l_Lean_MessageData_toString(v_data_116_);
v___x_166_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_167_ = lean_string_dec_eq(v_caption_115_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__11));
lean_inc_ref(v_caption_115_);
v___x_169_ = lean_string_append(v_caption_115_, v___x_168_);
v___x_170_ = lean_string_append(v___x_169_, v___x_165_);
lean_dec_ref(v___x_165_);
v_str_158_ = v___x_170_;
goto v___jp_157_;
}
else
{
v_str_158_ = v___x_165_;
goto v___jp_157_;
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
uint32_t v___x_97_; uint8_t v___x_98_; 
v___x_97_ = 10;
v___x_98_ = lean_uint32_dec_eq(v___y_96_, v___x_97_);
if (v___x_98_ == 0)
{
v___y_91_ = v___y_95_;
goto v___jp_90_;
}
else
{
return v___y_95_;
}
}
v___jp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_101_ = lean_string_utf8_byte_size(v_str_100_);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_nat_dec_eq(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_inc_ref(v_str_100_);
v___x_104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_104_, 0, v_str_100_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_101_);
v___x_105_ = l_String_Slice_Pos_prev_x3f(v___x_104_, v___x_101_);
if (lean_obj_tag(v___x_105_) == 0)
{
uint32_t v___x_106_; 
lean_dec_ref_known(v___x_104_, 3);
v___x_106_ = 65;
v___y_95_ = v_str_100_;
v___y_96_ = v___x_106_;
goto v___jp_94_;
}
else
{
lean_object* v_val_107_; lean_object* v___x_108_; 
v_val_107_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v___x_105_, 1);
v___x_108_ = l_String_Slice_Pos_get_x3f(v___x_104_, v_val_107_);
lean_dec(v_val_107_);
lean_dec_ref_known(v___x_104_, 3);
if (lean_obj_tag(v___x_108_) == 0)
{
uint32_t v___x_109_; 
v___x_109_ = 65;
v___y_95_ = v_str_100_;
v___y_96_ = v___x_109_;
goto v___jp_94_;
}
else
{
lean_object* v_val_110_; uint32_t v___x_111_; 
v_val_110_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_val_110_);
lean_dec_ref_known(v___x_108_, 1);
v___x_111_ = lean_unbox_uint32(v_val_110_);
lean_dec(v_val_110_);
v___y_95_ = v_str_100_;
v___y_96_ = v___x_111_;
goto v___jp_94_;
}
}
}
else
{
v___y_91_ = v_str_100_;
goto v___jp_90_;
}
}
v___jp_117_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_121_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__1));
v___x_122_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v___y_119_, v_pos_112_);
v___x_123_ = lean_string_append(v___x_121_, v___x_122_);
lean_dec_ref(v___x_122_);
v___x_124_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2));
v___x_125_ = lean_string_append(v___x_123_, v___x_124_);
v___x_126_ = lean_string_append(v___x_125_, v___y_120_);
lean_dec_ref(v___y_120_);
v___x_127_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_128_ = lean_string_append(v___x_126_, v___x_127_);
v___x_129_ = lean_string_append(v___x_128_, v___y_118_);
lean_dec_ref(v___y_118_);
v_str_100_ = v___x_129_;
goto v___jp_99_;
}
v___jp_130_:
{
if (lean_obj_tag(v_reportPos_x3f_88_) == 1)
{
if (lean_obj_tag(v_endPos_113_) == 0)
{
lean_object* v_val_132_; lean_object* v___x_133_; 
v_val_132_ = lean_ctor_get(v_reportPos_x3f_88_, 0);
v___x_133_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__3));
v___y_118_ = v_str_131_;
v___y_119_ = v_val_132_;
v___y_120_ = v___x_133_;
goto v___jp_117_;
}
else
{
lean_object* v_val_134_; lean_object* v_val_135_; lean_object* v_line_136_; lean_object* v_column_137_; lean_object* v_line_138_; uint8_t v___x_139_; 
v_val_134_ = lean_ctor_get(v_endPos_113_, 0);
lean_inc(v_val_134_);
lean_dec_ref_known(v_endPos_113_, 1);
v_val_135_ = lean_ctor_get(v_reportPos_x3f_88_, 0);
v_line_136_ = lean_ctor_get(v_val_134_, 0);
v_column_137_ = lean_ctor_get(v_val_134_, 1);
v_line_138_ = lean_ctor_get(v_pos_112_, 0);
v___x_139_ = lean_nat_dec_eq(v_line_136_, v_line_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v_val_135_, v_val_134_);
v___y_118_ = v_str_131_;
v___y_119_ = v_val_135_;
v___y_120_ = v___x_140_;
goto v___jp_117_;
}
else
{
lean_object* v___x_141_; 
lean_inc(v_column_137_);
lean_dec(v_val_134_);
v___x_141_ = l_Nat_reprFast(v_column_137_);
v___y_118_ = v_str_131_;
v___y_119_ = v_val_135_;
v___y_120_ = v___x_141_;
goto v___jp_117_;
}
}
}
else
{
lean_dec(v_endPos_113_);
lean_dec_ref(v_pos_112_);
v_str_100_ = v_str_131_;
goto v___jp_99_;
}
}
v___jp_142_:
{
uint8_t v___x_144_; 
v___x_144_ = l_Lean_Message_isTrace(v_msg_87_);
lean_dec_ref(v_msg_87_);
if (v___x_144_ == 0)
{
switch(v_severity_114_)
{
case 0:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__4));
v___x_146_ = lean_string_append(v___x_145_, v_str_143_);
lean_dec_ref(v_str_143_);
v_str_131_ = v___x_146_;
goto v___jp_130_;
}
case 1:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__5));
v___x_148_ = lean_string_append(v___x_147_, v_str_143_);
lean_dec_ref(v_str_143_);
v_str_131_ = v___x_148_;
goto v___jp_130_;
}
default: 
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__6));
v___x_150_ = lean_string_append(v___x_149_, v_str_143_);
lean_dec_ref(v_str_143_);
v_str_131_ = v___x_150_;
goto v___jp_130_;
}
}
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__7));
v___x_152_ = lean_string_append(v___x_151_, v_str_143_);
lean_dec_ref(v_str_143_);
v_str_131_ = v___x_152_;
goto v___jp_130_;
}
}
v___jp_153_:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_156_ = lean_string_append(v___x_155_, v___y_154_);
lean_dec_ref(v___y_154_);
v_str_143_ = v___x_156_;
goto v___jp_142_;
}
v___jp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_159_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_160_ = lean_string_utf8_byte_size(v_str_158_);
v___x_161_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_162_ = lean_nat_dec_le(v___x_161_, v___x_160_);
if (v___x_162_ == 0)
{
v___y_154_ = v_str_158_;
goto v___jp_153_;
}
else
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_string_memcmp(v_str_158_, v___x_159_, v___x_163_, v___x_163_, v___x_161_);
if (v___x_164_ == 0)
{
v___y_154_ = v_str_158_;
goto v___jp_153_;
}
else
{
v_str_143_ = v_str_158_;
goto v___jp_142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___boxed(lean_object* v_msg_171_, lean_object* v_reportPos_x3f_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_msg_171_, v_reportPos_x3f_172_);
lean_dec(v_reportPos_x3f_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(uint8_t v_x_175_){
_start:
{
switch(v_x_175_)
{
case 0:
{
lean_object* v___x_176_; 
v___x_176_ = lean_unsigned_to_nat(0u);
return v___x_176_;
}
case 1:
{
lean_object* v___x_177_; 
v___x_177_ = lean_unsigned_to_nat(1u);
return v___x_177_;
}
default: 
{
lean_object* v___x_178_; 
v___x_178_ = lean_unsigned_to_nat(2u);
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___boxed(lean_object* v_x_179_){
_start:
{
uint8_t v_x_boxed_180_; lean_object* v_res_181_; 
v_x_boxed_180_ = lean_unbox(v_x_179_);
v_res_181_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(v_x_boxed_180_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(lean_object* v_k_182_){
_start:
{
lean_inc(v_k_182_);
return v_k_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg___boxed(lean_object* v_k_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(v_k_183_);
lean_dec(v_k_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(lean_object* v_motive_185_, lean_object* v_ctorIdx_186_, uint8_t v_t_187_, lean_object* v_h_188_, lean_object* v_k_189_){
_start:
{
lean_inc(v_k_189_);
return v_k_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___boxed(lean_object* v_motive_190_, lean_object* v_ctorIdx_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_k_194_){
_start:
{
uint8_t v_t_boxed_195_; lean_object* v_res_196_; 
v_t_boxed_195_ = lean_unbox(v_t_192_);
v_res_196_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(v_motive_190_, v_ctorIdx_191_, v_t_boxed_195_, v_h_193_, v_k_194_);
lean_dec(v_k_194_);
lean_dec(v_ctorIdx_191_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(lean_object* v_check_197_){
_start:
{
lean_inc(v_check_197_);
return v_check_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg___boxed(lean_object* v_check_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(v_check_198_);
lean_dec(v_check_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(lean_object* v_motive_200_, uint8_t v_t_201_, lean_object* v_h_202_, lean_object* v_check_203_){
_start:
{
lean_inc(v_check_203_);
return v_check_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___boxed(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_check_207_){
_start:
{
uint8_t v_t_boxed_208_; lean_object* v_res_209_; 
v_t_boxed_208_ = lean_unbox(v_t_205_);
v_res_209_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(v_motive_204_, v_t_boxed_208_, v_h_206_, v_check_207_);
lean_dec(v_check_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(lean_object* v_drop_210_){
_start:
{
lean_inc(v_drop_210_);
return v_drop_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg___boxed(lean_object* v_drop_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(v_drop_211_);
lean_dec(v_drop_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(lean_object* v_motive_213_, uint8_t v_t_214_, lean_object* v_h_215_, lean_object* v_drop_216_){
_start:
{
lean_inc(v_drop_216_);
return v_drop_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___boxed(lean_object* v_motive_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_drop_220_){
_start:
{
uint8_t v_t_boxed_221_; lean_object* v_res_222_; 
v_t_boxed_221_ = lean_unbox(v_t_218_);
v_res_222_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(v_motive_217_, v_t_boxed_221_, v_h_219_, v_drop_220_);
lean_dec(v_drop_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(lean_object* v_pass_223_){
_start:
{
lean_inc(v_pass_223_);
return v_pass_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg___boxed(lean_object* v_pass_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(v_pass_224_);
lean_dec(v_pass_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(lean_object* v_motive_226_, uint8_t v_t_227_, lean_object* v_h_228_, lean_object* v_pass_229_){
_start:
{
lean_inc(v_pass_229_);
return v_pass_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___boxed(lean_object* v_motive_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_pass_233_){
_start:
{
uint8_t v_t_boxed_234_; lean_object* v_res_235_; 
v_t_boxed_234_ = lean_unbox(v_t_231_);
v_res_235_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(v_motive_230_, v_t_boxed_234_, v_h_232_, v_pass_233_);
lean_dec(v_pass_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(uint8_t v_x_236_){
_start:
{
switch(v_x_236_)
{
case 0:
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(0u);
return v___x_237_;
}
case 1:
{
lean_object* v___x_238_; 
v___x_238_ = lean_unsigned_to_nat(1u);
return v___x_238_;
}
default: 
{
lean_object* v___x_239_; 
v___x_239_ = lean_unsigned_to_nat(2u);
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___boxed(lean_object* v_x_240_){
_start:
{
uint8_t v_x_boxed_241_; lean_object* v_res_242_; 
v_x_boxed_241_ = lean_unbox(v_x_240_);
v_res_242_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(v_x_boxed_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(lean_object* v_k_243_){
_start:
{
lean_inc(v_k_243_);
return v_k_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg___boxed(lean_object* v_k_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(v_k_244_);
lean_dec(v_k_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(lean_object* v_motive_246_, lean_object* v_ctorIdx_247_, uint8_t v_t_248_, lean_object* v_h_249_, lean_object* v_k_250_){
_start:
{
lean_inc(v_k_250_);
return v_k_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___boxed(lean_object* v_motive_251_, lean_object* v_ctorIdx_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_k_255_){
_start:
{
uint8_t v_t_boxed_256_; lean_object* v_res_257_; 
v_t_boxed_256_ = lean_unbox(v_t_253_);
v_res_257_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(v_motive_251_, v_ctorIdx_252_, v_t_boxed_256_, v_h_254_, v_k_255_);
lean_dec(v_k_255_);
lean_dec(v_ctorIdx_252_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(lean_object* v_exact_258_){
_start:
{
lean_inc(v_exact_258_);
return v_exact_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg___boxed(lean_object* v_exact_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(v_exact_259_);
lean_dec(v_exact_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(lean_object* v_motive_261_, uint8_t v_t_262_, lean_object* v_h_263_, lean_object* v_exact_264_){
_start:
{
lean_inc(v_exact_264_);
return v_exact_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___boxed(lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_exact_268_){
_start:
{
uint8_t v_t_boxed_269_; lean_object* v_res_270_; 
v_t_boxed_269_ = lean_unbox(v_t_266_);
v_res_270_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(v_motive_265_, v_t_boxed_269_, v_h_267_, v_exact_268_);
lean_dec(v_exact_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(lean_object* v_normalized_271_){
_start:
{
lean_inc(v_normalized_271_);
return v_normalized_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg___boxed(lean_object* v_normalized_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(v_normalized_272_);
lean_dec(v_normalized_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(lean_object* v_motive_274_, uint8_t v_t_275_, lean_object* v_h_276_, lean_object* v_normalized_277_){
_start:
{
lean_inc(v_normalized_277_);
return v_normalized_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___boxed(lean_object* v_motive_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_normalized_281_){
_start:
{
uint8_t v_t_boxed_282_; lean_object* v_res_283_; 
v_t_boxed_282_ = lean_unbox(v_t_279_);
v_res_283_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(v_motive_278_, v_t_boxed_282_, v_h_280_, v_normalized_281_);
lean_dec(v_normalized_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(lean_object* v_lax_284_){
_start:
{
lean_inc(v_lax_284_);
return v_lax_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg___boxed(lean_object* v_lax_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(v_lax_285_);
lean_dec(v_lax_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(lean_object* v_motive_287_, uint8_t v_t_288_, lean_object* v_h_289_, lean_object* v_lax_290_){
_start:
{
lean_inc(v_lax_290_);
return v_lax_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___boxed(lean_object* v_motive_291_, lean_object* v_t_292_, lean_object* v_h_293_, lean_object* v_lax_294_){
_start:
{
uint8_t v_t_boxed_295_; lean_object* v_res_296_; 
v_t_boxed_295_ = lean_unbox(v_t_292_);
v_res_296_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(v_motive_291_, v_t_boxed_295_, v_h_293_, v_lax_294_);
lean_dec(v_lax_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(uint8_t v_x_297_){
_start:
{
if (v_x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_unsigned_to_nat(0u);
return v___x_298_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = lean_unsigned_to_nat(1u);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___boxed(lean_object* v_x_300_){
_start:
{
uint8_t v_x_boxed_301_; lean_object* v_res_302_; 
v_x_boxed_301_ = lean_unbox(v_x_300_);
v_res_302_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(v_x_boxed_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(lean_object* v_k_303_){
_start:
{
lean_inc(v_k_303_);
return v_k_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg___boxed(lean_object* v_k_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(v_k_304_);
lean_dec(v_k_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(lean_object* v_motive_306_, lean_object* v_ctorIdx_307_, uint8_t v_t_308_, lean_object* v_h_309_, lean_object* v_k_310_){
_start:
{
lean_inc(v_k_310_);
return v_k_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___boxed(lean_object* v_motive_311_, lean_object* v_ctorIdx_312_, lean_object* v_t_313_, lean_object* v_h_314_, lean_object* v_k_315_){
_start:
{
uint8_t v_t_boxed_316_; lean_object* v_res_317_; 
v_t_boxed_316_ = lean_unbox(v_t_313_);
v_res_317_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(v_motive_311_, v_ctorIdx_312_, v_t_boxed_316_, v_h_314_, v_k_315_);
lean_dec(v_k_315_);
lean_dec(v_ctorIdx_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(lean_object* v_exact_318_){
_start:
{
lean_inc(v_exact_318_);
return v_exact_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg___boxed(lean_object* v_exact_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(v_exact_319_);
lean_dec(v_exact_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(lean_object* v_motive_321_, uint8_t v_t_322_, lean_object* v_h_323_, lean_object* v_exact_324_){
_start:
{
lean_inc(v_exact_324_);
return v_exact_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___boxed(lean_object* v_motive_325_, lean_object* v_t_326_, lean_object* v_h_327_, lean_object* v_exact_328_){
_start:
{
uint8_t v_t_boxed_329_; lean_object* v_res_330_; 
v_t_boxed_329_ = lean_unbox(v_t_326_);
v_res_330_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(v_motive_325_, v_t_boxed_329_, v_h_327_, v_exact_328_);
lean_dec(v_exact_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(lean_object* v_sorted_331_){
_start:
{
lean_inc(v_sorted_331_);
return v_sorted_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg___boxed(lean_object* v_sorted_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(v_sorted_332_);
lean_dec(v_sorted_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(lean_object* v_motive_334_, uint8_t v_t_335_, lean_object* v_h_336_, lean_object* v_sorted_337_){
_start:
{
lean_inc(v_sorted_337_);
return v_sorted_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___boxed(lean_object* v_motive_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_sorted_341_){
_start:
{
uint8_t v_t_boxed_342_; lean_object* v_res_343_; 
v_t_boxed_342_ = lean_unbox(v_t_339_);
v_res_343_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(v_motive_338_, v_t_boxed_342_, v_h_340_, v_sorted_341_);
lean_dec(v_sorted_341_);
return v_res_343_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_box(0);
v___x_345_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg(){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___boxed(lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(lean_object* v_00_u03b1_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___boxed(lean_object* v_00_u03b1_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(v_00_u03b1_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(lean_object* v_action_x3f_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
if (lean_obj_tag(v_action_x3f_379_) == 1)
{
lean_object* v_val_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_414_; 
v_val_383_ = lean_ctor_get(v_action_x3f_379_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_action_x3f_379_);
if (v_isSharedCheck_414_ == 0)
{
v___x_385_ = v_action_x3f_379_;
v_isShared_386_ = v_isSharedCheck_414_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_val_383_);
lean_dec(v_action_x3f_379_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_414_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1));
lean_inc(v_val_383_);
v___x_388_ = l_Lean_Syntax_isOfKind(v_val_383_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
lean_del_object(v___x_385_);
lean_dec(v_val_383_);
v___x_389_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = l_Lean_Syntax_getArg(v_val_383_, v___x_390_);
lean_dec(v_val_383_);
v___x_392_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4));
lean_inc(v___x_391_);
v___x_393_ = l_Lean_Syntax_isOfKind(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6));
lean_inc(v___x_391_);
v___x_395_ = l_Lean_Syntax_isOfKind(v___x_391_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8));
v___x_397_ = l_Lean_Syntax_isOfKind(v___x_391_, v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
lean_del_object(v___x_385_);
v___x_398_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_398_;
}
else
{
uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_399_ = 2;
v___x_400_ = lean_box(v___x_399_);
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 0);
lean_ctor_set(v___x_385_, 0, v___x_400_);
v___x_402_ = v___x_385_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
else
{
uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
lean_dec(v___x_391_);
v___x_404_ = 1;
v___x_405_ = lean_box(v___x_404_);
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 0);
lean_ctor_set(v___x_385_, 0, v___x_405_);
v___x_407_ = v___x_385_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
lean_dec(v___x_391_);
v___x_409_ = 0;
v___x_410_ = lean_box(v___x_409_);
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 0);
lean_ctor_set(v___x_385_, 0, v___x_410_);
v___x_412_ = v___x_385_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
else
{
uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec(v_action_x3f_379_);
v___x_415_ = 0;
v___x_416_ = lean_box(v___x_415_);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___boxed(lean_object* v_action_x3f_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
return v_res_422_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(uint8_t v___x_423_, lean_object* v_x_424_){
_start:
{
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed(lean_object* v___x_425_, lean_object* v_x_426_){
_start:
{
uint8_t v___x_777__boxed_427_; uint8_t v_res_428_; lean_object* v_r_429_; 
v___x_777__boxed_427_ = lean_unbox(v___x_425_);
v_res_428_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_777__boxed_427_, v_x_426_);
lean_dec_ref(v_x_426_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(uint8_t v___x_430_, uint8_t v___x_431_, lean_object* v_msg_432_){
_start:
{
uint8_t v___y_434_; uint8_t v___x_438_; 
v___x_438_ = l_Lean_Message_isTrace(v_msg_432_);
if (v___x_438_ == 0)
{
v___y_434_ = v___x_431_;
goto v___jp_433_;
}
else
{
v___y_434_ = v___x_430_;
goto v___jp_433_;
}
v___jp_433_:
{
if (v___y_434_ == 0)
{
return v___x_430_;
}
else
{
uint8_t v_severity_435_; uint8_t v___x_436_; uint8_t v___x_437_; 
v_severity_435_ = lean_ctor_get_uint8(v_msg_432_, sizeof(void*)*5 + 1);
v___x_436_ = 2;
v___x_437_ = l_Lean_instBEqMessageSeverity_beq(v_severity_435_, v___x_436_);
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v_msg_441_){
_start:
{
uint8_t v___x_783__boxed_442_; uint8_t v___x_784__boxed_443_; uint8_t v_res_444_; lean_object* v_r_445_; 
v___x_783__boxed_442_ = lean_unbox(v___x_439_);
v___x_784__boxed_443_ = lean_unbox(v___x_440_);
v_res_444_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_783__boxed_442_, v___x_784__boxed_443_, v_msg_441_);
lean_dec_ref(v_msg_441_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(uint8_t v___x_446_, uint8_t v___x_447_, lean_object* v_msg_448_){
_start:
{
uint8_t v___y_450_; uint8_t v___x_454_; 
v___x_454_ = l_Lean_Message_isTrace(v_msg_448_);
if (v___x_454_ == 0)
{
v___y_450_ = v___x_447_;
goto v___jp_449_;
}
else
{
v___y_450_ = v___x_446_;
goto v___jp_449_;
}
v___jp_449_:
{
if (v___y_450_ == 0)
{
return v___x_446_;
}
else
{
uint8_t v_severity_451_; uint8_t v___x_452_; uint8_t v___x_453_; 
v_severity_451_ = lean_ctor_get_uint8(v_msg_448_, sizeof(void*)*5 + 1);
v___x_452_ = 1;
v___x_453_ = l_Lean_instBEqMessageSeverity_beq(v_severity_451_, v___x_452_);
return v___x_453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object* v___x_455_, lean_object* v___x_456_, lean_object* v_msg_457_){
_start:
{
uint8_t v___x_799__boxed_458_; uint8_t v___x_800__boxed_459_; uint8_t v_res_460_; lean_object* v_r_461_; 
v___x_799__boxed_458_ = lean_unbox(v___x_455_);
v___x_800__boxed_459_ = lean_unbox(v___x_456_);
v_res_460_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_799__boxed_458_, v___x_800__boxed_459_, v_msg_457_);
lean_dec_ref(v_msg_457_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(uint8_t v___x_462_, uint8_t v___x_463_, lean_object* v_msg_464_){
_start:
{
uint8_t v___y_466_; uint8_t v___x_470_; 
v___x_470_ = l_Lean_Message_isTrace(v_msg_464_);
if (v___x_470_ == 0)
{
v___y_466_ = v___x_463_;
goto v___jp_465_;
}
else
{
v___y_466_ = v___x_462_;
goto v___jp_465_;
}
v___jp_465_:
{
if (v___y_466_ == 0)
{
return v___x_462_;
}
else
{
uint8_t v_severity_467_; uint8_t v___x_468_; uint8_t v___x_469_; 
v_severity_467_ = lean_ctor_get_uint8(v_msg_464_, sizeof(void*)*5 + 1);
v___x_468_ = 0;
v___x_469_ = l_Lean_instBEqMessageSeverity_beq(v_severity_467_, v___x_468_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object* v___x_471_, lean_object* v___x_472_, lean_object* v_msg_473_){
_start:
{
uint8_t v___x_815__boxed_474_; uint8_t v___x_816__boxed_475_; uint8_t v_res_476_; lean_object* v_r_477_; 
v___x_815__boxed_474_ = lean_unbox(v___x_471_);
v___x_816__boxed_475_ = lean_unbox(v___x_472_);
v_res_476_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_815__boxed_474_, v___x_816__boxed_475_, v_msg_473_);
lean_dec_ref(v_msg_473_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(lean_object* v_x_503_){
_start:
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1));
lean_inc(v_x_503_);
v___x_506_ = l_Lean_Syntax_isOfKind(v_x_503_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
lean_dec(v_x_503_);
v___x_507_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = l_Lean_Syntax_getArg(v_x_503_, v___x_508_);
lean_dec(v_x_503_);
v___x_510_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3));
lean_inc(v___x_509_);
v___x_511_ = l_Lean_Syntax_isOfKind(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5));
lean_inc(v___x_509_);
v___x_513_ = l_Lean_Syntax_isOfKind(v___x_509_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7));
lean_inc(v___x_509_);
v___x_515_ = l_Lean_Syntax_isOfKind(v___x_509_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9));
lean_inc(v___x_509_);
v___x_517_ = l_Lean_Syntax_isOfKind(v___x_509_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11));
v___x_519_ = l_Lean_Syntax_isOfKind(v___x_509_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_520_;
}
else
{
lean_object* v___x_521_; lean_object* v___f_522_; lean_object* v___x_523_; 
v___x_521_ = lean_box(v___x_519_);
v___f_522_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_522_, 0, v___x_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___f_522_);
return v___x_523_;
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___f_526_; lean_object* v___x_527_; 
lean_dec(v___x_509_);
v___x_524_ = lean_box(v___x_515_);
v___x_525_ = lean_box(v___x_517_);
v___f_526_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_526_, 0, v___x_524_);
lean_closure_set(v___f_526_, 1, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___f_526_);
return v___x_527_;
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___f_530_; lean_object* v___x_531_; 
lean_dec(v___x_509_);
v___x_528_ = lean_box(v___x_513_);
v___x_529_ = lean_box(v___x_515_);
v___f_530_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_530_, 0, v___x_528_);
lean_closure_set(v___f_530_, 1, v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___f_530_);
return v___x_531_;
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___f_534_; lean_object* v___x_535_; 
lean_dec(v___x_509_);
v___x_532_ = lean_box(v___x_511_);
v___x_533_ = lean_box(v___x_513_);
v___f_534_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_534_, 0, v___x_532_);
lean_closure_set(v___f_534_, 1, v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___f_534_);
return v___x_535_;
}
}
else
{
lean_object* v___f_536_; lean_object* v___x_537_; 
lean_dec(v___x_509_);
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
lean_dec_ref_known(v_snd_556_, 1);
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
lean_dec_ref_known(v_snd_567_, 1);
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
uint8_t v_a_6444__boxed_580_; uint8_t v_res_581_; lean_object* v_r_582_; 
v_a_6444__boxed_580_ = lean_unbox(v_a_578_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_576_, v_snd_577_, v_a_6444__boxed_580_, v___y_579_);
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
lean_dec_ref_known(v___x_680_, 1);
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
lean_dec_ref_known(v___x_753_, 1);
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
lean_dec_ref_known(v___x_772_, 1);
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
lean_dec_ref_known(v___x_799_, 1);
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
lean_dec_ref_known(v___x_817_, 1);
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
lean_dec_ref_known(v___x_844_, 1);
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
lean_dec_ref_known(v___x_862_, 1);
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
lean_dec_ref_known(v___x_891_, 1);
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
lean_dec_ref_known(v___x_911_, 1);
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
lean_dec_ref_known(v___x_946_, 1);
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
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = l_Lean_Syntax_getArg(v___x_702_, v___x_707_);
lean_dec(v___x_702_);
v___x_709_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v___x_708_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___f_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v___f_713_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_713_, 0, v_a_712_);
lean_closure_set(v___f_713_, 1, v_snd_673_);
lean_closure_set(v___f_713_, 2, v_a_710_);
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
lean_dec(v_a_710_);
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
lean_dec(v___x_708_);
lean_del_object(v___x_675_);
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
lean_del_object(v___x_670_);
lean_dec(v_fst_668_);
lean_del_object(v___x_666_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
v_a_735_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_709_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_709_);
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
uint8_t v___x_7319__boxed_1040_; size_t v_i_boxed_1041_; size_t v_stop_boxed_1042_; lean_object* v_res_1043_; 
v___x_7319__boxed_1040_ = lean_unbox(v___x_1035_);
v_i_boxed_1041_ = lean_unbox_usize(v_i_1037_);
lean_dec(v_i_1037_);
v_stop_boxed_1042_ = lean_unbox_usize(v_stop_1038_);
lean_dec(v_stop_1038_);
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_7319__boxed_1040_, v_as_1036_, v_i_boxed_1041_, v_stop_boxed_1042_, v_b_1039_);
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
lean_inc_n(v_val_1131_, 2);
lean_dec_ref_known(v_spec_x3f_1072_, 1);
v___x_1132_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7));
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
lean_object* v___x_1150_; lean_object* v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; lean_object* v_snd_1155_; 
v___x_1150_ = lean_box(v___x_1149_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v___x_1147_);
v___x_1152_ = ((size_t)0ULL);
v___x_1153_ = lean_usize_of_nat(v___x_1148_);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1133_, v___x_1145_, v___x_1152_, v___x_1153_, v___x_1151_);
lean_dec_ref(v___x_1145_);
v_snd_1155_ = lean_ctor_get(v___x_1154_, 1);
lean_inc(v_snd_1155_);
lean_dec_ref(v___x_1154_);
v___y_1116_ = v_snd_1155_;
goto v___jp_1115_;
}
}
}
else
{
lean_object* v___x_1156_; 
lean_dec(v_spec_x3f_1072_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_cfg_1130_);
return v___x_1156_;
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
lean_dec_ref_known(v___x_1119_, 1);
v_elts_1077_ = v_val_1129_;
v___y_1078_ = v_a_1073_;
v___y_1079_ = v_a_1074_;
goto v___jp_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object* v_spec_x3f_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v_spec_x3f_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(lean_object* v_s_1174_, lean_object* v_replacement_1175_, lean_object* v_a_1176_, lean_object* v_b_1177_){
_start:
{
lean_object* v_it_1179_; lean_object* v_startPos_1180_; lean_object* v_endPos_1181_; lean_object* v_it_1190_; 
switch(lean_obj_tag(v_a_1176_))
{
case 0:
{
lean_object* v_pos_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1208_; 
v_pos_1196_ = lean_ctor_get(v_a_1176_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_a_1176_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1198_ = v_a_1176_;
v_isShared_1199_ = v_isSharedCheck_1208_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_pos_1196_);
lean_dec(v_a_1176_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1208_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v_startInclusive_1200_; lean_object* v_endExclusive_1201_; lean_object* v___x_1202_; uint8_t v_decide_1203_; 
v_startInclusive_1200_ = lean_ctor_get(v_s_1174_, 1);
v_endExclusive_1201_ = lean_ctor_get(v_s_1174_, 2);
v___x_1202_ = lean_nat_sub(v_endExclusive_1201_, v_startInclusive_1200_);
v_decide_1203_ = lean_nat_dec_eq(v_pos_1196_, v___x_1202_);
lean_dec(v___x_1202_);
if (v_decide_1203_ == 0)
{
lean_object* v___x_1205_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set_tag(v___x_1198_, 1);
v___x_1205_ = v___x_1198_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_pos_1196_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
v_it_1190_ = v___x_1205_;
goto v___jp_1189_;
}
}
else
{
lean_object* v___x_1207_; 
lean_del_object(v___x_1198_);
lean_dec(v_pos_1196_);
v___x_1207_ = lean_box(3);
v_it_1190_ = v___x_1207_;
goto v___jp_1189_;
}
}
}
case 1:
{
lean_object* v_pos_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1221_; 
v_pos_1209_ = lean_ctor_get(v_a_1176_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_a_1176_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1211_ = v_a_1176_;
v_isShared_1212_ = v_isSharedCheck_1221_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_pos_1209_);
lean_dec(v_a_1176_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1221_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_str_1213_; lean_object* v_startInclusive_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v_str_1213_ = lean_ctor_get(v_s_1174_, 0);
v_startInclusive_1214_ = lean_ctor_get(v_s_1174_, 1);
v___x_1215_ = lean_nat_add(v_startInclusive_1214_, v_pos_1209_);
v___x_1216_ = lean_string_utf8_next_fast(v_str_1213_, v___x_1215_);
lean_dec(v___x_1215_);
v___x_1217_ = lean_nat_sub(v___x_1216_, v_startInclusive_1214_);
lean_inc(v___x_1217_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set_tag(v___x_1211_, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1217_);
v___x_1219_ = v___x_1211_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
v_it_1179_ = v___x_1219_;
v_startPos_1180_ = v_pos_1209_;
v_endPos_1181_ = v___x_1217_;
goto v___jp_1178_;
}
}
}
case 2:
{
lean_object* v_needle_1222_; lean_object* v_table_1223_; lean_object* v_stackPos_1224_; lean_object* v_needlePos_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1286_; 
v_needle_1222_ = lean_ctor_get(v_a_1176_, 0);
v_table_1223_ = lean_ctor_get(v_a_1176_, 1);
v_stackPos_1224_ = lean_ctor_get(v_a_1176_, 2);
v_needlePos_1225_ = lean_ctor_get(v_a_1176_, 3);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_a_1176_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1227_ = v_a_1176_;
v_isShared_1228_ = v_isSharedCheck_1286_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_needlePos_1225_);
lean_inc(v_stackPos_1224_);
lean_inc(v_table_1223_);
lean_inc(v_needle_1222_);
lean_dec(v_a_1176_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1286_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_str_1229_; lean_object* v_startInclusive_1230_; lean_object* v_endExclusive_1231_; lean_object* v_str_1232_; lean_object* v_startInclusive_1233_; lean_object* v_endExclusive_1234_; lean_object* v_basePos_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_str_1229_ = lean_ctor_get(v_needle_1222_, 0);
v_startInclusive_1230_ = lean_ctor_get(v_needle_1222_, 1);
v_endExclusive_1231_ = lean_ctor_get(v_needle_1222_, 2);
v_str_1232_ = lean_ctor_get(v_s_1174_, 0);
v_startInclusive_1233_ = lean_ctor_get(v_s_1174_, 1);
v_endExclusive_1234_ = lean_ctor_get(v_s_1174_, 2);
v_basePos_1235_ = lean_nat_sub(v_stackPos_1224_, v_needlePos_1225_);
v___x_1236_ = lean_nat_sub(v_endExclusive_1231_, v_startInclusive_1230_);
v___x_1237_ = lean_nat_add(v_basePos_1235_, v___x_1236_);
v___x_1238_ = lean_nat_sub(v_endExclusive_1234_, v_startInclusive_1233_);
v___x_1239_ = lean_nat_dec_le(v___x_1237_, v___x_1238_);
lean_dec(v___x_1237_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
lean_dec(v___x_1236_);
lean_del_object(v___x_1227_);
lean_dec(v_needlePos_1225_);
lean_dec(v_stackPos_1224_);
lean_dec_ref(v_table_1223_);
lean_dec_ref(v_needle_1222_);
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = lean_nat_add(v_basePos_1235_, v___x_1240_);
v___x_1242_ = lean_nat_dec_le(v___x_1241_, v___x_1238_);
lean_dec(v___x_1241_);
if (v___x_1242_ == 0)
{
lean_dec(v___x_1238_);
lean_dec(v_basePos_1235_);
lean_dec_ref(v_s_1174_);
return v_b_1177_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = l_String_Slice_pos_x21(v_s_1174_, v_basePos_1235_);
lean_dec(v_basePos_1235_);
v___x_1244_ = lean_box(3);
v_it_1179_ = v___x_1244_;
v_startPos_1180_ = v___x_1243_;
v_endPos_1181_ = v___x_1238_;
goto v___jp_1178_;
}
}
else
{
lean_object* v___x_1245_; uint8_t v_stackByte_1246_; lean_object* v___x_1247_; uint8_t v_patByte_1248_; uint8_t v___x_1249_; 
lean_dec(v___x_1238_);
v___x_1245_ = lean_nat_add(v_startInclusive_1233_, v_stackPos_1224_);
v_stackByte_1246_ = lean_string_get_byte_fast(v_str_1232_, v___x_1245_);
v___x_1247_ = lean_nat_add(v_startInclusive_1230_, v_needlePos_1225_);
v_patByte_1248_ = lean_string_get_byte_fast(v_str_1229_, v___x_1247_);
v___x_1249_ = lean_uint8_dec_eq(v_stackByte_1246_, v_patByte_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; uint8_t v_decide_1251_; 
lean_dec(v___x_1236_);
v___x_1250_ = lean_unsigned_to_nat(0u);
v_decide_1251_ = lean_nat_dec_eq(v_needlePos_1225_, v___x_1250_);
if (v_decide_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_newNeedlePos_1254_; uint8_t v___x_1255_; 
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_sub(v_needlePos_1225_, v___x_1252_);
lean_dec(v_needlePos_1225_);
v_newNeedlePos_1254_ = lean_array_fget_borrowed(v_table_1223_, v___x_1253_);
lean_dec(v___x_1253_);
v___x_1255_ = lean_nat_dec_eq(v_newNeedlePos_1254_, v___x_1250_);
if (v___x_1255_ == 0)
{
lean_object* v_oldBasePos_1256_; lean_object* v___x_1257_; lean_object* v_newBasePos_1258_; lean_object* v___x_1260_; 
lean_inc(v_newNeedlePos_1254_);
v_oldBasePos_1256_ = l_String_Slice_pos_x21(v_s_1174_, v_basePos_1235_);
lean_dec(v_basePos_1235_);
v___x_1257_ = lean_nat_sub(v_stackPos_1224_, v_newNeedlePos_1254_);
v_newBasePos_1258_ = l_String_Slice_pos_x21(v_s_1174_, v___x_1257_);
lean_dec(v___x_1257_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v_newNeedlePos_1254_);
v___x_1260_ = v___x_1227_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_needle_1222_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_table_1223_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_stackPos_1224_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_newNeedlePos_1254_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
v_it_1179_ = v___x_1260_;
v_startPos_1180_ = v_oldBasePos_1256_;
v_endPos_1181_ = v_newBasePos_1258_;
goto v___jp_1178_;
}
}
else
{
lean_object* v_basePos_1262_; lean_object* v_nextStackPos_1263_; lean_object* v___x_1265_; 
v_basePos_1262_ = l_String_Slice_pos_x21(v_s_1174_, v_basePos_1235_);
lean_dec(v_basePos_1235_);
v_nextStackPos_1263_ = l_String_Slice_posGE___redArg(v_s_1174_, v_stackPos_1224_);
lean_inc(v_nextStackPos_1263_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v___x_1250_);
lean_ctor_set(v___x_1227_, 2, v_nextStackPos_1263_);
v___x_1265_ = v___x_1227_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_needle_1222_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_table_1223_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v_nextStackPos_1263_);
lean_ctor_set(v_reuseFailAlloc_1266_, 3, v___x_1250_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
v_it_1179_ = v___x_1265_;
v_startPos_1180_ = v_basePos_1262_;
v_endPos_1181_ = v_nextStackPos_1263_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v_basePos_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_nextStackPos_1270_; lean_object* v___x_1272_; 
lean_dec(v_basePos_1235_);
lean_dec(v_needlePos_1225_);
v_basePos_1267_ = l_String_Slice_pos_x21(v_s_1174_, v_stackPos_1224_);
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = lean_nat_add(v_stackPos_1224_, v___x_1268_);
lean_dec(v_stackPos_1224_);
v_nextStackPos_1270_ = l_String_Slice_posGE___redArg(v_s_1174_, v___x_1269_);
lean_inc(v_nextStackPos_1270_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v___x_1250_);
lean_ctor_set(v___x_1227_, 2, v_nextStackPos_1270_);
v___x_1272_ = v___x_1227_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_needle_1222_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_table_1223_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_nextStackPos_1270_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v___x_1250_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
v_it_1179_ = v___x_1272_;
v_startPos_1180_ = v_basePos_1267_;
v_endPos_1181_ = v_nextStackPos_1270_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v___x_1274_; lean_object* v_nextStackPos_1275_; lean_object* v_nextNeedlePos_1276_; uint8_t v_decide_1277_; 
lean_dec(v_basePos_1235_);
v___x_1274_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1275_ = lean_nat_add(v_stackPos_1224_, v___x_1274_);
lean_dec(v_stackPos_1224_);
v_nextNeedlePos_1276_ = lean_nat_add(v_needlePos_1225_, v___x_1274_);
lean_dec(v_needlePos_1225_);
v_decide_1277_ = lean_nat_dec_eq(v_nextNeedlePos_1276_, v___x_1236_);
lean_dec(v___x_1236_);
if (v_decide_1277_ == 0)
{
lean_object* v___x_1279_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v_nextNeedlePos_1276_);
lean_ctor_set(v___x_1227_, 2, v_nextStackPos_1275_);
v___x_1279_ = v___x_1227_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_needle_1222_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_table_1223_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v_nextStackPos_1275_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v_nextNeedlePos_1276_);
v___x_1279_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v_a_1176_ = v___x_1279_;
goto _start;
}
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
lean_dec(v_nextNeedlePos_1276_);
v___x_1282_ = lean_unsigned_to_nat(0u);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v___x_1282_);
lean_ctor_set(v___x_1227_, 2, v_nextStackPos_1275_);
v___x_1284_ = v___x_1227_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_needle_1222_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_table_1223_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_nextStackPos_1275_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
v_it_1190_ = v___x_1284_;
goto v___jp_1189_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1174_);
return v_b_1177_;
}
}
v___jp_1178_:
{
lean_object* v___x_1182_; lean_object* v_str_1183_; lean_object* v_startInclusive_1184_; lean_object* v_endExclusive_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_inc_ref(v_s_1174_);
v___x_1182_ = l_String_Slice_slice_x21(v_s_1174_, v_startPos_1180_, v_endPos_1181_);
lean_dec(v_endPos_1181_);
lean_dec(v_startPos_1180_);
v_str_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc_ref(v_str_1183_);
v_startInclusive_1184_ = lean_ctor_get(v___x_1182_, 1);
lean_inc(v_startInclusive_1184_);
v_endExclusive_1185_ = lean_ctor_get(v___x_1182_, 2);
lean_inc(v_endExclusive_1185_);
lean_dec_ref(v___x_1182_);
v___x_1186_ = lean_string_utf8_extract_fast(v_str_1183_, v_startInclusive_1184_, v_endExclusive_1185_);
lean_dec(v_endExclusive_1185_);
lean_dec(v_startInclusive_1184_);
lean_dec_ref(v_str_1183_);
v___x_1187_ = lean_string_append(v_b_1177_, v___x_1186_);
lean_dec_ref(v___x_1186_);
v_a_1176_ = v_it_1179_;
v_b_1177_ = v___x_1187_;
goto _start;
}
v___jp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_string_utf8_byte_size(v_replacement_1175_);
v___x_1193_ = lean_string_utf8_extract_fast(v_replacement_1175_, v___x_1191_, v___x_1192_);
v___x_1194_ = lean_string_append(v_b_1177_, v___x_1193_);
lean_dec_ref(v___x_1193_);
v_a_1176_ = v_it_1190_;
v_b_1177_ = v___x_1194_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg___boxed(lean_object* v_s_1287_, lean_object* v_replacement_1288_, lean_object* v_a_1289_, lean_object* v_b_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1287_, v_replacement_1288_, v_a_1289_, v_b_1290_);
lean_dec_ref(v_replacement_1288_);
return v_res_1291_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1294_ = lean_string_utf8_byte_size(v___x_1293_);
return v___x_1294_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1295_ = lean_unsigned_to_nat(0u);
v___x_1296_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1297_ = lean_nat_dec_eq(v___x_1296_, v___x_1295_);
return v___x_1297_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___x_1299_);
lean_ctor_set(v___x_1301_, 2, v___x_1298_);
return v___x_1301_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1303_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4);
v___x_1306_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1307_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1305_);
lean_ctor_set(v___x_1307_, 2, v___x_1304_);
lean_ctor_set(v___x_1307_, 3, v___x_1304_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object* v_s_1310_, lean_object* v_replacement_1311_){
_start:
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1313_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5);
v___x_1315_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1310_, v_replacement_1311_, v___x_1314_, v___x_1312_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1317_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1310_, v_replacement_1311_, v___x_1316_, v___x_1312_);
return v___x_1317_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___boxed(lean_object* v_s_1318_, lean_object* v_replacement_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1318_, v_replacement_1319_);
lean_dec_ref(v_replacement_1319_);
return v_res_1320_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1323_ = lean_string_utf8_byte_size(v___x_1322_);
return v___x_1323_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1326_ = lean_nat_dec_eq(v___x_1325_, v___x_1324_);
return v___x_1326_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1327_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v___x_1328_);
lean_ctor_set(v___x_1330_, 2, v___x_1327_);
return v___x_1330_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1332_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1331_);
return v___x_1332_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4);
v___x_1335_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1336_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v___x_1334_);
lean_ctor_set(v___x_1336_, 2, v___x_1333_);
lean_ctor_set(v___x_1336_, 3, v___x_1333_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object* v_s_1337_, lean_object* v_replacement_1338_){
_start:
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1340_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5);
v___x_1342_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1337_, v_replacement_1338_, v___x_1341_, v___x_1339_);
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1344_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1337_, v_replacement_1338_, v___x_1343_, v___x_1339_);
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object* v_s_1345_, lean_object* v_replacement_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1345_, v_replacement_1346_);
lean_dec_ref(v_replacement_1346_);
return v_res_1347_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1350_ = lean_string_utf8_byte_size(v___x_1349_);
return v___x_1350_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1353_ = lean_nat_dec_eq(v___x_1352_, v___x_1351_);
return v___x_1353_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1354_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v___x_1355_);
lean_ctor_set(v___x_1357_, 2, v___x_1354_);
return v___x_1357_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1359_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4);
v___x_1362_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1363_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v___x_1361_);
lean_ctor_set(v___x_1363_, 2, v___x_1360_);
lean_ctor_set(v___x_1363_, 3, v___x_1360_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(lean_object* v_s_1364_, lean_object* v_replacement_1365_){
_start:
{
lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1367_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5);
v___x_1369_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1364_, v_replacement_1365_, v___x_1368_, v___x_1366_);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1371_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1364_, v_replacement_1365_, v___x_1370_, v___x_1366_);
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___boxed(lean_object* v_s_1372_, lean_object* v_replacement_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1372_, v_replacement_1373_);
lean_dec_ref(v_replacement_1373_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object* v_s_1378_){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0));
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = lean_string_utf8_byte_size(v_s_1378_);
v___x_1382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1382_, 0, v_s_1378_);
lean_ctor_set(v___x_1382_, 1, v___x_1380_);
lean_ctor_set(v___x_1382_, 2, v___x_1381_);
v___x_1383_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1382_, v___x_1379_);
v___x_1384_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1));
v___x_1385_ = lean_string_utf8_byte_size(v___x_1383_);
v___x_1386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1383_);
lean_ctor_set(v___x_1386_, 1, v___x_1380_);
lean_ctor_set(v___x_1386_, 2, v___x_1385_);
v___x_1387_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v___x_1386_, v___x_1384_);
v___x_1388_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2));
v___x_1389_ = lean_string_utf8_byte_size(v___x_1387_);
v___x_1390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1387_);
lean_ctor_set(v___x_1390_, 1, v___x_1380_);
lean_ctor_set(v___x_1390_, 2, v___x_1389_);
v___x_1391_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v___x_1390_, v___x_1388_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(lean_object* v_s_1392_, lean_object* v_pattern_1393_, lean_object* v_replacement_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1392_, v_replacement_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___boxed(lean_object* v_s_1396_, lean_object* v_pattern_1397_, lean_object* v_replacement_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(v_s_1396_, v_pattern_1397_, v_replacement_1398_);
lean_dec_ref(v_replacement_1398_);
lean_dec_ref(v_pattern_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(lean_object* v_s_1400_, lean_object* v_pattern_1401_, lean_object* v_replacement_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1400_, v_replacement_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___boxed(lean_object* v_s_1404_, lean_object* v_pattern_1405_, lean_object* v_replacement_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(v_s_1404_, v_pattern_1405_, v_replacement_1406_);
lean_dec_ref(v_replacement_1406_);
lean_dec_ref(v_pattern_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(lean_object* v_s_1408_, lean_object* v_pattern_1409_, lean_object* v_replacement_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1408_, v_replacement_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___boxed(lean_object* v_s_1412_, lean_object* v_pattern_1413_, lean_object* v_replacement_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(v_s_1412_, v_pattern_1413_, v_replacement_1414_);
lean_dec_ref(v_replacement_1414_);
lean_dec_ref(v_pattern_1413_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(lean_object* v_s_1416_, lean_object* v_replacement_1417_, lean_object* v_inst_1418_, lean_object* v_R_1419_, lean_object* v_a_1420_, lean_object* v_b_1421_, lean_object* v_c_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1416_, v_replacement_1417_, v_a_1420_, v_b_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___boxed(lean_object* v_s_1424_, lean_object* v_replacement_1425_, lean_object* v_inst_1426_, lean_object* v_R_1427_, lean_object* v_a_1428_, lean_object* v_b_1429_, lean_object* v_c_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(v_s_1424_, v_replacement_1425_, v_inst_1426_, v_R_1427_, v_a_1428_, v_b_1429_, v_c_1430_);
lean_dec_ref(v_replacement_1425_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object* v_s_1432_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1433_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_string_utf8_byte_size(v_s_1432_);
v___x_1436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1436_, 0, v_s_1432_);
lean_ctor_set(v___x_1436_, 1, v___x_1434_);
lean_ctor_set(v___x_1436_, 2, v___x_1435_);
v___x_1437_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1436_, v___x_1433_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg(){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___closed__0));
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___boxed(lean_object* v___dummy_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
return v_res_1443_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object* v_s_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object* v_s_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v_s_1447_);
lean_dec_ref(v_s_1447_);
return v_res_1448_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1451_ = lean_nat_dec_eq(v___x_1450_, v___x_1449_);
return v___x_1451_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1452_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___x_1453_);
lean_ctor_set(v___x_1455_, 2, v___x_1452_);
return v___x_1455_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1457_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2);
v___x_1460_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1461_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v___x_1459_);
lean_ctor_set(v___x_1461_, 2, v___x_1458_);
lean_ctor_set(v___x_1461_, 3, v___x_1458_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object* v_s_1462_, lean_object* v_replacement_1463_){
_start:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1465_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3);
v___x_1467_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1462_, v_replacement_1463_, v___x_1466_, v___x_1464_);
return v___x_1467_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1469_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1462_, v_replacement_1463_, v___x_1468_, v___x_1464_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object* v_s_1470_, lean_object* v_replacement_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1470_, v_replacement_1471_);
lean_dec_ref(v_replacement_1471_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object* v_s_1473_, lean_object* v___x_1474_, lean_object* v___x_1475_, lean_object* v_a_1476_, lean_object* v_b_1477_){
_start:
{
lean_object* v_it_1479_; lean_object* v_startInclusive_1480_; lean_object* v_endExclusive_1481_; 
if (lean_obj_tag(v_a_1476_) == 0)
{
lean_object* v_currPos_1489_; lean_object* v_searcher_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1518_; 
v_currPos_1489_ = lean_ctor_get(v_a_1476_, 0);
v_searcher_1490_ = lean_ctor_get(v_a_1476_, 1);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_a_1476_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1492_ = v_a_1476_;
v_isShared_1493_ = v_isSharedCheck_1518_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_searcher_1490_);
lean_inc(v_currPos_1489_);
lean_dec(v_a_1476_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1518_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
uint8_t v_decide_1504_; 
v_decide_1504_ = lean_nat_dec_eq(v_searcher_1490_, v___x_1475_);
if (v_decide_1504_ == 0)
{
uint32_t v___x_1505_; uint32_t v___x_1506_; uint8_t v___x_1507_; 
v___x_1505_ = lean_string_utf8_get_fast(v_s_1473_, v_searcher_1490_);
v___x_1506_ = 32;
v___x_1507_ = lean_uint32_dec_eq(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
uint32_t v___x_1508_; uint8_t v___x_1509_; 
v___x_1508_ = 9;
v___x_1509_ = lean_uint32_dec_eq(v___x_1505_, v___x_1508_);
if (v___x_1509_ == 0)
{
uint32_t v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = 13;
v___x_1511_ = lean_uint32_dec_eq(v___x_1505_, v___x_1510_);
if (v___x_1511_ == 0)
{
uint32_t v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = 10;
v___x_1513_ = lean_uint32_dec_eq(v___x_1505_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_del_object(v___x_1492_);
v___x_1514_ = lean_string_utf8_next_fast(v_s_1473_, v_searcher_1490_);
lean_dec(v_searcher_1490_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_currPos_1489_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v_a_1476_ = v___x_1515_;
goto _start;
}
else
{
goto v___jp_1494_;
}
}
else
{
goto v___jp_1494_;
}
}
else
{
goto v___jp_1494_;
}
}
else
{
goto v___jp_1494_;
}
}
else
{
lean_object* v___x_1517_; 
lean_del_object(v___x_1492_);
lean_dec(v_searcher_1490_);
v___x_1517_ = lean_box(1);
lean_inc(v___x_1475_);
v_it_1479_ = v___x_1517_;
v_startInclusive_1480_ = v_currPos_1489_;
v_endExclusive_1481_ = v___x_1475_;
goto v___jp_1478_;
}
v___jp_1494_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_slice_1498_; lean_object* v_nextIt_1500_; 
v___x_1495_ = lean_string_utf8_next_fast(v_s_1473_, v_searcher_1490_);
v___x_1496_ = lean_nat_sub(v___x_1495_, v_searcher_1490_);
v___x_1497_ = lean_nat_add(v_searcher_1490_, v___x_1496_);
lean_dec(v___x_1496_);
v_slice_1498_ = l_String_Slice_subslice_x21(v___x_1474_, v_currPos_1489_, v_searcher_1490_);
lean_inc(v___x_1497_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 1, v___x_1497_);
lean_ctor_set(v___x_1492_, 0, v___x_1497_);
v_nextIt_1500_ = v___x_1492_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v___x_1497_);
v_nextIt_1500_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v_startInclusive_1501_; lean_object* v_endExclusive_1502_; 
v_startInclusive_1501_ = lean_ctor_get(v_slice_1498_, 0);
lean_inc(v_startInclusive_1501_);
v_endExclusive_1502_ = lean_ctor_get(v_slice_1498_, 1);
lean_inc(v_endExclusive_1502_);
lean_dec_ref(v_slice_1498_);
v_it_1479_ = v_nextIt_1500_;
v_startInclusive_1480_ = v_startInclusive_1501_;
v_endExclusive_1481_ = v_endExclusive_1502_;
goto v___jp_1478_;
}
}
}
}
else
{
lean_dec(v___x_1475_);
lean_dec_ref(v_s_1473_);
return v_b_1477_;
}
v___jp_1478_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1482_ = lean_nat_sub(v_endExclusive_1481_, v_startInclusive_1480_);
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = lean_nat_dec_eq(v___x_1482_, v___x_1483_);
lean_dec(v___x_1482_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_inc_ref(v_s_1473_);
v___x_1485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1485_, 0, v_s_1473_);
lean_ctor_set(v___x_1485_, 1, v_startInclusive_1480_);
lean_ctor_set(v___x_1485_, 2, v_endExclusive_1481_);
v___x_1486_ = lean_array_push(v_b_1477_, v___x_1485_);
v_a_1476_ = v_it_1479_;
v_b_1477_ = v___x_1486_;
goto _start;
}
else
{
lean_dec(v_endExclusive_1481_);
lean_dec(v_startInclusive_1480_);
v_a_1476_ = v_it_1479_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object* v_s_1519_, lean_object* v___x_1520_, lean_object* v___x_1521_, lean_object* v_a_1522_, lean_object* v_b_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1519_, v___x_1520_, v___x_1521_, v_a_1522_, v_b_1523_);
lean_dec_ref(v___x_1520_);
return v_res_1524_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1526_ = lean_string_utf8_byte_size(v___x_1525_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1527_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0);
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v___x_1528_);
lean_ctor_set(v___x_1530_, 2, v___x_1527_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t v_mode_1533_, lean_object* v_s_1534_){
_start:
{
switch(v_mode_1533_)
{
case 0:
{
return v_s_1534_;
}
case 1:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = lean_string_utf8_byte_size(v_s_1534_);
v___x_1538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1538_, 0, v_s_1534_);
lean_ctor_set(v___x_1538_, 1, v___x_1536_);
lean_ctor_set(v___x_1538_, 2, v___x_1537_);
v___x_1539_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v___x_1538_, v___x_1535_);
return v___x_1539_;
}
default: 
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1);
v___x_1542_ = lean_string_utf8_byte_size(v_s_1534_);
lean_inc_ref(v_s_1534_);
v___x_1543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1543_, 0, v_s_1534_);
lean_ctor_set(v___x_1543_, 1, v___x_1540_);
lean_ctor_set(v___x_1543_, 2, v___x_1542_);
v___x_1544_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0);
v___x_1545_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__2));
v___x_1546_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1534_, v___x_1543_, v___x_1542_, v___x_1544_, v___x_1545_);
lean_dec_ref_known(v___x_1543_, 3);
v___x_1547_ = lean_array_to_list(v___x_1546_);
v___x_1548_ = l_String_Slice_intercalate(v___x_1541_, v___x_1547_);
lean_dec(v___x_1547_);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object* v_mode_1549_, lean_object* v_s_1550_){
_start:
{
uint8_t v_mode_boxed_1551_; lean_object* v_res_1552_; 
v_mode_boxed_1551_ = lean_unbox(v_mode_1549_);
v_res_1552_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v_mode_boxed_1551_, v_s_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object* v_s_1553_, lean_object* v_pattern_1554_, lean_object* v_replacement_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1553_, v_replacement_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object* v_s_1557_, lean_object* v_pattern_1558_, lean_object* v_replacement_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(v_s_1557_, v_pattern_1558_, v_replacement_1559_);
lean_dec_ref(v_replacement_1559_);
lean_dec_ref(v_pattern_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object* v_s_1561_, lean_object* v___x_1562_, lean_object* v___x_1563_, lean_object* v_inst_1564_, lean_object* v_R_1565_, lean_object* v_a_1566_, lean_object* v_b_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1561_, v___x_1562_, v___x_1563_, v_a_1566_, v_b_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___boxed(lean_object* v_s_1569_, lean_object* v___x_1570_, lean_object* v___x_1571_, lean_object* v_inst_1572_, lean_object* v_R_1573_, lean_object* v_a_1574_, lean_object* v_b_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(v_s_1569_, v___x_1570_, v___x_1571_, v_inst_1572_, v_R_1573_, v_a_1574_, v_b_1575_);
lean_dec_ref(v___x_1570_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(lean_object* v_hi_1577_, lean_object* v_pivot_1578_, lean_object* v_as_1579_, lean_object* v_i_1580_, lean_object* v_k_1581_){
_start:
{
uint8_t v___x_1582_; 
v___x_1582_ = lean_nat_dec_lt(v_k_1581_, v_hi_1577_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec(v_k_1581_);
v___x_1583_ = lean_array_fswap(v_as_1579_, v_i_1580_, v_hi_1577_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v_i_1580_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = lean_array_fget_borrowed(v_as_1579_, v_k_1581_);
v___x_1586_ = lean_string_dec_lt(v___x_1585_, v_pivot_1578_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_unsigned_to_nat(1u);
v___x_1588_ = lean_nat_add(v_k_1581_, v___x_1587_);
lean_dec(v_k_1581_);
v_k_1581_ = v___x_1588_;
goto _start;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1590_ = lean_array_fswap(v_as_1579_, v_i_1580_, v_k_1581_);
v___x_1591_ = lean_unsigned_to_nat(1u);
v___x_1592_ = lean_nat_add(v_i_1580_, v___x_1591_);
lean_dec(v_i_1580_);
v___x_1593_ = lean_nat_add(v_k_1581_, v___x_1591_);
lean_dec(v_k_1581_);
v_as_1579_ = v___x_1590_;
v_i_1580_ = v___x_1592_;
v_k_1581_ = v___x_1593_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg___boxed(lean_object* v_hi_1595_, lean_object* v_pivot_1596_, lean_object* v_as_1597_, lean_object* v_i_1598_, lean_object* v_k_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1595_, v_pivot_1596_, v_as_1597_, v_i_1598_, v_k_1599_);
lean_dec_ref(v_pivot_1596_);
lean_dec(v_hi_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object* v_n_1601_, lean_object* v_as_1602_, lean_object* v_lo_1603_, lean_object* v_hi_1604_){
_start:
{
lean_object* v___y_1606_; uint8_t v___x_1616_; 
v___x_1616_ = lean_nat_dec_lt(v_lo_1603_, v_hi_1604_);
if (v___x_1616_ == 0)
{
lean_dec(v_lo_1603_);
return v_as_1602_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_mid_1619_; lean_object* v___y_1621_; lean_object* v___y_1627_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1617_ = lean_nat_add(v_lo_1603_, v_hi_1604_);
v___x_1618_ = lean_unsigned_to_nat(1u);
v_mid_1619_ = lean_nat_shiftr(v___x_1617_, v___x_1618_);
lean_dec(v___x_1617_);
v___x_1632_ = lean_array_fget_borrowed(v_as_1602_, v_mid_1619_);
v___x_1633_ = lean_array_fget_borrowed(v_as_1602_, v_lo_1603_);
v___x_1634_ = lean_string_dec_lt(v___x_1632_, v___x_1633_);
if (v___x_1634_ == 0)
{
v___y_1627_ = v_as_1602_;
goto v___jp_1626_;
}
else
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_array_fswap(v_as_1602_, v_lo_1603_, v_mid_1619_);
v___y_1627_ = v___x_1635_;
goto v___jp_1626_;
}
v___jp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1622_ = lean_array_fget_borrowed(v___y_1621_, v_mid_1619_);
v___x_1623_ = lean_array_fget_borrowed(v___y_1621_, v_hi_1604_);
v___x_1624_ = lean_string_dec_lt(v___x_1622_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_dec(v_mid_1619_);
v___y_1606_ = v___y_1621_;
goto v___jp_1605_;
}
else
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_array_fswap(v___y_1621_, v_mid_1619_, v_hi_1604_);
lean_dec(v_mid_1619_);
v___y_1606_ = v___x_1625_;
goto v___jp_1605_;
}
}
v___jp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1628_ = lean_array_fget_borrowed(v___y_1627_, v_hi_1604_);
v___x_1629_ = lean_array_fget_borrowed(v___y_1627_, v_lo_1603_);
v___x_1630_ = lean_string_dec_lt(v___x_1628_, v___x_1629_);
if (v___x_1630_ == 0)
{
v___y_1621_ = v___y_1627_;
goto v___jp_1620_;
}
else
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_array_fswap(v___y_1627_, v_lo_1603_, v_hi_1604_);
v___y_1621_ = v___x_1631_;
goto v___jp_1620_;
}
}
}
v___jp_1605_:
{
lean_object* v_pivot_1607_; lean_object* v___x_1608_; lean_object* v_fst_1609_; lean_object* v_snd_1610_; uint8_t v___x_1611_; 
v_pivot_1607_ = lean_array_fget(v___y_1606_, v_hi_1604_);
lean_inc_n(v_lo_1603_, 2);
v___x_1608_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1604_, v_pivot_1607_, v___y_1606_, v_lo_1603_, v_lo_1603_);
lean_dec(v_pivot_1607_);
v_fst_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_fst_1609_);
v_snd_1610_ = lean_ctor_get(v___x_1608_, 1);
lean_inc(v_snd_1610_);
lean_dec_ref(v___x_1608_);
v___x_1611_ = lean_nat_dec_le(v_hi_1604_, v_fst_1609_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1601_, v_snd_1610_, v_lo_1603_, v_fst_1609_);
v___x_1613_ = lean_unsigned_to_nat(1u);
v___x_1614_ = lean_nat_add(v_fst_1609_, v___x_1613_);
lean_dec(v_fst_1609_);
v_as_1602_ = v___x_1612_;
v_lo_1603_ = v___x_1614_;
goto _start;
}
else
{
lean_dec(v_fst_1609_);
lean_dec(v_lo_1603_);
return v_snd_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object* v_n_1636_, lean_object* v_as_1637_, lean_object* v_lo_1638_, lean_object* v_hi_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1636_, v_as_1637_, v_lo_1638_, v_hi_1639_);
lean_dec(v_hi_1639_);
lean_dec(v_n_1636_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t v_mode_1641_, lean_object* v_msgs_1642_){
_start:
{
if (v_mode_1641_ == 0)
{
return v_msgs_1642_;
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1643_ = lean_array_mk(v_msgs_1642_);
v___x_1644_ = lean_array_get_size(v___x_1643_);
v___x_1650_ = lean_unsigned_to_nat(0u);
v___x_1651_ = lean_nat_dec_eq(v___x_1644_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___y_1655_; uint8_t v___x_1657_; 
v___x_1652_ = lean_unsigned_to_nat(1u);
v___x_1653_ = lean_nat_sub(v___x_1644_, v___x_1652_);
v___x_1657_ = lean_nat_dec_le(v___x_1650_, v___x_1653_);
if (v___x_1657_ == 0)
{
lean_inc(v___x_1653_);
v___y_1655_ = v___x_1653_;
goto v___jp_1654_;
}
else
{
v___y_1655_ = v___x_1650_;
goto v___jp_1654_;
}
v___jp_1654_:
{
uint8_t v___x_1656_; 
v___x_1656_ = lean_nat_dec_le(v___y_1655_, v___x_1653_);
if (v___x_1656_ == 0)
{
lean_dec(v___x_1653_);
lean_inc(v___y_1655_);
v___y_1646_ = v___y_1655_;
v___y_1647_ = v___y_1655_;
goto v___jp_1645_;
}
else
{
v___y_1646_ = v___y_1655_;
v___y_1647_ = v___x_1653_;
goto v___jp_1645_;
}
}
}
else
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_array_to_list(v___x_1643_);
return v___x_1658_;
}
v___jp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v___x_1644_, v___x_1643_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
v___x_1649_ = lean_array_to_list(v___x_1648_);
return v___x_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* v_mode_1659_, lean_object* v_msgs_1660_){
_start:
{
uint8_t v_mode_boxed_1661_; lean_object* v_res_1662_; 
v_mode_boxed_1661_ = lean_unbox(v_mode_1659_);
v_res_1662_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_boxed_1661_, v_msgs_1660_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object* v_n_1663_, lean_object* v_as_1664_, lean_object* v_lo_1665_, lean_object* v_hi_1666_, lean_object* v_w_1667_, lean_object* v_hlo_1668_, lean_object* v_hhi_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1663_, v_as_1664_, v_lo_1665_, v_hi_1666_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object* v_n_1671_, lean_object* v_as_1672_, lean_object* v_lo_1673_, lean_object* v_hi_1674_, lean_object* v_w_1675_, lean_object* v_hlo_1676_, lean_object* v_hhi_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(v_n_1671_, v_as_1672_, v_lo_1673_, v_hi_1674_, v_w_1675_, v_hlo_1676_, v_hhi_1677_);
lean_dec(v_hi_1674_);
lean_dec(v_n_1671_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(lean_object* v_n_1679_, lean_object* v_lo_1680_, lean_object* v_hi_1681_, lean_object* v_hhi_1682_, lean_object* v_pivot_1683_, lean_object* v_as_1684_, lean_object* v_i_1685_, lean_object* v_k_1686_, lean_object* v_ilo_1687_, lean_object* v_ik_1688_, lean_object* v_w_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1681_, v_pivot_1683_, v_as_1684_, v_i_1685_, v_k_1686_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___boxed(lean_object* v_n_1691_, lean_object* v_lo_1692_, lean_object* v_hi_1693_, lean_object* v_hhi_1694_, lean_object* v_pivot_1695_, lean_object* v_as_1696_, lean_object* v_i_1697_, lean_object* v_k_1698_, lean_object* v_ilo_1699_, lean_object* v_ik_1700_, lean_object* v_w_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(v_n_1691_, v_lo_1692_, v_hi_1693_, v_hhi_1694_, v_pivot_1695_, v_as_1696_, v_i_1697_, v_k_1698_, v_ilo_1699_, v_ik_1700_, v_w_1701_);
lean_dec_ref(v_pivot_1695_);
lean_dec(v_hi_1693_);
lean_dec(v_lo_1692_);
lean_dec(v_n_1691_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object* v_as_1703_, size_t v_i_1704_, size_t v_stop_1705_, lean_object* v_b_1706_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = lean_usize_dec_eq(v_i_1704_, v_stop_1705_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v_diagnostics_1709_; lean_object* v_msgLog_1710_; lean_object* v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; 
v___x_1708_ = lean_array_uget_borrowed(v_as_1703_, v_i_1704_);
v_diagnostics_1709_ = lean_ctor_get(v___x_1708_, 1);
v_msgLog_1710_ = lean_ctor_get(v_diagnostics_1709_, 0);
lean_inc_ref(v_msgLog_1710_);
v___x_1711_ = l_Lean_MessageLog_append(v_b_1706_, v_msgLog_1710_);
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_add(v_i_1704_, v___x_1712_);
v_i_1704_ = v___x_1713_;
v_b_1706_ = v___x_1711_;
goto _start;
}
else
{
return v_b_1706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0___boxed(lean_object* v_as_1715_, lean_object* v_i_1716_, lean_object* v_stop_1717_, lean_object* v_b_1718_){
_start:
{
size_t v_i_boxed_1719_; size_t v_stop_boxed_1720_; lean_object* v_res_1721_; 
v_i_boxed_1719_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_stop_boxed_1720_ = lean_unbox_usize(v_stop_1717_);
lean_dec(v_stop_1717_);
v_res_1721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v_as_1715_, v_i_boxed_1719_, v_stop_boxed_1720_, v_b_1718_);
lean_dec_ref(v_as_1715_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object* v_as_1722_, size_t v_i_1723_, size_t v_stop_1724_, lean_object* v_b_1725_){
_start:
{
lean_object* v___y_1727_; uint8_t v___x_1731_; 
v___x_1731_ = lean_usize_dec_eq(v_i_1723_, v_stop_1724_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1732_ = lean_array_uget_borrowed(v_as_1722_, v_i_1723_);
v___x_1733_ = l_Lean_MessageLog_empty;
lean_inc(v___x_1732_);
v___x_1734_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1732_);
v___x_1735_ = l_Lean_Language_SnapshotTree_getAll(v___x_1734_);
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_array_get_size(v___x_1735_);
v___x_1738_ = lean_nat_dec_lt(v___x_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
lean_dec_ref(v___x_1735_);
v___x_1739_ = l_Lean_MessageLog_append(v_b_1725_, v___x_1733_);
v___y_1727_ = v___x_1739_;
goto v___jp_1726_;
}
else
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_nat_dec_le(v___x_1737_, v___x_1737_);
if (v___x_1740_ == 0)
{
if (v___x_1738_ == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref(v___x_1735_);
v___x_1741_ = l_Lean_MessageLog_append(v_b_1725_, v___x_1733_);
v___y_1727_ = v___x_1741_;
goto v___jp_1726_;
}
else
{
size_t v___x_1742_; size_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1742_ = ((size_t)0ULL);
v___x_1743_ = lean_usize_of_nat(v___x_1737_);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1735_, v___x_1742_, v___x_1743_, v___x_1733_);
lean_dec_ref(v___x_1735_);
v___x_1745_ = l_Lean_MessageLog_append(v_b_1725_, v___x_1744_);
v___y_1727_ = v___x_1745_;
goto v___jp_1726_;
}
}
else
{
size_t v___x_1746_; size_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1746_ = ((size_t)0ULL);
v___x_1747_ = lean_usize_of_nat(v___x_1737_);
v___x_1748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1735_, v___x_1746_, v___x_1747_, v___x_1733_);
lean_dec_ref(v___x_1735_);
v___x_1749_ = l_Lean_MessageLog_append(v_b_1725_, v___x_1748_);
v___y_1727_ = v___x_1749_;
goto v___jp_1726_;
}
}
}
else
{
return v_b_1725_;
}
v___jp_1726_:
{
size_t v___x_1728_; size_t v___x_1729_; 
v___x_1728_ = ((size_t)1ULL);
v___x_1729_ = lean_usize_add(v_i_1723_, v___x_1728_);
v_i_1723_ = v___x_1729_;
v_b_1725_ = v___y_1727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1___boxed(lean_object* v_as_1750_, lean_object* v_i_1751_, lean_object* v_stop_1752_, lean_object* v_b_1753_){
_start:
{
size_t v_i_boxed_1754_; size_t v_stop_boxed_1755_; lean_object* v_res_1756_; 
v_i_boxed_1754_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_stop_boxed_1755_ = lean_unbox_usize(v_stop_1752_);
lean_dec(v_stop_1752_);
v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_as_1750_, v_i_boxed_1754_, v_stop_boxed_1755_, v_b_1753_);
lean_dec_ref(v_as_1750_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object* v_cmd_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_fileName_1763_; lean_object* v_fileMap_1764_; lean_object* v_currRecDepth_1765_; lean_object* v_cmdPos_1766_; lean_object* v_macroStack_1767_; lean_object* v_quotContext_x3f_1768_; lean_object* v_currMacroScope_1769_; lean_object* v_ref_1770_; lean_object* v_cancelTk_x3f_1771_; uint8_t v_suppressElabErrors_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_fileName_1763_ = lean_ctor_get(v_a_1760_, 0);
v_fileMap_1764_ = lean_ctor_get(v_a_1760_, 1);
v_currRecDepth_1765_ = lean_ctor_get(v_a_1760_, 2);
v_cmdPos_1766_ = lean_ctor_get(v_a_1760_, 3);
v_macroStack_1767_ = lean_ctor_get(v_a_1760_, 4);
v_quotContext_x3f_1768_ = lean_ctor_get(v_a_1760_, 5);
v_currMacroScope_1769_ = lean_ctor_get(v_a_1760_, 6);
v_ref_1770_ = lean_ctor_get(v_a_1760_, 7);
v_cancelTk_x3f_1771_ = lean_ctor_get(v_a_1760_, 9);
v_suppressElabErrors_1772_ = lean_ctor_get_uint8(v_a_1760_, sizeof(void*)*10);
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
v___x_1775_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1771_);
lean_inc(v_ref_1770_);
lean_inc(v_currMacroScope_1769_);
lean_inc(v_quotContext_x3f_1768_);
lean_inc(v_macroStack_1767_);
lean_inc(v_cmdPos_1766_);
lean_inc(v_currRecDepth_1765_);
lean_inc_ref(v_fileMap_1764_);
lean_inc_ref(v_fileName_1763_);
v___x_1776_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1776_, 0, v_fileName_1763_);
lean_ctor_set(v___x_1776_, 1, v_fileMap_1764_);
lean_ctor_set(v___x_1776_, 2, v_currRecDepth_1765_);
lean_ctor_set(v___x_1776_, 3, v_cmdPos_1766_);
lean_ctor_set(v___x_1776_, 4, v_macroStack_1767_);
lean_ctor_set(v___x_1776_, 5, v_quotContext_x3f_1768_);
lean_ctor_set(v___x_1776_, 6, v_currMacroScope_1769_);
lean_ctor_set(v___x_1776_, 7, v_ref_1770_);
lean_ctor_set(v___x_1776_, 8, v___x_1775_);
lean_ctor_set(v___x_1776_, 9, v_cancelTk_x3f_1771_);
lean_ctor_set_uint8(v___x_1776_, sizeof(void*)*10, v_suppressElabErrors_1772_);
v___x_1777_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1759_, v___x_1774_, v___x_1776_, v_a_1761_);
lean_dec_ref_known(v___x_1776_, 10);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1823_; 
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v___x_1777_, 0);
lean_dec(v_unused_1824_);
v___x_1779_ = v___x_1777_;
v_isShared_1780_ = v_isSharedCheck_1823_;
goto v_resetjp_1778_;
}
else
{
lean_dec(v___x_1777_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1823_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v_messages_1783_; lean_object* v___y_1785_; lean_object* v_snapshotTasks_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1781_ = lean_st_ref_get(v_a_1761_);
v___x_1782_ = lean_st_ref_get(v_a_1761_);
v_messages_1783_ = lean_ctor_get(v___x_1781_, 1);
lean_inc_ref(v_messages_1783_);
lean_dec(v___x_1781_);
v_snapshotTasks_1812_ = lean_ctor_get(v___x_1782_, 10);
lean_inc_ref(v_snapshotTasks_1812_);
lean_dec(v___x_1782_);
v___x_1813_ = l_Lean_MessageLog_empty;
v___x_1814_ = lean_array_get_size(v_snapshotTasks_1812_);
v___x_1815_ = lean_nat_dec_lt(v___x_1773_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_dec_ref(v_snapshotTasks_1812_);
v___y_1785_ = v___x_1813_;
goto v___jp_1784_;
}
else
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_nat_dec_le(v___x_1814_, v___x_1814_);
if (v___x_1816_ == 0)
{
if (v___x_1815_ == 0)
{
lean_dec_ref(v_snapshotTasks_1812_);
v___y_1785_ = v___x_1813_;
goto v___jp_1784_;
}
else
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = lean_usize_of_nat(v___x_1814_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1812_, v___x_1817_, v___x_1818_, v___x_1813_);
lean_dec_ref(v_snapshotTasks_1812_);
v___y_1785_ = v___x_1819_;
goto v___jp_1784_;
}
}
else
{
size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = lean_usize_of_nat(v___x_1814_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1812_, v___x_1820_, v___x_1821_, v___x_1813_);
lean_dec_ref(v_snapshotTasks_1812_);
v___y_1785_ = v___x_1822_;
goto v___jp_1784_;
}
}
v___jp_1784_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v_env_1788_; lean_object* v_messages_1789_; lean_object* v_scopes_1790_; lean_object* v_usedQuotCtxts_1791_; lean_object* v_nextMacroScope_1792_; lean_object* v_maxRecDepth_1793_; lean_object* v_ngen_1794_; lean_object* v_auxDeclNGen_1795_; lean_object* v_infoState_1796_; lean_object* v_traceState_1797_; lean_object* v_prevLinterStates_1798_; lean_object* v_codeQualityEntryTasks_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1810_; 
v___x_1786_ = l_Lean_MessageLog_append(v_messages_1783_, v___y_1785_);
v___x_1787_ = lean_st_ref_take(v_a_1761_);
v_env_1788_ = lean_ctor_get(v___x_1787_, 0);
v_messages_1789_ = lean_ctor_get(v___x_1787_, 1);
v_scopes_1790_ = lean_ctor_get(v___x_1787_, 2);
v_usedQuotCtxts_1791_ = lean_ctor_get(v___x_1787_, 3);
v_nextMacroScope_1792_ = lean_ctor_get(v___x_1787_, 4);
v_maxRecDepth_1793_ = lean_ctor_get(v___x_1787_, 5);
v_ngen_1794_ = lean_ctor_get(v___x_1787_, 6);
v_auxDeclNGen_1795_ = lean_ctor_get(v___x_1787_, 7);
v_infoState_1796_ = lean_ctor_get(v___x_1787_, 8);
v_traceState_1797_ = lean_ctor_get(v___x_1787_, 9);
v_prevLinterStates_1798_ = lean_ctor_get(v___x_1787_, 11);
v_codeQualityEntryTasks_1799_ = lean_ctor_get(v___x_1787_, 12);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; 
v_unused_1811_ = lean_ctor_get(v___x_1787_, 10);
lean_dec(v_unused_1811_);
v___x_1801_ = v___x_1787_;
v_isShared_1802_ = v_isSharedCheck_1810_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1799_);
lean_inc(v_prevLinterStates_1798_);
lean_inc(v_traceState_1797_);
lean_inc(v_infoState_1796_);
lean_inc(v_auxDeclNGen_1795_);
lean_inc(v_ngen_1794_);
lean_inc(v_maxRecDepth_1793_);
lean_inc(v_nextMacroScope_1792_);
lean_inc(v_usedQuotCtxts_1791_);
lean_inc(v_scopes_1790_);
lean_inc(v_messages_1789_);
lean_inc(v_env_1788_);
lean_dec(v___x_1787_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1810_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 10, v___x_1774_);
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_env_1788_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_messages_1789_);
lean_ctor_set(v_reuseFailAlloc_1809_, 2, v_scopes_1790_);
lean_ctor_set(v_reuseFailAlloc_1809_, 3, v_usedQuotCtxts_1791_);
lean_ctor_set(v_reuseFailAlloc_1809_, 4, v_nextMacroScope_1792_);
lean_ctor_set(v_reuseFailAlloc_1809_, 5, v_maxRecDepth_1793_);
lean_ctor_set(v_reuseFailAlloc_1809_, 6, v_ngen_1794_);
lean_ctor_set(v_reuseFailAlloc_1809_, 7, v_auxDeclNGen_1795_);
lean_ctor_set(v_reuseFailAlloc_1809_, 8, v_infoState_1796_);
lean_ctor_set(v_reuseFailAlloc_1809_, 9, v_traceState_1797_);
lean_ctor_set(v_reuseFailAlloc_1809_, 10, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1809_, 11, v_prevLinterStates_1798_);
lean_ctor_set(v_reuseFailAlloc_1809_, 12, v_codeQualityEntryTasks_1799_);
v___x_1804_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1805_ = lean_st_ref_put(v_a_1761_, v___x_1804_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1786_);
v___x_1807_ = v___x_1779_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1786_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1777_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1777_);
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
lean_dec_ref_known(v___x_1843_, 1);
if (lean_obj_tag(v_val_1845_) == 1)
{
uint8_t v_v_1846_; 
v_v_1846_ = lean_ctor_get_uint8(v_val_1845_, 0);
lean_dec_ref_known(v_val_1845_, 0);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg(){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___closed__0));
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___boxed(lean_object* v___dummy_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v_res_1857_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1861_);
lean_dec_ref(v_s_1861_);
return v_res_1862_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_box(1);
v___x_1864_ = l_Lean_MessageData_ofFormat(v___x_1863_);
return v___x_1864_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1869_ = l_Lean_MessageData_ofFormat(v___x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1870_, lean_object* v_x_1871_){
_start:
{
if (lean_obj_tag(v_x_1871_) == 0)
{
return v_x_1870_;
}
else
{
lean_object* v_head_1872_; lean_object* v_tail_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1895_; 
v_head_1872_ = lean_ctor_get(v_x_1871_, 0);
v_tail_1873_ = lean_ctor_get(v_x_1871_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_x_1871_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1875_ = v_x_1871_;
v_isShared_1876_ = v_isSharedCheck_1895_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_tail_1873_);
lean_inc(v_head_1872_);
lean_dec(v_x_1871_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1895_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_before_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1893_; 
v_before_1877_ = lean_ctor_get(v_head_1872_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_head_1872_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v_head_1872_, 1);
lean_dec(v_unused_1894_);
v___x_1879_ = v_head_1872_;
v_isShared_1880_ = v_isSharedCheck_1893_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_before_1877_);
lean_dec(v_head_1872_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1893_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1881_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 7);
lean_ctor_set(v___x_1879_, 1, v___x_1881_);
lean_ctor_set(v___x_1879_, 0, v_x_1870_);
v___x_1883_ = v___x_1879_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_x_1870_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1884_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1876_ == 0)
{
lean_ctor_set_tag(v___x_1875_, 7);
lean_ctor_set(v___x_1875_, 1, v___x_1884_);
lean_ctor_set(v___x_1875_, 0, v___x_1883_);
v___x_1886_ = v___x_1875_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = l_Lean_MessageData_ofSyntax(v_before_1877_);
v___x_1888_ = l_Lean_indentD(v___x_1887_);
v___x_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1886_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v_x_1870_ = v___x_1889_;
v_x_1871_ = v_tail_1873_;
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
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1900_ = l_Lean_MessageData_ofFormat(v___x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1901_, lean_object* v_macroStack_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_scopes_1907_; lean_object* v___x_1908_; lean_object* v_opts_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1905_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1906_ = lean_st_ref_get(v___y_1903_);
v_scopes_1907_ = lean_ctor_get(v___x_1906_, 2);
lean_inc(v_scopes_1907_);
lean_dec(v___x_1906_);
v___x_1908_ = l_List_head_x21___redArg(v___x_1905_, v_scopes_1907_);
lean_dec(v_scopes_1907_);
v_opts_1909_ = lean_ctor_get(v___x_1908_, 1);
lean_inc_ref(v_opts_1909_);
lean_dec(v___x_1908_);
v___x_1910_ = l_Lean_Elab_pp_macroStack;
v___x_1911_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1909_, v___x_1910_);
lean_dec_ref(v_opts_1909_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; 
lean_dec(v_macroStack_1902_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_msgData_1901_);
return v___x_1912_;
}
else
{
if (lean_obj_tag(v_macroStack_1902_) == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_msgData_1901_);
return v___x_1913_;
}
else
{
lean_object* v_head_1914_; lean_object* v_after_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1930_; 
v_head_1914_ = lean_ctor_get(v_macroStack_1902_, 0);
lean_inc(v_head_1914_);
v_after_1915_ = lean_ctor_get(v_head_1914_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_head_1914_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v_head_1914_, 0);
lean_dec(v_unused_1931_);
v___x_1917_ = v_head_1914_;
v_isShared_1918_ = v_isSharedCheck_1930_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_after_1915_);
lean_dec(v_head_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1930_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1919_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 7);
lean_ctor_set(v___x_1917_, 1, v___x_1919_);
lean_ctor_set(v___x_1917_, 0, v_msgData_1901_);
v___x_1921_ = v___x_1917_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_msgData_1901_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_msgData_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1922_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l_Lean_MessageData_ofSyntax(v_after_1915_);
v___x_1925_ = l_Lean_indentD(v___x_1924_);
v_msgData_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1926_, 0, v___x_1923_);
lean_ctor_set(v_msgData_1926_, 1, v___x_1925_);
v___x_1927_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1926_, v_macroStack_1902_);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1932_, lean_object* v_macroStack_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1932_, v_macroStack_1933_, v___y_1934_);
lean_dec(v___y_1934_);
return v_res_1936_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
lean_ctor_set(v___x_1942_, 2, v___x_1941_);
lean_ctor_set(v___x_1942_, 3, v___x_1941_);
lean_ctor_set(v___x_1942_, 4, v___x_1940_);
lean_ctor_set(v___x_1942_, 5, v___x_1940_);
lean_ctor_set(v___x_1942_, 6, v___x_1940_);
lean_ctor_set(v___x_1942_, 7, v___x_1940_);
lean_ctor_set(v___x_1942_, 8, v___x_1940_);
lean_ctor_set(v___x_1942_, 9, v___x_1940_);
lean_ctor_set(v___x_1942_, 10, v___x_1940_);
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = lean_unsigned_to_nat(32u);
v___x_1944_ = lean_mk_empty_array_with_capacity(v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1946_ = ((size_t)5ULL);
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = lean_unsigned_to_nat(32u);
v___x_1949_ = lean_mk_empty_array_with_capacity(v___x_1948_);
v___x_1950_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1951_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v___x_1949_);
lean_ctor_set(v___x_1951_, 2, v___x_1947_);
lean_ctor_set(v___x_1951_, 3, v___x_1947_);
lean_ctor_set_usize(v___x_1951_, 4, v___x_1946_);
return v___x_1951_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1952_ = lean_box(1);
v___x_1953_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1954_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1955_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v___x_1953_);
lean_ctor_set(v___x_1955_, 2, v___x_1952_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v___x_1959_; lean_object* v_env_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_scopes_1963_; lean_object* v___x_1964_; lean_object* v_opts_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1959_ = lean_st_ref_get(v___y_1957_);
v_env_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc_ref(v_env_1960_);
lean_dec(v___x_1959_);
v___x_1961_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1962_ = lean_st_ref_get(v___y_1957_);
v_scopes_1963_ = lean_ctor_get(v___x_1962_, 2);
lean_inc(v_scopes_1963_);
lean_dec(v___x_1962_);
v___x_1964_ = l_List_head_x21___redArg(v___x_1961_, v_scopes_1963_);
lean_dec(v_scopes_1963_);
v_opts_1965_ = lean_ctor_get(v___x_1964_, 1);
lean_inc_ref(v_opts_1965_);
lean_dec(v___x_1964_);
v___x_1966_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1967_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1968_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1968_, 0, v_env_1960_);
lean_ctor_set(v___x_1968_, 1, v___x_1966_);
lean_ctor_set(v___x_1968_, 2, v___x_1967_);
lean_ctor_set(v___x_1968_, 3, v_opts_1965_);
v___x_1969_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
lean_ctor_set(v___x_1969_, 1, v_msgData_1956_);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1971_, v___y_1972_);
lean_dec(v___y_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_Elab_Command_getRef___redArg(v___y_1976_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v_macroStack_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_a_1984_; lean_object* v___x_1985_; lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1994_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v_macroStack_1981_ = lean_ctor_get(v___y_1976_, 4);
v___x_1982_ = l_Lean_Elab_getBetterRef(v_a_1980_, v_macroStack_1981_);
lean_dec(v_a_1980_);
v___x_1983_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1975_, v___y_1977_);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref(v___x_1983_);
lean_inc(v_macroStack_1981_);
v___x_1985_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1984_, v_macroStack_1981_, v___y_1977_);
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1982_);
lean_ctor_set(v___x_1990_, 1, v_a_1986_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set_tag(v___x_1988_, 1);
lean_ctor_set(v___x_1988_, 0, v___x_1990_);
v___x_1992_ = v___x_1988_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v_msg_1975_);
v_a_1995_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1979_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1979_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_2008_, lean_object* v_msg_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_Elab_Command_getRef___redArg(v___y_2010_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v_fileName_2015_; lean_object* v_fileMap_2016_; lean_object* v_currRecDepth_2017_; lean_object* v_cmdPos_2018_; lean_object* v_macroStack_2019_; lean_object* v_quotContext_x3f_2020_; lean_object* v_currMacroScope_2021_; lean_object* v_snap_x3f_2022_; lean_object* v_cancelTk_x3f_2023_; uint8_t v_suppressElabErrors_2024_; lean_object* v_ref_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v_fileName_2015_ = lean_ctor_get(v___y_2010_, 0);
v_fileMap_2016_ = lean_ctor_get(v___y_2010_, 1);
v_currRecDepth_2017_ = lean_ctor_get(v___y_2010_, 2);
v_cmdPos_2018_ = lean_ctor_get(v___y_2010_, 3);
v_macroStack_2019_ = lean_ctor_get(v___y_2010_, 4);
v_quotContext_x3f_2020_ = lean_ctor_get(v___y_2010_, 5);
v_currMacroScope_2021_ = lean_ctor_get(v___y_2010_, 6);
v_snap_x3f_2022_ = lean_ctor_get(v___y_2010_, 8);
v_cancelTk_x3f_2023_ = lean_ctor_get(v___y_2010_, 9);
v_suppressElabErrors_2024_ = lean_ctor_get_uint8(v___y_2010_, sizeof(void*)*10);
v_ref_2025_ = l_Lean_replaceRef(v_ref_2008_, v_a_2014_);
lean_dec(v_a_2014_);
lean_inc(v_cancelTk_x3f_2023_);
lean_inc(v_snap_x3f_2022_);
lean_inc(v_currMacroScope_2021_);
lean_inc(v_quotContext_x3f_2020_);
lean_inc(v_macroStack_2019_);
lean_inc(v_cmdPos_2018_);
lean_inc(v_currRecDepth_2017_);
lean_inc_ref(v_fileMap_2016_);
lean_inc_ref(v_fileName_2015_);
v___x_2026_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2026_, 0, v_fileName_2015_);
lean_ctor_set(v___x_2026_, 1, v_fileMap_2016_);
lean_ctor_set(v___x_2026_, 2, v_currRecDepth_2017_);
lean_ctor_set(v___x_2026_, 3, v_cmdPos_2018_);
lean_ctor_set(v___x_2026_, 4, v_macroStack_2019_);
lean_ctor_set(v___x_2026_, 5, v_quotContext_x3f_2020_);
lean_ctor_set(v___x_2026_, 6, v_currMacroScope_2021_);
lean_ctor_set(v___x_2026_, 7, v_ref_2025_);
lean_ctor_set(v___x_2026_, 8, v_snap_x3f_2022_);
lean_ctor_set(v___x_2026_, 9, v_cancelTk_x3f_2023_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*10, v_suppressElabErrors_2024_);
v___x_2027_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_2009_, v___x_2026_, v___y_2011_);
lean_dec_ref_known(v___x_2026_, 10);
return v___x_2027_;
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec_ref(v_msg_2009_);
v_a_2028_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2013_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2013_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_2036_, lean_object* v_msg_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_2036_, v_msg_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v_ref_2036_);
return v_res_2041_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_2044_ = l_Lean_stringToMessageData(v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_val_2059_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = lean_unsigned_to_nat(1u);
v___x_2067_ = l_Lean_Syntax_getArg(v_stx_2048_, v___x_2066_);
switch(lean_obj_tag(v___x_2067_))
{
case 2:
{
lean_object* v_val_2068_; 
lean_dec(v_stx_2048_);
v_val_2068_ = lean_ctor_get(v___x_2067_, 1);
lean_inc_ref(v_val_2068_);
lean_dec_ref_known(v___x_2067_, 2);
v_val_2059_ = v_val_2068_;
goto v___jp_2058_;
}
case 1:
{
lean_object* v_kind_2069_; 
v_kind_2069_ = lean_ctor_get(v___x_2067_, 1);
lean_inc(v_kind_2069_);
if (lean_obj_tag(v_kind_2069_) == 1)
{
lean_object* v_pre_2070_; 
v_pre_2070_ = lean_ctor_get(v_kind_2069_, 0);
lean_inc(v_pre_2070_);
if (lean_obj_tag(v_pre_2070_) == 1)
{
lean_object* v_pre_2071_; 
v_pre_2071_ = lean_ctor_get(v_pre_2070_, 0);
lean_inc(v_pre_2071_);
if (lean_obj_tag(v_pre_2071_) == 1)
{
lean_object* v_pre_2072_; 
v_pre_2072_ = lean_ctor_get(v_pre_2071_, 0);
lean_inc(v_pre_2072_);
if (lean_obj_tag(v_pre_2072_) == 1)
{
lean_object* v_pre_2073_; 
v_pre_2073_ = lean_ctor_get(v_pre_2072_, 0);
if (lean_obj_tag(v_pre_2073_) == 0)
{
lean_object* v_str_2074_; lean_object* v_str_2075_; lean_object* v_str_2076_; lean_object* v_str_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v_str_2074_ = lean_ctor_get(v_kind_2069_, 1);
lean_inc_ref(v_str_2074_);
lean_dec_ref_known(v_kind_2069_, 2);
v_str_2075_ = lean_ctor_get(v_pre_2070_, 1);
lean_inc_ref(v_str_2075_);
lean_dec_ref_known(v_pre_2070_, 2);
v_str_2076_ = lean_ctor_get(v_pre_2071_, 1);
lean_inc_ref(v_str_2076_);
lean_dec_ref_known(v_pre_2071_, 2);
v_str_2077_ = lean_ctor_get(v_pre_2072_, 1);
lean_inc_ref(v_str_2077_);
lean_dec_ref_known(v_pre_2072_, 2);
v___x_2078_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_2079_ = lean_string_dec_eq(v_str_2077_, v___x_2078_);
lean_dec_ref(v_str_2077_);
if (v___x_2079_ == 0)
{
lean_dec_ref(v_str_2076_);
lean_dec_ref(v_str_2075_);
lean_dec_ref(v_str_2074_);
lean_dec_ref_known(v___x_2067_, 3);
goto v___jp_2052_;
}
else
{
lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2081_ = lean_string_dec_eq(v_str_2076_, v___x_2080_);
lean_dec_ref(v_str_2076_);
if (v___x_2081_ == 0)
{
lean_dec_ref(v_str_2075_);
lean_dec_ref(v_str_2074_);
lean_dec_ref_known(v___x_2067_, 3);
goto v___jp_2052_;
}
else
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2083_ = lean_string_dec_eq(v_str_2075_, v___x_2082_);
lean_dec_ref(v_str_2075_);
if (v___x_2083_ == 0)
{
lean_dec_ref(v_str_2074_);
lean_dec_ref_known(v___x_2067_, 3);
goto v___jp_2052_;
}
else
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2084_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2085_ = lean_string_dec_eq(v_str_2074_, v___x_2084_);
lean_dec_ref(v_str_2074_);
if (v___x_2085_ == 0)
{
lean_dec_ref_known(v___x_2067_, 3);
goto v___jp_2052_;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = l_Lean_Syntax_getArg(v___x_2067_, v___x_2086_);
lean_dec_ref_known(v___x_2067_, 3);
if (lean_obj_tag(v___x_2087_) == 2)
{
lean_object* v_val_2088_; 
lean_dec(v_stx_2048_);
v_val_2088_ = lean_ctor_get(v___x_2087_, 1);
lean_inc_ref(v_val_2088_);
lean_dec_ref_known(v___x_2087_, 2);
v_val_2059_ = v_val_2088_;
goto v___jp_2058_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec(v___x_2087_);
v___x_2089_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2048_);
v___x_2090_ = l_Lean_MessageData_ofSyntax(v_stx_2048_);
v___x_2091_ = l_Lean_indentD(v___x_2090_);
v___x_2092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2089_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2048_, v___x_2092_, v___y_2049_, v___y_2050_);
lean_dec(v_stx_2048_);
return v___x_2093_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2072_, 2);
lean_dec_ref_known(v_pre_2071_, 2);
lean_dec_ref_known(v_pre_2070_, 2);
lean_dec_ref_known(v_kind_2069_, 2);
lean_dec_ref_known(v___x_2067_, 3);
goto v___jp_2052_;
}
}
else
{
lean_dec_ref_known(v_pre_2071_, 2);
lean_dec(v_pre_2072_);
lean_dec_ref_known(v_pre_2070_, 2);
lean_dec_ref_known(v_kind_2069_, 2);
lean_dec_ref_known(v___x_2067_, 3);
goto v___jp_2052_;
}
}
else
{
lean_dec(v_pre_2071_);
lean_dec_ref_known(v_pre_2070_, 2);
lean_dec_ref_known(v_kind_2069_, 2);
lean_dec_ref_known(v___x_2067_, 3);
goto v___jp_2052_;
}
}
else
{
lean_dec_ref_known(v_kind_2069_, 2);
lean_dec(v_pre_2070_);
lean_dec_ref_known(v___x_2067_, 3);
goto v___jp_2052_;
}
}
else
{
lean_dec_ref_known(v___x_2067_, 3);
lean_dec(v_kind_2069_);
goto v___jp_2052_;
}
}
default: 
{
lean_dec(v___x_2067_);
goto v___jp_2052_;
}
}
v___jp_2052_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2053_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2048_);
v___x_2054_ = l_Lean_MessageData_ofSyntax(v_stx_2048_);
v___x_2055_ = l_Lean_indentD(v___x_2054_);
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2053_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2048_, v___x_2056_, v___y_2049_, v___y_2050_);
lean_dec(v_stx_2048_);
return v___x_2057_;
}
v___jp_2058_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = lean_string_utf8_byte_size(v_val_2059_);
v___x_2062_ = lean_unsigned_to_nat(2u);
v___x_2063_ = lean_nat_sub(v___x_2061_, v___x_2062_);
v___x_2064_ = lean_string_utf8_extract(v_val_2059_, v___x_2060_, v___x_2063_);
lean_dec(v___x_2063_);
lean_dec_ref(v_val_2059_);
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
return v___x_2065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2099_, size_t v_sz_2100_, size_t v_i_2101_, lean_object* v_b_2102_){
_start:
{
lean_object* v_a_2104_; uint8_t v___x_2108_; 
v___x_2108_ = lean_usize_dec_lt(v_i_2101_, v_sz_2100_);
if (v___x_2108_ == 0)
{
return v_b_2102_;
}
else
{
lean_object* v_a_2109_; lean_object* v_fst_2110_; lean_object* v_snd_2111_; lean_object* v_out_2112_; uint8_t v___x_2113_; 
v_a_2109_ = lean_array_uget_borrowed(v_as_2099_, v_i_2101_);
v_fst_2110_ = lean_ctor_get(v_a_2109_, 0);
v_snd_2111_ = lean_ctor_get(v_a_2109_, 1);
v_out_2112_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2113_ = lean_string_dec_eq(v_snd_2111_, v_out_2112_);
if (v___x_2113_ == 0)
{
uint8_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2114_ = lean_unbox(v_fst_2110_);
v___x_2115_ = l_Lean_Diff_Action_linePrefix(v___x_2114_);
v___x_2116_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2117_ = lean_string_append(v___x_2115_, v___x_2116_);
v___x_2118_ = lean_string_append(v___x_2117_, v_snd_2111_);
v___x_2119_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2120_ = lean_string_append(v___x_2118_, v___x_2119_);
v___x_2121_ = lean_string_append(v_b_2102_, v___x_2120_);
lean_dec_ref(v___x_2120_);
v_a_2104_ = v___x_2121_;
goto v___jp_2103_;
}
else
{
uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2122_ = lean_unbox(v_fst_2110_);
v___x_2123_ = l_Lean_Diff_Action_linePrefix(v___x_2122_);
v___x_2124_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2125_ = lean_string_append(v___x_2123_, v___x_2124_);
v___x_2126_ = lean_string_append(v_b_2102_, v___x_2125_);
lean_dec_ref(v___x_2125_);
v_a_2104_ = v___x_2126_;
goto v___jp_2103_;
}
}
v___jp_2103_:
{
size_t v___x_2105_; size_t v___x_2106_; 
v___x_2105_ = ((size_t)1ULL);
v___x_2106_ = lean_usize_add(v_i_2101_, v___x_2105_);
v_i_2101_ = v___x_2106_;
v_b_2102_ = v_a_2104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2127_, lean_object* v_sz_2128_, lean_object* v_i_2129_, lean_object* v_b_2130_){
_start:
{
size_t v_sz_boxed_2131_; size_t v_i_boxed_2132_; lean_object* v_res_2133_; 
v_sz_boxed_2131_ = lean_unbox_usize(v_sz_2128_);
lean_dec(v_sz_2128_);
v_i_boxed_2132_ = lean_unbox_usize(v_i_2129_);
lean_dec(v_i_2129_);
v_res_2133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2127_, v_sz_boxed_2131_, v_i_boxed_2132_, v_b_2130_);
lean_dec_ref(v_as_2127_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2134_){
_start:
{
lean_object* v_out_2135_; size_t v_sz_2136_; size_t v___x_2137_; lean_object* v___x_2138_; 
v_out_2135_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v_sz_2136_ = lean_array_size(v_lines_2134_);
v___x_2137_ = ((size_t)0ULL);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2134_, v_sz_2136_, v___x_2137_, v_out_2135_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2139_);
lean_dec_ref(v_lines_2139_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2141_, lean_object* v_as_x27_2142_, lean_object* v_b_2143_){
_start:
{
if (lean_obj_tag(v_as_x27_2142_) == 0)
{
lean_object* v___x_2145_; 
lean_dec_ref(v_filterFn_2141_);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v_b_2143_);
return v___x_2145_;
}
else
{
lean_object* v_head_2146_; uint8_t v_isSilent_2147_; 
v_head_2146_ = lean_ctor_get(v_as_x27_2142_, 0);
v_isSilent_2147_ = lean_ctor_get_uint8(v_head_2146_, sizeof(void*)*5 + 2);
if (v_isSilent_2147_ == 0)
{
lean_object* v_tail_2148_; lean_object* v_fst_2149_; lean_object* v_snd_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2170_; 
v_tail_2148_ = lean_ctor_get(v_as_x27_2142_, 1);
v_fst_2149_ = lean_ctor_get(v_b_2143_, 0);
v_snd_2150_ = lean_ctor_get(v_b_2143_, 1);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_b_2143_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2152_ = v_b_2143_;
v_isShared_2153_ = v_isSharedCheck_2170_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_snd_2150_);
lean_inc(v_fst_2149_);
lean_dec(v_b_2143_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2170_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
lean_inc_ref(v_filterFn_2141_);
lean_inc(v_head_2146_);
v___x_2154_ = lean_apply_1(v_filterFn_2141_, v_head_2146_);
v___x_2155_ = lean_unbox(v___x_2154_);
switch(v___x_2155_)
{
case 0:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
lean_inc(v_head_2146_);
v___x_2156_ = l_Lean_MessageLog_add(v_head_2146_, v_fst_2149_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2156_);
v___x_2158_ = v___x_2152_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_snd_2150_);
v___x_2158_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
v_as_x27_2142_ = v_tail_2148_;
v_b_2143_ = v___x_2158_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2162_; 
if (v_isShared_2153_ == 0)
{
v___x_2162_ = v___x_2152_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_fst_2149_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_snd_2150_);
v___x_2162_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
v_as_x27_2142_ = v_tail_2148_;
v_b_2143_ = v___x_2162_;
goto _start;
}
}
default: 
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_inc(v_head_2146_);
v___x_2165_ = l_Lean_MessageLog_add(v_head_2146_, v_snd_2150_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v___x_2165_);
v___x_2167_ = v___x_2152_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_fst_2149_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
v_as_x27_2142_ = v_tail_2148_;
v_b_2143_ = v___x_2167_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2171_; lean_object* v_fst_2172_; lean_object* v_snd_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2181_; 
v_tail_2171_ = lean_ctor_get(v_as_x27_2142_, 1);
v_fst_2172_ = lean_ctor_get(v_b_2143_, 0);
v_snd_2173_ = lean_ctor_get(v_b_2143_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_b_2143_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2175_ = v_b_2143_;
v_isShared_2176_ = v_isSharedCheck_2181_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_snd_2173_);
lean_inc(v_fst_2172_);
lean_dec(v_b_2143_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2181_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_fst_2172_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_snd_2173_);
v___x_2178_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
v_as_x27_2142_ = v_tail_2171_;
v_b_2143_ = v___x_2178_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2182_, lean_object* v_as_x27_2183_, lean_object* v_b_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2182_, v_as_x27_2183_, v_b_2184_);
lean_dec(v_as_x27_2183_);
return v_res_2186_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2187_, lean_object* v_a_2188_, uint8_t v_b_2189_){
_start:
{
uint8_t v___x_2190_; 
v___x_2190_ = 0;
switch(lean_obj_tag(v_a_2188_))
{
case 0:
{
lean_object* v_pos_2191_; lean_object* v_startInclusive_2192_; lean_object* v_endExclusive_2193_; lean_object* v___x_2194_; uint8_t v_decide_2195_; 
v_pos_2191_ = lean_ctor_get(v_a_2188_, 0);
lean_inc(v_pos_2191_);
lean_dec_ref_known(v_a_2188_, 1);
v_startInclusive_2192_ = lean_ctor_get(v_s_2187_, 1);
v_endExclusive_2193_ = lean_ctor_get(v_s_2187_, 2);
v___x_2194_ = lean_nat_sub(v_endExclusive_2193_, v_startInclusive_2192_);
v_decide_2195_ = lean_nat_dec_eq(v_pos_2191_, v___x_2194_);
lean_dec(v___x_2194_);
lean_dec(v_pos_2191_);
if (v_decide_2195_ == 0)
{
uint8_t v___x_2196_; 
v___x_2196_ = 1;
return v___x_2196_;
}
else
{
return v_decide_2195_;
}
}
case 1:
{
lean_object* v_pos_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2210_; 
v_pos_2197_ = lean_ctor_get(v_a_2188_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_a_2188_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2199_ = v_a_2188_;
v_isShared_2200_ = v_isSharedCheck_2210_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_pos_2197_);
lean_dec(v_a_2188_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2210_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v_str_2201_; lean_object* v_startInclusive_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v_str_2201_ = lean_ctor_get(v_s_2187_, 0);
v_startInclusive_2202_ = lean_ctor_get(v_s_2187_, 1);
v___x_2203_ = lean_nat_add(v_startInclusive_2202_, v_pos_2197_);
lean_dec(v_pos_2197_);
v___x_2204_ = lean_string_utf8_next_fast(v_str_2201_, v___x_2203_);
lean_dec(v___x_2203_);
v___x_2205_ = lean_nat_sub(v___x_2204_, v_startInclusive_2202_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set_tag(v___x_2199_, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2205_);
v___x_2207_ = v___x_2199_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
v_a_2188_ = v___x_2207_;
v_b_2189_ = v___x_2190_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2211_; lean_object* v_table_2212_; lean_object* v_stackPos_2213_; lean_object* v_needlePos_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2269_; 
v_needle_2211_ = lean_ctor_get(v_a_2188_, 0);
v_table_2212_ = lean_ctor_get(v_a_2188_, 1);
v_stackPos_2213_ = lean_ctor_get(v_a_2188_, 2);
v_needlePos_2214_ = lean_ctor_get(v_a_2188_, 3);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_a_2188_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2216_ = v_a_2188_;
v_isShared_2217_ = v_isSharedCheck_2269_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_needlePos_2214_);
lean_inc(v_stackPos_2213_);
lean_inc(v_table_2212_);
lean_inc(v_needle_2211_);
lean_dec(v_a_2188_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2269_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v_str_2218_; lean_object* v_startInclusive_2219_; lean_object* v_endExclusive_2220_; lean_object* v_str_2221_; lean_object* v_startInclusive_2222_; lean_object* v_endExclusive_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v_str_2218_ = lean_ctor_get(v_needle_2211_, 0);
v_startInclusive_2219_ = lean_ctor_get(v_needle_2211_, 1);
v_endExclusive_2220_ = lean_ctor_get(v_needle_2211_, 2);
v_str_2221_ = lean_ctor_get(v_s_2187_, 0);
v_startInclusive_2222_ = lean_ctor_get(v_s_2187_, 1);
v_endExclusive_2223_ = lean_ctor_get(v_s_2187_, 2);
v___x_2224_ = lean_nat_sub(v_stackPos_2213_, v_needlePos_2214_);
v___x_2225_ = lean_nat_sub(v_endExclusive_2220_, v_startInclusive_2219_);
v___x_2226_ = lean_nat_add(v___x_2224_, v___x_2225_);
v___x_2227_ = lean_nat_sub(v_endExclusive_2223_, v_startInclusive_2222_);
v___x_2228_ = lean_nat_dec_le(v___x_2226_, v___x_2227_);
lean_dec(v___x_2226_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
lean_dec(v___x_2225_);
lean_del_object(v___x_2216_);
lean_dec(v_needlePos_2214_);
lean_dec(v_stackPos_2213_);
lean_dec_ref(v_table_2212_);
lean_dec_ref(v_needle_2211_);
v___x_2229_ = lean_unsigned_to_nat(1u);
v___x_2230_ = lean_nat_add(v___x_2224_, v___x_2229_);
lean_dec(v___x_2224_);
v___x_2231_ = lean_nat_dec_le(v___x_2230_, v___x_2227_);
lean_dec(v___x_2227_);
lean_dec(v___x_2230_);
if (v___x_2231_ == 0)
{
return v_b_2189_;
}
else
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_box(3);
v_a_2188_ = v___x_2232_;
v_b_2189_ = v___x_2190_;
goto _start;
}
}
else
{
lean_object* v___x_2234_; uint8_t v_stackByte_2235_; lean_object* v___x_2236_; uint8_t v_patByte_2237_; uint8_t v___x_2238_; 
lean_dec(v___x_2227_);
lean_dec(v___x_2224_);
v___x_2234_ = lean_nat_add(v_startInclusive_2222_, v_stackPos_2213_);
v_stackByte_2235_ = lean_string_get_byte_fast(v_str_2221_, v___x_2234_);
v___x_2236_ = lean_nat_add(v_startInclusive_2219_, v_needlePos_2214_);
v_patByte_2237_ = lean_string_get_byte_fast(v_str_2218_, v___x_2236_);
v___x_2238_ = lean_uint8_dec_eq(v_stackByte_2235_, v_patByte_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; uint8_t v_decide_2240_; 
lean_dec(v___x_2225_);
v___x_2239_ = lean_unsigned_to_nat(0u);
v_decide_2240_ = lean_nat_dec_eq(v_needlePos_2214_, v___x_2239_);
if (v_decide_2240_ == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v_newNeedlePos_2243_; uint8_t v___x_2244_; 
v___x_2241_ = lean_unsigned_to_nat(1u);
v___x_2242_ = lean_nat_sub(v_needlePos_2214_, v___x_2241_);
lean_dec(v_needlePos_2214_);
v_newNeedlePos_2243_ = lean_array_fget_borrowed(v_table_2212_, v___x_2242_);
lean_dec(v___x_2242_);
v___x_2244_ = lean_nat_dec_eq(v_newNeedlePos_2243_, v___x_2239_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2246_; 
lean_inc(v_newNeedlePos_2243_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 3, v_newNeedlePos_2243_);
v___x_2246_ = v___x_2216_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_needle_2211_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_table_2212_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_stackPos_2213_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v_newNeedlePos_2243_);
v___x_2246_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
v_a_2188_ = v___x_2246_;
v_b_2189_ = v___x_2190_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2249_; lean_object* v___x_2251_; 
v_nextStackPos_2249_ = l_String_Slice_posGE___redArg(v_s_2187_, v_stackPos_2213_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 3, v___x_2239_);
lean_ctor_set(v___x_2216_, 2, v_nextStackPos_2249_);
v___x_2251_ = v___x_2216_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_needle_2211_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_table_2212_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_nextStackPos_2249_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v___x_2239_);
v___x_2251_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
v_a_2188_ = v___x_2251_;
v_b_2189_ = v___x_2190_;
goto _start;
}
}
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v_nextStackPos_2256_; lean_object* v___x_2258_; 
lean_dec(v_needlePos_2214_);
v___x_2254_ = lean_unsigned_to_nat(1u);
v___x_2255_ = lean_nat_add(v_stackPos_2213_, v___x_2254_);
lean_dec(v_stackPos_2213_);
v_nextStackPos_2256_ = l_String_Slice_posGE___redArg(v_s_2187_, v___x_2255_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 3, v___x_2239_);
lean_ctor_set(v___x_2216_, 2, v_nextStackPos_2256_);
v___x_2258_ = v___x_2216_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_needle_2211_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_table_2212_);
lean_ctor_set(v_reuseFailAlloc_2260_, 2, v_nextStackPos_2256_);
lean_ctor_set(v_reuseFailAlloc_2260_, 3, v___x_2239_);
v___x_2258_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
v_a_2188_ = v___x_2258_;
v_b_2189_ = v___x_2190_;
goto _start;
}
}
}
else
{
lean_object* v___x_2261_; lean_object* v_nextNeedlePos_2262_; uint8_t v_decide_2263_; 
v___x_2261_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2262_ = lean_nat_add(v_needlePos_2214_, v___x_2261_);
lean_dec(v_needlePos_2214_);
v_decide_2263_ = lean_nat_dec_eq(v_nextNeedlePos_2262_, v___x_2225_);
lean_dec(v___x_2225_);
if (v_decide_2263_ == 0)
{
lean_object* v_nextStackPos_2264_; lean_object* v___x_2266_; 
v_nextStackPos_2264_ = lean_nat_add(v_stackPos_2213_, v___x_2261_);
lean_dec(v_stackPos_2213_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 3, v_nextNeedlePos_2262_);
lean_ctor_set(v___x_2216_, 2, v_nextStackPos_2264_);
v___x_2266_ = v___x_2216_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_needle_2211_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_table_2212_);
lean_ctor_set(v_reuseFailAlloc_2268_, 2, v_nextStackPos_2264_);
lean_ctor_set(v_reuseFailAlloc_2268_, 3, v_nextNeedlePos_2262_);
v___x_2266_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
v_a_2188_ = v___x_2266_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2262_);
lean_del_object(v___x_2216_);
lean_dec(v_stackPos_2213_);
lean_dec_ref(v_table_2212_);
lean_dec_ref(v_needle_2211_);
return v_decide_2263_;
}
}
}
}
}
default: 
{
return v_b_2189_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2270_, lean_object* v_a_2271_, lean_object* v_b_2272_){
_start:
{
uint8_t v_b_boxed_2273_; uint8_t v_res_2274_; lean_object* v_r_2275_; 
v_b_boxed_2273_ = lean_unbox(v_b_2272_);
v_res_2274_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2270_, v_a_2271_, v_b_boxed_2273_);
lean_dec_ref(v_s_2270_);
v_r_2275_ = lean_box(v_res_2274_);
return v_r_2275_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2276_, lean_object* v_s_2277_){
_start:
{
lean_object* v___y_2279_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = lean_string_utf8_byte_size(v___x_2276_);
v___x_2284_ = lean_nat_dec_eq(v___x_2283_, v___x_2282_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2276_);
lean_ctor_set(v___x_2285_, 1, v___x_2282_);
lean_ctor_set(v___x_2285_, 2, v___x_2283_);
v___x_2286_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2285_);
v___x_2287_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
lean_ctor_set(v___x_2287_, 2, v___x_2282_);
lean_ctor_set(v___x_2287_, 3, v___x_2282_);
v___y_2279_ = v___x_2287_;
goto v___jp_2278_;
}
else
{
lean_object* v___x_2288_; 
lean_dec_ref(v___x_2276_);
v___x_2288_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_2279_ = v___x_2288_;
goto v___jp_2278_;
}
v___jp_2278_:
{
uint8_t v___x_2280_; uint8_t v___x_2281_; 
v___x_2280_ = 0;
v___x_2281_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2277_, v___y_2279_, v___x_2280_);
return v___x_2281_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2289_, lean_object* v_s_2290_){
_start:
{
uint8_t v_res_2291_; lean_object* v_r_2292_; 
v_res_2291_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2289_, v_s_2290_);
lean_dec_ref(v_s_2290_);
v_r_2292_ = lean_box(v_res_2291_);
return v_r_2292_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v_suppressElabErrors_2293_, uint8_t v___y_2294_, lean_object* v_x_2295_){
_start:
{
if (lean_obj_tag(v_x_2295_) == 1)
{
lean_object* v_pre_2296_; 
v_pre_2296_ = lean_ctor_get(v_x_2295_, 0);
if (lean_obj_tag(v_pre_2296_) == 0)
{
lean_object* v_str_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v_str_2297_ = lean_ctor_get(v_x_2295_, 1);
v___x_2298_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2299_ = lean_string_dec_eq(v_str_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
return v___x_2299_;
}
else
{
return v_suppressElabErrors_2293_;
}
}
else
{
return v___y_2294_;
}
}
else
{
return v___y_2294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_2300_, lean_object* v___y_2301_, lean_object* v_x_2302_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2303_; uint8_t v___y_26126__boxed_2304_; uint8_t v_res_2305_; lean_object* v_r_2306_; 
v_suppressElabErrors_boxed_2303_ = lean_unbox(v_suppressElabErrors_2300_);
v___y_26126__boxed_2304_ = lean_unbox(v___y_2301_);
v_res_2305_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v_suppressElabErrors_boxed_2303_, v___y_26126__boxed_2304_, v_x_2302_);
lean_dec(v_x_2302_);
v_r_2306_ = lean_box(v_res_2305_);
return v_r_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2307_, lean_object* v_msgData_2308_, uint8_t v_severity_2309_, uint8_t v_isSilent_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; uint8_t v___y_2319_; lean_object* v___y_2320_; uint8_t v___y_2321_; lean_object* v___y_2322_; uint8_t v___y_2380_; lean_object* v___y_2381_; uint8_t v___y_2382_; uint8_t v___y_2383_; lean_object* v___y_2384_; uint8_t v___y_2408_; lean_object* v___y_2409_; uint8_t v___y_2410_; uint8_t v___y_2411_; lean_object* v___y_2412_; uint8_t v___y_2416_; uint8_t v___y_2417_; uint8_t v___y_2418_; uint8_t v___x_2433_; uint8_t v___y_2435_; uint8_t v___y_2436_; uint8_t v___y_2437_; uint8_t v___y_2439_; uint8_t v___x_2451_; 
v___x_2433_ = 2;
v___x_2451_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2309_, v___x_2433_);
if (v___x_2451_ == 0)
{
v___y_2439_ = v___x_2451_;
goto v___jp_2438_;
}
else
{
uint8_t v___x_2452_; 
lean_inc_ref(v_msgData_2308_);
v___x_2452_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2308_);
v___y_2439_ = v___x_2452_;
goto v___jp_2438_;
}
v___jp_2314_:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_Elab_Command_getScope___redArg(v___y_2322_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v_currNamespace_2325_; lean_object* v___x_2326_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v_currNamespace_2325_ = lean_ctor_get(v_a_2324_, 2);
lean_inc(v_currNamespace_2325_);
lean_dec(v_a_2324_);
v___x_2326_ = l_Lean_Elab_Command_getScope___redArg(v___y_2322_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2362_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2362_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2362_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v_openDecls_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v_env_2336_; lean_object* v_messages_2337_; lean_object* v_scopes_2338_; lean_object* v_usedQuotCtxts_2339_; lean_object* v_nextMacroScope_2340_; lean_object* v_maxRecDepth_2341_; lean_object* v_ngen_2342_; lean_object* v_auxDeclNGen_2343_; lean_object* v_infoState_2344_; lean_object* v_traceState_2345_; lean_object* v_snapshotTasks_2346_; lean_object* v_prevLinterStates_2347_; lean_object* v_codeQualityEntryTasks_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2361_; 
v_openDecls_2331_ = lean_ctor_get(v_a_2327_, 3);
lean_inc(v_openDecls_2331_);
lean_dec(v_a_2327_);
v___x_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2332_, 0, v_currNamespace_2325_);
lean_ctor_set(v___x_2332_, 1, v_openDecls_2331_);
v___x_2333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v___y_2320_);
lean_inc_ref(v___y_2318_);
lean_inc_ref(v___y_2317_);
v___x_2334_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2334_, 0, v___y_2317_);
lean_ctor_set(v___x_2334_, 1, v___y_2315_);
lean_ctor_set(v___x_2334_, 2, v___y_2316_);
lean_ctor_set(v___x_2334_, 3, v___y_2318_);
lean_ctor_set(v___x_2334_, 4, v___x_2333_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*5, v___y_2321_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*5 + 1, v___y_2319_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*5 + 2, v_isSilent_2310_);
v___x_2335_ = lean_st_ref_take(v___y_2322_);
v_env_2336_ = lean_ctor_get(v___x_2335_, 0);
v_messages_2337_ = lean_ctor_get(v___x_2335_, 1);
v_scopes_2338_ = lean_ctor_get(v___x_2335_, 2);
v_usedQuotCtxts_2339_ = lean_ctor_get(v___x_2335_, 3);
v_nextMacroScope_2340_ = lean_ctor_get(v___x_2335_, 4);
v_maxRecDepth_2341_ = lean_ctor_get(v___x_2335_, 5);
v_ngen_2342_ = lean_ctor_get(v___x_2335_, 6);
v_auxDeclNGen_2343_ = lean_ctor_get(v___x_2335_, 7);
v_infoState_2344_ = lean_ctor_get(v___x_2335_, 8);
v_traceState_2345_ = lean_ctor_get(v___x_2335_, 9);
v_snapshotTasks_2346_ = lean_ctor_get(v___x_2335_, 10);
v_prevLinterStates_2347_ = lean_ctor_get(v___x_2335_, 11);
v_codeQualityEntryTasks_2348_ = lean_ctor_get(v___x_2335_, 12);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2350_ = v___x_2335_;
v_isShared_2351_ = v_isSharedCheck_2361_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2348_);
lean_inc(v_prevLinterStates_2347_);
lean_inc(v_snapshotTasks_2346_);
lean_inc(v_traceState_2345_);
lean_inc(v_infoState_2344_);
lean_inc(v_auxDeclNGen_2343_);
lean_inc(v_ngen_2342_);
lean_inc(v_maxRecDepth_2341_);
lean_inc(v_nextMacroScope_2340_);
lean_inc(v_usedQuotCtxts_2339_);
lean_inc(v_scopes_2338_);
lean_inc(v_messages_2337_);
lean_inc(v_env_2336_);
lean_dec(v___x_2335_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2361_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2352_ = lean_box(0);
v___x_2353_ = l_Lean_MessageLog_add(v___x_2334_, v_messages_2337_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 1, v___x_2353_);
v___x_2355_ = v___x_2350_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_env_2336_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_scopes_2338_);
lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_usedQuotCtxts_2339_);
lean_ctor_set(v_reuseFailAlloc_2360_, 4, v_nextMacroScope_2340_);
lean_ctor_set(v_reuseFailAlloc_2360_, 5, v_maxRecDepth_2341_);
lean_ctor_set(v_reuseFailAlloc_2360_, 6, v_ngen_2342_);
lean_ctor_set(v_reuseFailAlloc_2360_, 7, v_auxDeclNGen_2343_);
lean_ctor_set(v_reuseFailAlloc_2360_, 8, v_infoState_2344_);
lean_ctor_set(v_reuseFailAlloc_2360_, 9, v_traceState_2345_);
lean_ctor_set(v_reuseFailAlloc_2360_, 10, v_snapshotTasks_2346_);
lean_ctor_set(v_reuseFailAlloc_2360_, 11, v_prevLinterStates_2347_);
lean_ctor_set(v_reuseFailAlloc_2360_, 12, v_codeQualityEntryTasks_2348_);
v___x_2355_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = lean_st_ref_put(v___y_2322_, v___x_2355_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2352_);
v___x_2358_ = v___x_2329_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2352_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec(v_currNamespace_2325_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
v_a_2363_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2326_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2326_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
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
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
v_a_2371_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2323_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2323_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
v___jp_2379_:
{
lean_object* v_fileName_2385_; lean_object* v_fileMap_2386_; uint8_t v_suppressElabErrors_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___f_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2406_; 
v_fileName_2385_ = lean_ctor_get(v___y_2311_, 0);
v_fileMap_2386_ = lean_ctor_get(v___y_2311_, 1);
v_suppressElabErrors_2387_ = lean_ctor_get_uint8(v___y_2311_, sizeof(void*)*10);
v___x_2388_ = lean_box(v_suppressElabErrors_2387_);
v___x_2389_ = lean_box(v___y_2380_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2390_, 0, v___x_2388_);
lean_closure_set(v___f_2390_, 1, v___x_2389_);
v___x_2391_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2308_);
v___x_2392_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2391_, v___y_2312_);
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2406_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2406_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_inc_ref_n(v_fileMap_2386_, 2);
v___x_2397_ = l_Lean_FileMap_toPosition(v_fileMap_2386_, v___y_2381_);
lean_dec(v___y_2381_);
v___x_2398_ = l_Lean_FileMap_toPosition(v_fileMap_2386_, v___y_2384_);
lean_dec(v___y_2384_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
v___x_2400_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
if (v_suppressElabErrors_2387_ == 0)
{
lean_del_object(v___x_2395_);
lean_dec_ref(v___f_2390_);
v___y_2315_ = v___x_2397_;
v___y_2316_ = v___x_2399_;
v___y_2317_ = v_fileName_2385_;
v___y_2318_ = v___x_2400_;
v___y_2319_ = v___y_2382_;
v___y_2320_ = v_a_2393_;
v___y_2321_ = v___y_2383_;
v___y_2322_ = v___y_2312_;
goto v___jp_2314_;
}
else
{
uint8_t v___x_2401_; 
lean_inc(v_a_2393_);
v___x_2401_ = l_Lean_MessageData_hasTag(v___f_2390_, v_a_2393_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
lean_dec_ref_known(v___x_2399_, 1);
lean_dec_ref(v___x_2397_);
lean_dec(v_a_2393_);
v___x_2402_ = lean_box(0);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2402_);
v___x_2404_ = v___x_2395_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
else
{
lean_del_object(v___x_2395_);
v___y_2315_ = v___x_2397_;
v___y_2316_ = v___x_2399_;
v___y_2317_ = v_fileName_2385_;
v___y_2318_ = v___x_2400_;
v___y_2319_ = v___y_2382_;
v___y_2320_ = v_a_2393_;
v___y_2321_ = v___y_2383_;
v___y_2322_ = v___y_2312_;
goto v___jp_2314_;
}
}
}
}
v___jp_2407_:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_Syntax_getTailPos_x3f(v___y_2409_, v___y_2411_);
lean_dec(v___y_2409_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_inc(v___y_2412_);
v___y_2380_ = v___y_2408_;
v___y_2381_ = v___y_2412_;
v___y_2382_ = v___y_2410_;
v___y_2383_ = v___y_2411_;
v___y_2384_ = v___y_2412_;
goto v___jp_2379_;
}
else
{
lean_object* v_val_2414_; 
v_val_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_val_2414_);
lean_dec_ref_known(v___x_2413_, 1);
v___y_2380_ = v___y_2408_;
v___y_2381_ = v___y_2412_;
v___y_2382_ = v___y_2410_;
v___y_2383_ = v___y_2411_;
v___y_2384_ = v_val_2414_;
goto v___jp_2379_;
}
}
v___jp_2415_:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_Elab_Command_getRef___redArg(v___y_2311_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v_ref_2421_; lean_object* v___x_2422_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v_ref_2421_ = l_Lean_replaceRef(v_ref_2307_, v_a_2420_);
lean_dec(v_a_2420_);
v___x_2422_ = l_Lean_Syntax_getPos_x3f(v_ref_2421_, v___y_2417_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v___x_2423_; 
v___x_2423_ = lean_unsigned_to_nat(0u);
v___y_2408_ = v___y_2416_;
v___y_2409_ = v_ref_2421_;
v___y_2410_ = v___y_2418_;
v___y_2411_ = v___y_2417_;
v___y_2412_ = v___x_2423_;
goto v___jp_2407_;
}
else
{
lean_object* v_val_2424_; 
v_val_2424_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_val_2424_);
lean_dec_ref_known(v___x_2422_, 1);
v___y_2408_ = v___y_2416_;
v___y_2409_ = v_ref_2421_;
v___y_2410_ = v___y_2418_;
v___y_2411_ = v___y_2417_;
v___y_2412_ = v_val_2424_;
goto v___jp_2407_;
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec_ref(v_msgData_2308_);
v_a_2425_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2419_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2419_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
v___jp_2434_:
{
if (v___y_2437_ == 0)
{
v___y_2416_ = v___y_2435_;
v___y_2417_ = v___y_2436_;
v___y_2418_ = v_severity_2309_;
goto v___jp_2415_;
}
else
{
v___y_2416_ = v___y_2435_;
v___y_2417_ = v___y_2436_;
v___y_2418_ = v___x_2433_;
goto v___jp_2415_;
}
}
v___jp_2438_:
{
if (v___y_2439_ == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v_scopes_2442_; lean_object* v___x_2443_; lean_object* v_opts_2444_; uint8_t v___x_2445_; uint8_t v___x_2446_; 
v___x_2440_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2441_ = lean_st_ref_get(v___y_2312_);
v_scopes_2442_ = lean_ctor_get(v___x_2441_, 2);
lean_inc(v_scopes_2442_);
lean_dec(v___x_2441_);
v___x_2443_ = l_List_head_x21___redArg(v___x_2440_, v_scopes_2442_);
lean_dec(v_scopes_2442_);
v_opts_2444_ = lean_ctor_get(v___x_2443_, 1);
lean_inc_ref(v_opts_2444_);
lean_dec(v___x_2443_);
v___x_2445_ = 1;
v___x_2446_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2309_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_dec_ref(v_opts_2444_);
v___y_2435_ = v___y_2439_;
v___y_2436_ = v___y_2439_;
v___y_2437_ = v___x_2446_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2447_ = l_Lean_warningAsError;
v___x_2448_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2444_, v___x_2447_);
lean_dec_ref(v_opts_2444_);
v___y_2435_ = v___y_2439_;
v___y_2436_ = v___y_2439_;
v___y_2437_ = v___x_2448_;
goto v___jp_2434_;
}
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_dec_ref(v_msgData_2308_);
v___x_2449_ = lean_box(0);
v___x_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
return v___x_2450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2453_, lean_object* v_msgData_2454_, lean_object* v_severity_2455_, lean_object* v_isSilent_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
uint8_t v_severity_boxed_2460_; uint8_t v_isSilent_boxed_2461_; lean_object* v_res_2462_; 
v_severity_boxed_2460_ = lean_unbox(v_severity_2455_);
v_isSilent_boxed_2461_ = lean_unbox(v_isSilent_2456_);
v_res_2462_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2453_, v_msgData_2454_, v_severity_boxed_2460_, v_isSilent_boxed_2461_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v_ref_2453_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2463_, lean_object* v_msgData_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
uint8_t v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; 
v___x_2468_ = 2;
v___x_2469_ = 0;
v___x_2470_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2463_, v_msgData_2464_, v___x_2468_, v___x_2469_, v___y_2465_, v___y_2466_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2471_, lean_object* v_msgData_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2471_, v_msgData_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v_ref_2471_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2477_, lean_object* v___x_2478_, lean_object* v___x_2479_, lean_object* v_a_2480_, lean_object* v_b_2481_){
_start:
{
lean_object* v_it_2483_; lean_object* v_startInclusive_2484_; lean_object* v_endExclusive_2485_; 
if (lean_obj_tag(v_a_2480_) == 0)
{
lean_object* v_currPos_2490_; lean_object* v_searcher_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2520_; 
v_currPos_2490_ = lean_ctor_get(v_a_2480_, 0);
v_searcher_2491_ = lean_ctor_get(v_a_2480_, 1);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_a_2480_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2493_ = v_a_2480_;
v_isShared_2494_ = v_isSharedCheck_2520_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_searcher_2491_);
lean_inc(v_currPos_2490_);
lean_dec(v_a_2480_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2520_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v_str_2495_; lean_object* v_startInclusive_2496_; lean_object* v_endExclusive_2497_; lean_object* v___x_2498_; uint8_t v_decide_2499_; 
v_str_2495_ = lean_ctor_get(v___x_2478_, 0);
v_startInclusive_2496_ = lean_ctor_get(v___x_2478_, 1);
v_endExclusive_2497_ = lean_ctor_get(v___x_2478_, 2);
v___x_2498_ = lean_nat_sub(v_endExclusive_2497_, v_startInclusive_2496_);
v_decide_2499_ = lean_nat_dec_eq(v_searcher_2491_, v___x_2498_);
lean_dec(v___x_2498_);
if (v_decide_2499_ == 0)
{
uint32_t v___x_2500_; lean_object* v___x_2501_; uint32_t v___x_2502_; uint8_t v___x_2503_; 
v___x_2500_ = 10;
v___x_2501_ = lean_nat_add(v_startInclusive_2496_, v_searcher_2491_);
v___x_2502_ = lean_string_utf8_get_fast(v_str_2495_, v___x_2501_);
v___x_2503_ = lean_uint32_dec_eq(v___x_2502_, v___x_2500_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2507_; 
lean_dec(v_searcher_2491_);
v___x_2504_ = lean_string_utf8_next_fast(v_str_2495_, v___x_2501_);
lean_dec(v___x_2501_);
v___x_2505_ = lean_nat_sub(v___x_2504_, v_startInclusive_2496_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 1, v___x_2505_);
v___x_2507_ = v___x_2493_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_currPos_2490_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
v_a_2480_ = v___x_2507_;
goto _start;
}
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v_slice_2513_; lean_object* v_nextIt_2515_; 
v___x_2510_ = lean_string_utf8_next_fast(v_str_2495_, v___x_2501_);
v___x_2511_ = lean_nat_sub(v___x_2510_, v___x_2501_);
lean_dec(v___x_2501_);
v___x_2512_ = lean_nat_add(v_searcher_2491_, v___x_2511_);
lean_dec(v___x_2511_);
v_slice_2513_ = l_String_Slice_subslice_x21(v___x_2478_, v_currPos_2490_, v_searcher_2491_);
lean_inc(v___x_2512_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 1, v___x_2512_);
lean_ctor_set(v___x_2493_, 0, v___x_2512_);
v_nextIt_2515_ = v___x_2493_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v___x_2512_);
v_nextIt_2515_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v_startInclusive_2516_; lean_object* v_endExclusive_2517_; 
v_startInclusive_2516_ = lean_ctor_get(v_slice_2513_, 0);
lean_inc(v_startInclusive_2516_);
v_endExclusive_2517_ = lean_ctor_get(v_slice_2513_, 1);
lean_inc(v_endExclusive_2517_);
lean_dec_ref(v_slice_2513_);
v_it_2483_ = v_nextIt_2515_;
v_startInclusive_2484_ = v_startInclusive_2516_;
v_endExclusive_2485_ = v_endExclusive_2517_;
goto v___jp_2482_;
}
}
}
else
{
lean_object* v___x_2519_; 
lean_del_object(v___x_2493_);
lean_dec(v_searcher_2491_);
v___x_2519_ = lean_box(1);
lean_inc(v___x_2479_);
v_it_2483_ = v___x_2519_;
v_startInclusive_2484_ = v_currPos_2490_;
v_endExclusive_2485_ = v___x_2479_;
goto v___jp_2482_;
}
}
}
else
{
lean_dec(v___x_2479_);
lean_dec_ref(v___x_2477_);
return v_b_2481_;
}
v___jp_2482_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
lean_inc_ref(v___x_2477_);
v___x_2486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2477_);
lean_ctor_set(v___x_2486_, 1, v_startInclusive_2484_);
lean_ctor_set(v___x_2486_, 2, v_endExclusive_2485_);
v___x_2487_ = l_String_Slice_toString(v___x_2486_);
lean_dec_ref_known(v___x_2486_, 3);
v___x_2488_ = lean_array_push(v_b_2481_, v___x_2487_);
v_a_2480_ = v_it_2483_;
v_b_2481_ = v___x_2488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2521_, lean_object* v___x_2522_, lean_object* v___x_2523_, lean_object* v_a_2524_, lean_object* v_b_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2521_, v___x_2522_, v___x_2523_, v_a_2524_, v_b_2525_);
lean_dec_ref(v___x_2522_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2527_, lean_object* v___x_2528_, lean_object* v___x_2529_, lean_object* v_a_2530_, lean_object* v_b_2531_){
_start:
{
lean_object* v_it_2533_; lean_object* v_startInclusive_2534_; lean_object* v_endExclusive_2535_; 
if (lean_obj_tag(v_a_2530_) == 0)
{
lean_object* v_currPos_2540_; lean_object* v_searcher_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2570_; 
v_currPos_2540_ = lean_ctor_get(v_a_2530_, 0);
v_searcher_2541_ = lean_ctor_get(v_a_2530_, 1);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_a_2530_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2543_ = v_a_2530_;
v_isShared_2544_ = v_isSharedCheck_2570_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_searcher_2541_);
lean_inc(v_currPos_2540_);
lean_dec(v_a_2530_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2570_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v_str_2545_; lean_object* v_startInclusive_2546_; lean_object* v_endExclusive_2547_; lean_object* v___x_2548_; uint8_t v_decide_2549_; 
v_str_2545_ = lean_ctor_get(v___x_2528_, 0);
v_startInclusive_2546_ = lean_ctor_get(v___x_2528_, 1);
v_endExclusive_2547_ = lean_ctor_get(v___x_2528_, 2);
v___x_2548_ = lean_nat_sub(v_endExclusive_2547_, v_startInclusive_2546_);
v_decide_2549_ = lean_nat_dec_eq(v_searcher_2541_, v___x_2548_);
lean_dec(v___x_2548_);
if (v_decide_2549_ == 0)
{
lean_object* v___x_2550_; uint32_t v___x_2551_; uint32_t v___x_2552_; uint8_t v___x_2553_; 
v___x_2550_ = lean_nat_add(v_startInclusive_2546_, v_searcher_2541_);
v___x_2551_ = lean_string_utf8_get_fast(v_str_2545_, v___x_2550_);
v___x_2552_ = 10;
v___x_2553_ = lean_uint32_dec_eq(v___x_2551_, v___x_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
lean_dec(v_searcher_2541_);
v___x_2554_ = lean_string_utf8_next_fast(v_str_2545_, v___x_2550_);
lean_dec(v___x_2550_);
v___x_2555_ = lean_nat_sub(v___x_2554_, v_startInclusive_2546_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 1, v___x_2555_);
v___x_2557_ = v___x_2543_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_currPos_2540_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; 
v___x_2558_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2527_, v___x_2528_, v___x_2529_, v___x_2557_, v_b_2531_);
return v___x_2558_;
}
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_slice_2563_; lean_object* v_nextIt_2565_; 
v___x_2560_ = lean_string_utf8_next_fast(v_str_2545_, v___x_2550_);
v___x_2561_ = lean_nat_sub(v___x_2560_, v___x_2550_);
lean_dec(v___x_2550_);
v___x_2562_ = lean_nat_add(v_searcher_2541_, v___x_2561_);
lean_dec(v___x_2561_);
v_slice_2563_ = l_String_Slice_subslice_x21(v___x_2528_, v_currPos_2540_, v_searcher_2541_);
lean_inc(v___x_2562_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 1, v___x_2562_);
lean_ctor_set(v___x_2543_, 0, v___x_2562_);
v_nextIt_2565_ = v___x_2543_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v___x_2562_);
v_nextIt_2565_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v_startInclusive_2566_; lean_object* v_endExclusive_2567_; 
v_startInclusive_2566_ = lean_ctor_get(v_slice_2563_, 0);
lean_inc(v_startInclusive_2566_);
v_endExclusive_2567_ = lean_ctor_get(v_slice_2563_, 1);
lean_inc(v_endExclusive_2567_);
lean_dec_ref(v_slice_2563_);
v_it_2533_ = v_nextIt_2565_;
v_startInclusive_2534_ = v_startInclusive_2566_;
v_endExclusive_2535_ = v_endExclusive_2567_;
goto v___jp_2532_;
}
}
}
else
{
lean_object* v___x_2569_; 
lean_del_object(v___x_2543_);
lean_dec(v_searcher_2541_);
v___x_2569_ = lean_box(1);
lean_inc(v___x_2529_);
v_it_2533_ = v___x_2569_;
v_startInclusive_2534_ = v_currPos_2540_;
v_endExclusive_2535_ = v___x_2529_;
goto v___jp_2532_;
}
}
}
else
{
lean_dec(v___x_2529_);
lean_dec_ref(v___x_2527_);
return v_b_2531_;
}
v___jp_2532_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_inc_ref(v___x_2527_);
v___x_2536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2527_);
lean_ctor_set(v___x_2536_, 1, v_startInclusive_2534_);
lean_ctor_set(v___x_2536_, 2, v_endExclusive_2535_);
v___x_2537_ = l_String_Slice_toString(v___x_2536_);
lean_dec_ref_known(v___x_2536_, 3);
v___x_2538_ = lean_array_push(v_b_2531_, v___x_2537_);
v___x_2539_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2527_, v___x_2528_, v___x_2529_, v_it_2533_, v___x_2538_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2571_, lean_object* v___x_2572_, lean_object* v___x_2573_, lean_object* v_a_2574_, lean_object* v_b_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2571_, v___x_2572_, v___x_2573_, v_a_2574_, v_b_2575_);
lean_dec_ref(v___x_2572_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; lean_object* v_infoState_2581_; uint8_t v_enabled_2582_; 
v___x_2580_ = lean_st_ref_get(v___y_2578_);
v_infoState_2581_ = lean_ctor_get(v___x_2580_, 8);
lean_inc_ref(v_infoState_2581_);
lean_dec(v___x_2580_);
v_enabled_2582_ = lean_ctor_get_uint8(v_infoState_2581_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2581_);
if (v_enabled_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_dec_ref(v_t_2577_);
v___x_2583_ = lean_box(0);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
return v___x_2584_;
}
else
{
lean_object* v___x_2585_; lean_object* v_infoState_2586_; lean_object* v_env_2587_; lean_object* v_messages_2588_; lean_object* v_scopes_2589_; lean_object* v_usedQuotCtxts_2590_; lean_object* v_nextMacroScope_2591_; lean_object* v_maxRecDepth_2592_; lean_object* v_ngen_2593_; lean_object* v_auxDeclNGen_2594_; lean_object* v_traceState_2595_; lean_object* v_snapshotTasks_2596_; lean_object* v_prevLinterStates_2597_; lean_object* v_codeQualityEntryTasks_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2620_; 
v___x_2585_ = lean_st_ref_take(v___y_2578_);
v_infoState_2586_ = lean_ctor_get(v___x_2585_, 8);
v_env_2587_ = lean_ctor_get(v___x_2585_, 0);
v_messages_2588_ = lean_ctor_get(v___x_2585_, 1);
v_scopes_2589_ = lean_ctor_get(v___x_2585_, 2);
v_usedQuotCtxts_2590_ = lean_ctor_get(v___x_2585_, 3);
v_nextMacroScope_2591_ = lean_ctor_get(v___x_2585_, 4);
v_maxRecDepth_2592_ = lean_ctor_get(v___x_2585_, 5);
v_ngen_2593_ = lean_ctor_get(v___x_2585_, 6);
v_auxDeclNGen_2594_ = lean_ctor_get(v___x_2585_, 7);
v_traceState_2595_ = lean_ctor_get(v___x_2585_, 9);
v_snapshotTasks_2596_ = lean_ctor_get(v___x_2585_, 10);
v_prevLinterStates_2597_ = lean_ctor_get(v___x_2585_, 11);
v_codeQualityEntryTasks_2598_ = lean_ctor_get(v___x_2585_, 12);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2600_ = v___x_2585_;
v_isShared_2601_ = v_isSharedCheck_2620_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2598_);
lean_inc(v_prevLinterStates_2597_);
lean_inc(v_snapshotTasks_2596_);
lean_inc(v_traceState_2595_);
lean_inc(v_infoState_2586_);
lean_inc(v_auxDeclNGen_2594_);
lean_inc(v_ngen_2593_);
lean_inc(v_maxRecDepth_2592_);
lean_inc(v_nextMacroScope_2591_);
lean_inc(v_usedQuotCtxts_2590_);
lean_inc(v_scopes_2589_);
lean_inc(v_messages_2588_);
lean_inc(v_env_2587_);
lean_dec(v___x_2585_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2620_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
uint8_t v_enabled_2602_; lean_object* v_assignment_2603_; lean_object* v_lazyAssignment_2604_; lean_object* v_trees_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2619_; 
v_enabled_2602_ = lean_ctor_get_uint8(v_infoState_2586_, sizeof(void*)*3);
v_assignment_2603_ = lean_ctor_get(v_infoState_2586_, 0);
v_lazyAssignment_2604_ = lean_ctor_get(v_infoState_2586_, 1);
v_trees_2605_ = lean_ctor_get(v_infoState_2586_, 2);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_infoState_2586_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2607_ = v_infoState_2586_;
v_isShared_2608_ = v_isSharedCheck_2619_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_trees_2605_);
lean_inc(v_lazyAssignment_2604_);
lean_inc(v_assignment_2603_);
lean_dec(v_infoState_2586_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2619_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2609_ = lean_box(0);
v___x_2610_ = l_Lean_PersistentArray_push___redArg(v_trees_2605_, v_t_2577_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 2, v___x_2610_);
v___x_2612_ = v___x_2607_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_assignment_2603_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_lazyAssignment_2604_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v___x_2610_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*3, v_enabled_2602_);
v___x_2612_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2614_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 8, v___x_2612_);
v___x_2614_ = v___x_2600_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_env_2587_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_messages_2588_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_scopes_2589_);
lean_ctor_set(v_reuseFailAlloc_2617_, 3, v_usedQuotCtxts_2590_);
lean_ctor_set(v_reuseFailAlloc_2617_, 4, v_nextMacroScope_2591_);
lean_ctor_set(v_reuseFailAlloc_2617_, 5, v_maxRecDepth_2592_);
lean_ctor_set(v_reuseFailAlloc_2617_, 6, v_ngen_2593_);
lean_ctor_set(v_reuseFailAlloc_2617_, 7, v_auxDeclNGen_2594_);
lean_ctor_set(v_reuseFailAlloc_2617_, 8, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2617_, 9, v_traceState_2595_);
lean_ctor_set(v_reuseFailAlloc_2617_, 10, v_snapshotTasks_2596_);
lean_ctor_set(v_reuseFailAlloc_2617_, 11, v_prevLinterStates_2597_);
lean_ctor_set(v_reuseFailAlloc_2617_, 12, v_codeQualityEntryTasks_2598_);
v___x_2614_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_st_ref_put(v___y_2578_, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2609_);
return v___x_2616_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2621_, v___y_2622_);
lean_dec(v___y_2622_);
return v_res_2624_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = lean_unsigned_to_nat(32u);
v___x_2626_ = lean_mk_empty_array_with_capacity(v___x_2625_);
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2628_ = ((size_t)5ULL);
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = lean_unsigned_to_nat(32u);
v___x_2631_ = lean_mk_empty_array_with_capacity(v___x_2630_);
v___x_2632_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2633_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v___x_2631_);
lean_ctor_set(v___x_2633_, 2, v___x_2629_);
lean_ctor_set(v___x_2633_, 3, v___x_2629_);
lean_ctor_set_usize(v___x_2633_, 4, v___x_2628_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; lean_object* v_infoState_2639_; uint8_t v_enabled_2640_; 
v___x_2638_ = lean_st_ref_get(v___y_2636_);
v_infoState_2639_ = lean_ctor_get(v___x_2638_, 8);
lean_inc_ref(v_infoState_2639_);
lean_dec(v___x_2638_);
v_enabled_2640_ = lean_ctor_get_uint8(v_infoState_2639_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2639_);
if (v_enabled_2640_ == 0)
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_dec_ref(v_t_2634_);
v___x_2641_ = lean_box(0);
v___x_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
return v___x_2642_;
}
else
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2644_, 0, v_t_2634_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2644_, v___y_2636_);
return v___x_2645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v___x_2651_, lean_object* v_edited_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_){
_start:
{
lean_object* v_fst_2655_; lean_object* v_snd_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2680_; 
v_fst_2655_ = lean_ctor_get(v_a_2654_, 0);
v_snd_2656_ = lean_ctor_get(v_a_2654_, 1);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_a_2654_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2658_ = v_a_2654_;
v_isShared_2659_ = v_isSharedCheck_2680_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_snd_2656_);
lean_inc(v_fst_2655_);
lean_dec(v_a_2654_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2680_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
uint8_t v___x_2660_; 
v___x_2660_ = lean_nat_dec_lt(v_snd_2656_, v___x_2651_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2662_; 
if (v_isShared_2659_ == 0)
{
v___x_2662_ = v___x_2658_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_fst_2655_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_snd_2656_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2664_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2665_ = lean_array_get_borrowed(v___x_2664_, v_edited_2652_, v_snd_2656_);
v___x_2666_ = lean_string_dec_eq(v___x_2665_, v_a_2653_);
if (v___x_2666_ == 0)
{
uint8_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2667_ = 0;
v___x_2668_ = lean_box(v___x_2667_);
lean_inc(v___x_2665_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 1, v___x_2665_);
lean_ctor_set(v___x_2658_, 0, v___x_2668_);
v___x_2670_ = v___x_2658_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___x_2665_);
v___x_2670_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2671_ = lean_array_push(v_fst_2655_, v___x_2670_);
v___x_2672_ = lean_unsigned_to_nat(1u);
v___x_2673_ = lean_nat_add(v_snd_2656_, v___x_2672_);
lean_dec(v_snd_2656_);
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2671_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v_a_2654_ = v___x_2674_;
goto _start;
}
}
else
{
lean_object* v___x_2678_; 
if (v_isShared_2659_ == 0)
{
v___x_2678_ = v___x_2658_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_fst_2655_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_snd_2656_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v___x_2681_, lean_object* v_edited_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2681_, v_edited_2682_, v_a_2683_, v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec_ref(v_edited_2682_);
lean_dec(v___x_2681_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(lean_object* v___x_2686_, lean_object* v_original_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_fst_2690_; lean_object* v_snd_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2715_; 
v_fst_2690_ = lean_ctor_get(v_a_2689_, 0);
v_snd_2691_ = lean_ctor_get(v_a_2689_, 1);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_a_2689_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2693_ = v_a_2689_;
v_isShared_2694_ = v_isSharedCheck_2715_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_snd_2691_);
lean_inc(v_fst_2690_);
lean_dec(v_a_2689_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2715_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
uint8_t v___x_2695_; 
v___x_2695_ = lean_nat_dec_lt(v_snd_2691_, v___x_2686_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2697_; 
if (v_isShared_2694_ == 0)
{
v___x_2697_ = v___x_2693_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_fst_2690_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_snd_2691_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2699_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2700_ = lean_array_get_borrowed(v___x_2699_, v_original_2687_, v_snd_2691_);
v___x_2701_ = lean_string_dec_eq(v___x_2700_, v_a_2688_);
if (v___x_2701_ == 0)
{
uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2702_ = 1;
v___x_2703_ = lean_box(v___x_2702_);
lean_inc(v___x_2700_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v___x_2700_);
lean_ctor_set(v___x_2693_, 0, v___x_2703_);
v___x_2705_ = v___x_2693_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2700_);
v___x_2705_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2706_ = lean_array_push(v_fst_2690_, v___x_2705_);
v___x_2707_ = lean_unsigned_to_nat(1u);
v___x_2708_ = lean_nat_add(v_snd_2691_, v___x_2707_);
lean_dec(v_snd_2691_);
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2706_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v_a_2689_ = v___x_2709_;
goto _start;
}
}
else
{
lean_object* v___x_2713_; 
if (v_isShared_2694_ == 0)
{
v___x_2713_ = v___x_2693_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_fst_2690_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_snd_2691_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg___boxed(lean_object* v___x_2716_, lean_object* v_original_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2716_, v_original_2717_, v_a_2718_, v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec_ref(v_original_2717_);
lean_dec(v___x_2716_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v___x_2721_, lean_object* v_original_2722_, lean_object* v___x_2723_, lean_object* v_edited_2724_, lean_object* v_as_2725_, size_t v_sz_2726_, size_t v_i_2727_, lean_object* v_b_2728_){
_start:
{
uint8_t v___x_2729_; 
v___x_2729_ = lean_usize_dec_lt(v_i_2727_, v_sz_2726_);
if (v___x_2729_ == 0)
{
return v_b_2728_;
}
else
{
lean_object* v_snd_2730_; lean_object* v_fst_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2778_; 
v_snd_2730_ = lean_ctor_get(v_b_2728_, 1);
v_fst_2731_ = lean_ctor_get(v_b_2728_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_b_2728_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2733_ = v_b_2728_;
v_isShared_2734_ = v_isSharedCheck_2778_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_snd_2730_);
lean_inc(v_fst_2731_);
lean_dec(v_b_2728_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2778_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_fst_2735_; lean_object* v_snd_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2777_; 
v_fst_2735_ = lean_ctor_get(v_snd_2730_, 0);
v_snd_2736_ = lean_ctor_get(v_snd_2730_, 1);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_snd_2730_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2738_ = v_snd_2730_;
v_isShared_2739_ = v_isSharedCheck_2777_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_snd_2736_);
lean_inc(v_fst_2735_);
lean_dec(v_snd_2730_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2777_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v_a_2740_; lean_object* v___x_2742_; 
v_a_2740_ = lean_array_uget_borrowed(v_as_2725_, v_i_2727_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 1, v_fst_2735_);
lean_ctor_set(v___x_2738_, 0, v_fst_2731_);
v___x_2742_ = v___x_2738_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_fst_2731_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_fst_2735_);
v___x_2742_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; lean_object* v_fst_2744_; lean_object* v_snd_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2775_; 
v___x_2743_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2721_, v_original_2722_, v_a_2740_, v___x_2742_);
v_fst_2744_ = lean_ctor_get(v___x_2743_, 0);
v_snd_2745_ = lean_ctor_get(v___x_2743_, 1);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2747_ = v___x_2743_;
v_isShared_2748_ = v_isSharedCheck_2775_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_snd_2745_);
lean_inc(v_fst_2744_);
lean_dec(v___x_2743_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2775_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 1, v_snd_2736_);
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_fst_2744_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_snd_2736_);
v___x_2750_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; lean_object* v_fst_2752_; lean_object* v_snd_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2773_; 
v___x_2751_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2723_, v_edited_2724_, v_a_2740_, v___x_2750_);
v_fst_2752_ = lean_ctor_get(v___x_2751_, 0);
v_snd_2753_ = lean_ctor_get(v___x_2751_, 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2755_ = v___x_2751_;
v_isShared_2756_ = v_isSharedCheck_2773_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_snd_2753_);
lean_inc(v_fst_2752_);
lean_dec(v___x_2751_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2773_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
uint8_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2757_ = 2;
v___x_2758_ = lean_box(v___x_2757_);
lean_inc(v_a_2740_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 1, v_a_2740_);
lean_ctor_set(v___x_2755_, 0, v___x_2758_);
v___x_2760_ = v___x_2755_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_a_2740_);
v___x_2760_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2761_ = lean_array_push(v_fst_2752_, v___x_2760_);
v___x_2762_ = lean_unsigned_to_nat(1u);
v___x_2763_ = lean_nat_add(v_snd_2745_, v___x_2762_);
lean_dec(v_snd_2745_);
v___x_2764_ = lean_nat_add(v_snd_2753_, v___x_2762_);
lean_dec(v_snd_2753_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2764_);
lean_ctor_set(v___x_2733_, 0, v___x_2763_);
v___x_2766_ = v___x_2733_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2763_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; size_t v___x_2768_; size_t v___x_2769_; 
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2761_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = ((size_t)1ULL);
v___x_2769_ = lean_usize_add(v_i_2727_, v___x_2768_);
v_i_2727_ = v___x_2769_;
v_b_2728_ = v___x_2767_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v___x_2779_, lean_object* v_original_2780_, lean_object* v___x_2781_, lean_object* v_edited_2782_, lean_object* v_as_2783_, lean_object* v_sz_2784_, lean_object* v_i_2785_, lean_object* v_b_2786_){
_start:
{
size_t v_sz_boxed_2787_; size_t v_i_boxed_2788_; lean_object* v_res_2789_; 
v_sz_boxed_2787_ = lean_unbox_usize(v_sz_2784_);
lean_dec(v_sz_2784_);
v_i_boxed_2788_ = lean_unbox_usize(v_i_2785_);
lean_dec(v_i_2785_);
v_res_2789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2779_, v_original_2780_, v___x_2781_, v_edited_2782_, v_as_2783_, v_sz_boxed_2787_, v_i_boxed_2788_, v_b_2786_);
lean_dec_ref(v_as_2783_);
lean_dec_ref(v_edited_2782_);
lean_dec(v___x_2781_);
lean_dec_ref(v_original_2780_);
lean_dec(v___x_2779_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v___x_2790_, lean_object* v_edited_2791_, lean_object* v___x_2792_, lean_object* v_original_2793_, lean_object* v_as_2794_, size_t v_sz_2795_, size_t v_i_2796_, lean_object* v_b_2797_){
_start:
{
uint8_t v___x_2798_; 
v___x_2798_ = lean_usize_dec_lt(v_i_2796_, v_sz_2795_);
if (v___x_2798_ == 0)
{
return v_b_2797_;
}
else
{
lean_object* v_snd_2799_; lean_object* v_fst_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2847_; 
v_snd_2799_ = lean_ctor_get(v_b_2797_, 1);
v_fst_2800_ = lean_ctor_get(v_b_2797_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_b_2797_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2802_ = v_b_2797_;
v_isShared_2803_ = v_isSharedCheck_2847_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_snd_2799_);
lean_inc(v_fst_2800_);
lean_dec(v_b_2797_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2847_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v_fst_2804_; lean_object* v_snd_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2846_; 
v_fst_2804_ = lean_ctor_get(v_snd_2799_, 0);
v_snd_2805_ = lean_ctor_get(v_snd_2799_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_snd_2799_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2807_ = v_snd_2799_;
v_isShared_2808_ = v_isSharedCheck_2846_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_snd_2805_);
lean_inc(v_fst_2804_);
lean_dec(v_snd_2799_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2846_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v_a_2809_; lean_object* v___x_2811_; 
v_a_2809_ = lean_array_uget_borrowed(v_as_2794_, v_i_2796_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 1, v_fst_2804_);
lean_ctor_set(v___x_2807_, 0, v_fst_2800_);
v___x_2811_ = v___x_2807_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_fst_2800_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_fst_2804_);
v___x_2811_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2812_; lean_object* v_fst_2813_; lean_object* v_snd_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2844_; 
v___x_2812_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2792_, v_original_2793_, v_a_2809_, v___x_2811_);
v_fst_2813_ = lean_ctor_get(v___x_2812_, 0);
v_snd_2814_ = lean_ctor_get(v___x_2812_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2816_ = v___x_2812_;
v_isShared_2817_ = v_isSharedCheck_2844_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_snd_2814_);
lean_inc(v_fst_2813_);
lean_dec(v___x_2812_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2844_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 1, v_snd_2805_);
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_fst_2813_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_snd_2805_);
v___x_2819_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; lean_object* v_fst_2821_; lean_object* v_snd_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2842_; 
v___x_2820_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2790_, v_edited_2791_, v_a_2809_, v___x_2819_);
v_fst_2821_ = lean_ctor_get(v___x_2820_, 0);
v_snd_2822_ = lean_ctor_get(v___x_2820_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2824_ = v___x_2820_;
v_isShared_2825_ = v_isSharedCheck_2842_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_snd_2822_);
lean_inc(v_fst_2821_);
lean_dec(v___x_2820_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2842_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
uint8_t v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2829_; 
v___x_2826_ = 2;
v___x_2827_ = lean_box(v___x_2826_);
lean_inc(v_a_2809_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 1, v_a_2809_);
lean_ctor_set(v___x_2824_, 0, v___x_2827_);
v___x_2829_ = v___x_2824_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_a_2809_);
v___x_2829_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2830_ = lean_array_push(v_fst_2821_, v___x_2829_);
v___x_2831_ = lean_unsigned_to_nat(1u);
v___x_2832_ = lean_nat_add(v_snd_2814_, v___x_2831_);
lean_dec(v_snd_2814_);
v___x_2833_ = lean_nat_add(v_snd_2822_, v___x_2831_);
lean_dec(v_snd_2822_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 1, v___x_2833_);
lean_ctor_set(v___x_2802_, 0, v___x_2832_);
v___x_2835_ = v___x_2802_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v___x_2833_);
v___x_2835_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; size_t v___x_2837_; size_t v___x_2838_; lean_object* v___x_2839_; 
v___x_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2830_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = ((size_t)1ULL);
v___x_2838_ = lean_usize_add(v_i_2796_, v___x_2837_);
v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2792_, v_original_2793_, v___x_2790_, v_edited_2791_, v_as_2794_, v_sz_2795_, v___x_2838_, v___x_2836_);
return v___x_2839_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v___x_2848_, lean_object* v_edited_2849_, lean_object* v___x_2850_, lean_object* v_original_2851_, lean_object* v_as_2852_, lean_object* v_sz_2853_, lean_object* v_i_2854_, lean_object* v_b_2855_){
_start:
{
size_t v_sz_boxed_2856_; size_t v_i_boxed_2857_; lean_object* v_res_2858_; 
v_sz_boxed_2856_ = lean_unbox_usize(v_sz_2853_);
lean_dec(v_sz_2853_);
v_i_boxed_2857_ = lean_unbox_usize(v_i_2854_);
lean_dec(v_i_2854_);
v_res_2858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_2848_, v_edited_2849_, v___x_2850_, v_original_2851_, v_as_2852_, v_sz_boxed_2856_, v_i_boxed_2857_, v_b_2855_);
lean_dec_ref(v_as_2852_);
lean_dec_ref(v_original_2851_);
lean_dec(v___x_2850_);
lean_dec_ref(v_edited_2849_);
lean_dec(v___x_2848_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_2859_, lean_object* v_original_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v_fst_2862_; lean_object* v_snd_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2882_; 
v_fst_2862_ = lean_ctor_get(v_a_2861_, 0);
v_snd_2863_ = lean_ctor_get(v_a_2861_, 1);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_a_2861_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2865_ = v_a_2861_;
v_isShared_2866_ = v_isSharedCheck_2882_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_snd_2863_);
lean_inc(v_fst_2862_);
lean_dec(v_a_2861_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2882_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
uint8_t v___x_2867_; 
v___x_2867_ = lean_nat_dec_lt(v_snd_2863_, v___x_2859_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2869_; 
if (v_isShared_2866_ == 0)
{
v___x_2869_ = v___x_2865_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_fst_2862_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_snd_2863_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
else
{
uint8_t v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2871_ = 1;
v___x_2872_ = lean_array_fget_borrowed(v_original_2860_, v_snd_2863_);
v___x_2873_ = lean_box(v___x_2871_);
lean_inc(v___x_2872_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v___x_2872_);
lean_ctor_set(v___x_2865_, 0, v___x_2873_);
v___x_2875_ = v___x_2865_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v___x_2872_);
v___x_2875_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2876_ = lean_array_push(v_fst_2862_, v___x_2875_);
v___x_2877_ = lean_unsigned_to_nat(1u);
v___x_2878_ = lean_nat_add(v_snd_2863_, v___x_2877_);
lean_dec(v_snd_2863_);
v___x_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2876_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v_a_2861_ = v___x_2879_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_2883_, lean_object* v_original_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_2883_, v_original_2884_, v_a_2885_);
lean_dec_ref(v_original_2884_);
lean_dec(v___x_2883_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_2887_, size_t v_i_2888_, lean_object* v_bs_2889_){
_start:
{
uint8_t v___x_2890_; 
v___x_2890_ = lean_usize_dec_lt(v_i_2888_, v_sz_2887_);
if (v___x_2890_ == 0)
{
return v_bs_2889_;
}
else
{
lean_object* v_v_2891_; lean_object* v___x_2892_; lean_object* v_bs_x27_2893_; uint8_t v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; size_t v___x_2897_; size_t v___x_2898_; lean_object* v___x_2899_; 
v_v_2891_ = lean_array_uget(v_bs_2889_, v_i_2888_);
v___x_2892_ = lean_unsigned_to_nat(0u);
v_bs_x27_2893_ = lean_array_uset(v_bs_2889_, v_i_2888_, v___x_2892_);
v___x_2894_ = 0;
v___x_2895_ = lean_box(v___x_2894_);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
lean_ctor_set(v___x_2896_, 1, v_v_2891_);
v___x_2897_ = ((size_t)1ULL);
v___x_2898_ = lean_usize_add(v_i_2888_, v___x_2897_);
v___x_2899_ = lean_array_uset(v_bs_x27_2893_, v_i_2888_, v___x_2896_);
v_i_2888_ = v___x_2898_;
v_bs_2889_ = v___x_2899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_2901_, lean_object* v_i_2902_, lean_object* v_bs_2903_){
_start:
{
size_t v_sz_boxed_2904_; size_t v_i_boxed_2905_; lean_object* v_res_2906_; 
v_sz_boxed_2904_ = lean_unbox_usize(v_sz_2901_);
lean_dec(v_sz_2901_);
v_i_boxed_2905_ = lean_unbox_usize(v_i_2902_);
lean_dec(v_i_2902_);
v_res_2906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_2904_, v_i_boxed_2905_, v_bs_2903_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_2907_, lean_object* v_edited_2908_, lean_object* v_a_2909_){
_start:
{
lean_object* v_fst_2910_; lean_object* v_snd_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2930_; 
v_fst_2910_ = lean_ctor_get(v_a_2909_, 0);
v_snd_2911_ = lean_ctor_get(v_a_2909_, 1);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_a_2909_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2913_ = v_a_2909_;
v_isShared_2914_ = v_isSharedCheck_2930_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_snd_2911_);
lean_inc(v_fst_2910_);
lean_dec(v_a_2909_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2930_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
uint8_t v___x_2915_; 
v___x_2915_ = lean_nat_dec_lt(v_snd_2911_, v___x_2907_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2917_; 
if (v_isShared_2914_ == 0)
{
v___x_2917_ = v___x_2913_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_fst_2910_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_snd_2911_);
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
uint8_t v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; 
v___x_2919_ = 0;
v___x_2920_ = lean_array_fget_borrowed(v_edited_2908_, v_snd_2911_);
v___x_2921_ = lean_box(v___x_2919_);
lean_inc(v___x_2920_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___x_2920_);
lean_ctor_set(v___x_2913_, 0, v___x_2921_);
v___x_2923_ = v___x_2913_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v___x_2920_);
v___x_2923_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2924_ = lean_array_push(v_fst_2910_, v___x_2923_);
v___x_2925_ = lean_unsigned_to_nat(1u);
v___x_2926_ = lean_nat_add(v_snd_2911_, v___x_2925_);
lean_dec(v_snd_2911_);
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2924_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v_a_2909_ = v___x_2927_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_2931_, lean_object* v_edited_2932_, lean_object* v_a_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_2931_, v_edited_2932_, v_a_2933_);
lean_dec_ref(v_edited_2932_);
lean_dec(v___x_2931_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(lean_object* v_x_2935_, lean_object* v_x_2936_){
_start:
{
if (lean_obj_tag(v_x_2936_) == 0)
{
lean_inc(v_x_2935_);
return v_x_2935_;
}
else
{
lean_object* v_key_2937_; lean_object* v_value_2938_; lean_object* v_tail_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_key_2937_ = lean_ctor_get(v_x_2936_, 0);
v_value_2938_ = lean_ctor_get(v_x_2936_, 1);
v_tail_2939_ = lean_ctor_get(v_x_2936_, 2);
v___x_2940_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2935_, v_tail_2939_);
lean_inc(v_value_2938_);
lean_inc(v_key_2937_);
v___x_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2941_, 0, v_key_2937_);
lean_ctor_set(v___x_2941_, 1, v_value_2938_);
v___x_2942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2940_);
return v___x_2942_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17___boxed(lean_object* v_x_2943_, lean_object* v_x_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2943_, v_x_2944_);
lean_dec(v_x_2944_);
lean_dec(v_x_2943_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(lean_object* v_as_2946_, size_t v_i_2947_, size_t v_stop_2948_, lean_object* v_b_2949_){
_start:
{
uint8_t v___x_2950_; 
v___x_2950_ = lean_usize_dec_eq(v_i_2947_, v_stop_2948_);
if (v___x_2950_ == 0)
{
size_t v___x_2951_; size_t v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2951_ = ((size_t)1ULL);
v___x_2952_ = lean_usize_sub(v_i_2947_, v___x_2951_);
v___x_2953_ = lean_array_uget_borrowed(v_as_2946_, v___x_2952_);
v___x_2954_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_b_2949_, v___x_2953_);
lean_dec(v_b_2949_);
v_i_2947_ = v___x_2952_;
v_b_2949_ = v___x_2954_;
goto _start;
}
else
{
return v_b_2949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18___boxed(lean_object* v_as_2956_, lean_object* v_i_2957_, lean_object* v_stop_2958_, lean_object* v_b_2959_){
_start:
{
size_t v_i_boxed_2960_; size_t v_stop_boxed_2961_; lean_object* v_res_2962_; 
v_i_boxed_2960_ = lean_unbox_usize(v_i_2957_);
lean_dec(v_i_2957_);
v_stop_boxed_2961_ = lean_unbox_usize(v_stop_2958_);
lean_dec(v_stop_2958_);
v_res_2962_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_as_2956_, v_i_boxed_2960_, v_stop_boxed_2961_, v_b_2959_);
lean_dec_ref(v_as_2956_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(lean_object* v_left_2963_, lean_object* v_right_2964_, lean_object* v_pref_2965_){
_start:
{
lean_object* v_start_2966_; lean_object* v_stop_2967_; lean_object* v_start_2968_; lean_object* v_stop_2969_; lean_object* v_i_2970_; uint8_t v___y_2972_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v_start_2966_ = lean_ctor_get(v_left_2963_, 1);
v_stop_2967_ = lean_ctor_get(v_left_2963_, 2);
v_start_2968_ = lean_ctor_get(v_right_2964_, 1);
v_stop_2969_ = lean_ctor_get(v_right_2964_, 2);
v_i_2970_ = lean_array_get_size(v_pref_2965_);
v___x_2986_ = lean_nat_sub(v_stop_2967_, v_start_2966_);
v___x_2987_ = lean_nat_dec_lt(v_i_2970_, v___x_2986_);
lean_dec(v___x_2986_);
if (v___x_2987_ == 0)
{
v___y_2972_ = v___x_2987_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_2988_; uint8_t v___x_2989_; 
v___x_2988_ = lean_nat_sub(v_stop_2969_, v_start_2968_);
v___x_2989_ = lean_nat_dec_lt(v_i_2970_, v___x_2988_);
lean_dec(v___x_2988_);
v___y_2972_ = v___x_2989_;
goto v___jp_2971_;
}
v___jp_2971_:
{
if (v___y_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2973_ = l_Subarray_drop___redArg(v_left_2963_, v_i_2970_);
v___x_2974_ = l_Subarray_drop___redArg(v_right_2964_, v_i_2970_);
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2973_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v_pref_2965_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2977_ = l_Subarray_get___redArg(v_left_2963_, v_i_2970_);
v___x_2978_ = l_Subarray_get___redArg(v_right_2964_, v_i_2970_);
v___x_2979_ = lean_string_dec_eq(v___x_2977_, v___x_2978_);
lean_dec(v___x_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
lean_dec(v___x_2977_);
v___x_2980_ = l_Subarray_drop___redArg(v_left_2963_, v_i_2970_);
v___x_2981_ = l_Subarray_drop___redArg(v_right_2964_, v_i_2970_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v_pref_2965_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
return v___x_2983_;
}
else
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_array_push(v_pref_2965_, v___x_2977_);
v_pref_2965_ = v___x_2984_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(lean_object* v_left_2992_, lean_object* v_right_2993_){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_2995_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(v_left_2992_, v_right_2993_, v___x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(lean_object* v_a_2996_, lean_object* v_b_2997_, lean_object* v_x_2998_){
_start:
{
if (lean_obj_tag(v_x_2998_) == 0)
{
lean_dec(v_b_2997_);
lean_dec_ref(v_a_2996_);
return v_x_2998_;
}
else
{
lean_object* v_key_2999_; lean_object* v_value_3000_; lean_object* v_tail_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3013_; 
v_key_2999_ = lean_ctor_get(v_x_2998_, 0);
v_value_3000_ = lean_ctor_get(v_x_2998_, 1);
v_tail_3001_ = lean_ctor_get(v_x_2998_, 2);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_x_2998_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3003_ = v_x_2998_;
v_isShared_3004_ = v_isSharedCheck_3013_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_tail_3001_);
lean_inc(v_value_3000_);
lean_inc(v_key_2999_);
lean_dec(v_x_2998_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3013_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
uint8_t v___x_3005_; 
v___x_3005_ = lean_string_dec_eq(v_key_2999_, v_a_2996_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_3006_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_2996_, v_b_2997_, v_tail_3001_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 2, v___x_3006_);
v___x_3008_ = v___x_3003_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_key_2999_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v_value_3000_);
lean_ctor_set(v_reuseFailAlloc_3009_, 2, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
else
{
lean_object* v___x_3011_; 
lean_dec(v_value_3000_);
lean_dec(v_key_2999_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 1, v_b_2997_);
lean_ctor_set(v___x_3003_, 0, v_a_2996_);
v___x_3011_ = v___x_3003_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_2996_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_b_2997_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_tail_3001_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(lean_object* v_x_3014_, lean_object* v_x_3015_){
_start:
{
if (lean_obj_tag(v_x_3015_) == 0)
{
return v_x_3014_;
}
else
{
lean_object* v_key_3016_; lean_object* v_value_3017_; lean_object* v_tail_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3041_; 
v_key_3016_ = lean_ctor_get(v_x_3015_, 0);
v_value_3017_ = lean_ctor_get(v_x_3015_, 1);
v_tail_3018_ = lean_ctor_get(v_x_3015_, 2);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_x_3015_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3020_ = v_x_3015_;
v_isShared_3021_ = v_isSharedCheck_3041_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_tail_3018_);
lean_inc(v_value_3017_);
lean_inc(v_key_3016_);
lean_dec(v_x_3015_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3041_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; uint64_t v___x_3023_; uint64_t v___x_3024_; uint64_t v___x_3025_; uint64_t v_fold_3026_; uint64_t v___x_3027_; uint64_t v___x_3028_; uint64_t v___x_3029_; size_t v___x_3030_; size_t v___x_3031_; size_t v___x_3032_; size_t v___x_3033_; size_t v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3022_ = lean_array_get_size(v_x_3014_);
v___x_3023_ = lean_string_hash(v_key_3016_);
v___x_3024_ = 32ULL;
v___x_3025_ = lean_uint64_shift_right(v___x_3023_, v___x_3024_);
v_fold_3026_ = lean_uint64_xor(v___x_3023_, v___x_3025_);
v___x_3027_ = 16ULL;
v___x_3028_ = lean_uint64_shift_right(v_fold_3026_, v___x_3027_);
v___x_3029_ = lean_uint64_xor(v_fold_3026_, v___x_3028_);
v___x_3030_ = lean_uint64_to_usize(v___x_3029_);
v___x_3031_ = lean_usize_of_nat(v___x_3022_);
v___x_3032_ = ((size_t)1ULL);
v___x_3033_ = lean_usize_sub(v___x_3031_, v___x_3032_);
v___x_3034_ = lean_usize_land(v___x_3030_, v___x_3033_);
v___x_3035_ = lean_array_uget_borrowed(v_x_3014_, v___x_3034_);
lean_inc(v___x_3035_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 2, v___x_3035_);
v___x_3037_ = v___x_3020_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_key_3016_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v_value_3017_);
lean_ctor_set(v_reuseFailAlloc_3040_, 2, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_array_uset(v_x_3014_, v___x_3034_, v___x_3037_);
v_x_3014_ = v___x_3038_;
v_x_3015_ = v_tail_3018_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(lean_object* v_i_3042_, lean_object* v_source_3043_, lean_object* v_target_3044_){
_start:
{
lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = lean_array_get_size(v_source_3043_);
v___x_3046_ = lean_nat_dec_lt(v_i_3042_, v___x_3045_);
if (v___x_3046_ == 0)
{
lean_dec_ref(v_source_3043_);
lean_dec(v_i_3042_);
return v_target_3044_;
}
else
{
lean_object* v_es_3047_; lean_object* v___x_3048_; lean_object* v_source_3049_; lean_object* v_target_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v_es_3047_ = lean_array_fget(v_source_3043_, v_i_3042_);
v___x_3048_ = lean_box(0);
v_source_3049_ = lean_array_fset(v_source_3043_, v_i_3042_, v___x_3048_);
v_target_3050_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_target_3044_, v_es_3047_);
v___x_3051_ = lean_unsigned_to_nat(1u);
v___x_3052_ = lean_nat_add(v_i_3042_, v___x_3051_);
lean_dec(v_i_3042_);
v_i_3042_ = v___x_3052_;
v_source_3043_ = v_source_3049_;
v_target_3044_ = v_target_3050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(lean_object* v_data_3054_){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v_nbuckets_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3055_ = lean_array_get_size(v_data_3054_);
v___x_3056_ = lean_unsigned_to_nat(2u);
v_nbuckets_3057_ = lean_nat_mul(v___x_3055_, v___x_3056_);
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3059_ = lean_box(0);
v___x_3060_ = lean_mk_array(v_nbuckets_3057_, v___x_3059_);
v___x_3061_ = lean_array_propagate_mark(v_data_3054_, v___x_3060_);
v___x_3062_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v___x_3058_, v_data_3054_, v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(lean_object* v_a_3063_, lean_object* v_x_3064_){
_start:
{
if (lean_obj_tag(v_x_3064_) == 0)
{
uint8_t v___x_3065_; 
v___x_3065_ = 0;
return v___x_3065_;
}
else
{
lean_object* v_key_3066_; lean_object* v_tail_3067_; uint8_t v___x_3068_; 
v_key_3066_ = lean_ctor_get(v_x_3064_, 0);
v_tail_3067_ = lean_ctor_get(v_x_3064_, 2);
v___x_3068_ = lean_string_dec_eq(v_key_3066_, v_a_3063_);
if (v___x_3068_ == 0)
{
v_x_3064_ = v_tail_3067_;
goto _start;
}
else
{
return v___x_3068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg___boxed(lean_object* v_a_3070_, lean_object* v_x_3071_){
_start:
{
uint8_t v_res_3072_; lean_object* v_r_3073_; 
v_res_3072_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_3070_, v_x_3071_);
lean_dec(v_x_3071_);
lean_dec_ref(v_a_3070_);
v_r_3073_ = lean_box(v_res_3072_);
return v_r_3073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(lean_object* v_m_3074_, lean_object* v_a_3075_, lean_object* v_b_3076_){
_start:
{
lean_object* v_size_3077_; lean_object* v_buckets_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3121_; 
v_size_3077_ = lean_ctor_get(v_m_3074_, 0);
v_buckets_3078_ = lean_ctor_get(v_m_3074_, 1);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_m_3074_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3080_ = v_m_3074_;
v_isShared_3081_ = v_isSharedCheck_3121_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_buckets_3078_);
lean_inc(v_size_3077_);
lean_dec(v_m_3074_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3121_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; uint64_t v___x_3083_; uint64_t v___x_3084_; uint64_t v___x_3085_; uint64_t v_fold_3086_; uint64_t v___x_3087_; uint64_t v___x_3088_; uint64_t v___x_3089_; size_t v___x_3090_; size_t v___x_3091_; size_t v___x_3092_; size_t v___x_3093_; size_t v___x_3094_; lean_object* v_bkt_3095_; uint8_t v___x_3096_; 
v___x_3082_ = lean_array_get_size(v_buckets_3078_);
v___x_3083_ = lean_string_hash(v_a_3075_);
v___x_3084_ = 32ULL;
v___x_3085_ = lean_uint64_shift_right(v___x_3083_, v___x_3084_);
v_fold_3086_ = lean_uint64_xor(v___x_3083_, v___x_3085_);
v___x_3087_ = 16ULL;
v___x_3088_ = lean_uint64_shift_right(v_fold_3086_, v___x_3087_);
v___x_3089_ = lean_uint64_xor(v_fold_3086_, v___x_3088_);
v___x_3090_ = lean_uint64_to_usize(v___x_3089_);
v___x_3091_ = lean_usize_of_nat(v___x_3082_);
v___x_3092_ = ((size_t)1ULL);
v___x_3093_ = lean_usize_sub(v___x_3091_, v___x_3092_);
v___x_3094_ = lean_usize_land(v___x_3090_, v___x_3093_);
v_bkt_3095_ = lean_array_uget_borrowed(v_buckets_3078_, v___x_3094_);
v___x_3096_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_3075_, v_bkt_3095_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; lean_object* v_size_x27_3098_; lean_object* v___x_3099_; lean_object* v_buckets_x27_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3097_ = lean_unsigned_to_nat(1u);
v_size_x27_3098_ = lean_nat_add(v_size_3077_, v___x_3097_);
lean_dec(v_size_3077_);
lean_inc(v_bkt_3095_);
v___x_3099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3099_, 0, v_a_3075_);
lean_ctor_set(v___x_3099_, 1, v_b_3076_);
lean_ctor_set(v___x_3099_, 2, v_bkt_3095_);
v_buckets_x27_3100_ = lean_array_uset(v_buckets_3078_, v___x_3094_, v___x_3099_);
v___x_3101_ = lean_unsigned_to_nat(4u);
v___x_3102_ = lean_nat_mul(v_size_x27_3098_, v___x_3101_);
v___x_3103_ = lean_unsigned_to_nat(3u);
v___x_3104_ = lean_nat_div(v___x_3102_, v___x_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_array_get_size(v_buckets_x27_3100_);
v___x_3106_ = lean_nat_dec_le(v___x_3104_, v___x_3105_);
lean_dec(v___x_3104_);
if (v___x_3106_ == 0)
{
lean_object* v_val_3107_; lean_object* v___x_3109_; 
v_val_3107_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_buckets_x27_3100_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 1, v_val_3107_);
lean_ctor_set(v___x_3080_, 0, v_size_x27_3098_);
v___x_3109_ = v___x_3080_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_size_x27_3098_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_val_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
else
{
lean_object* v___x_3112_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 1, v_buckets_x27_3100_);
lean_ctor_set(v___x_3080_, 0, v_size_x27_3098_);
v___x_3112_ = v___x_3080_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_size_x27_3098_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_buckets_x27_3100_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
else
{
lean_object* v___x_3114_; lean_object* v_buckets_x27_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
lean_inc(v_bkt_3095_);
v___x_3114_ = lean_box(0);
v_buckets_x27_3115_ = lean_array_uset(v_buckets_3078_, v___x_3094_, v___x_3114_);
v___x_3116_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_3075_, v_b_3076_, v_bkt_3095_);
v___x_3117_ = lean_array_uset(v_buckets_x27_3115_, v___x_3094_, v___x_3116_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 1, v___x_3117_);
v___x_3119_ = v___x_3080_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_size_3077_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(lean_object* v_a_3122_, lean_object* v_x_3123_){
_start:
{
if (lean_obj_tag(v_x_3123_) == 0)
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_box(0);
return v___x_3124_;
}
else
{
lean_object* v_key_3125_; lean_object* v_value_3126_; lean_object* v_tail_3127_; uint8_t v___x_3128_; 
v_key_3125_ = lean_ctor_get(v_x_3123_, 0);
v_value_3126_ = lean_ctor_get(v_x_3123_, 1);
v_tail_3127_ = lean_ctor_get(v_x_3123_, 2);
v___x_3128_ = lean_string_dec_eq(v_key_3125_, v_a_3122_);
if (v___x_3128_ == 0)
{
v_x_3123_ = v_tail_3127_;
goto _start;
}
else
{
lean_object* v___x_3130_; 
lean_inc(v_value_3126_);
v___x_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_value_3126_);
return v___x_3130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg___boxed(lean_object* v_a_3131_, lean_object* v_x_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3131_, v_x_3132_);
lean_dec(v_x_3132_);
lean_dec_ref(v_a_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(lean_object* v_m_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_buckets_3136_; lean_object* v___x_3137_; uint64_t v___x_3138_; uint64_t v___x_3139_; uint64_t v___x_3140_; uint64_t v_fold_3141_; uint64_t v___x_3142_; uint64_t v___x_3143_; uint64_t v___x_3144_; size_t v___x_3145_; size_t v___x_3146_; size_t v___x_3147_; size_t v___x_3148_; size_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_buckets_3136_ = lean_ctor_get(v_m_3134_, 1);
v___x_3137_ = lean_array_get_size(v_buckets_3136_);
v___x_3138_ = lean_string_hash(v_a_3135_);
v___x_3139_ = 32ULL;
v___x_3140_ = lean_uint64_shift_right(v___x_3138_, v___x_3139_);
v_fold_3141_ = lean_uint64_xor(v___x_3138_, v___x_3140_);
v___x_3142_ = 16ULL;
v___x_3143_ = lean_uint64_shift_right(v_fold_3141_, v___x_3142_);
v___x_3144_ = lean_uint64_xor(v_fold_3141_, v___x_3143_);
v___x_3145_ = lean_uint64_to_usize(v___x_3144_);
v___x_3146_ = lean_usize_of_nat(v___x_3137_);
v___x_3147_ = ((size_t)1ULL);
v___x_3148_ = lean_usize_sub(v___x_3146_, v___x_3147_);
v___x_3149_ = lean_usize_land(v___x_3145_, v___x_3148_);
v___x_3150_ = lean_array_uget_borrowed(v_buckets_3136_, v___x_3149_);
v___x_3151_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3135_, v___x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg___boxed(lean_object* v_m_3152_, lean_object* v_a_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_3152_, v_a_3153_);
lean_dec_ref(v_a_3153_);
lean_dec_ref(v_m_3152_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(lean_object* v_histogram_3155_, lean_object* v_index_3156_, lean_object* v_val_3157_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3155_, v_val_3157_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3159_ = lean_unsigned_to_nat(1u);
v___x_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3160_, 0, v_index_3156_);
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = lean_box(0);
v___x_3163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3159_);
lean_ctor_set(v___x_3163_, 1, v___x_3160_);
lean_ctor_set(v___x_3163_, 2, v___x_3161_);
lean_ctor_set(v___x_3163_, 3, v___x_3162_);
v___x_3164_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3155_, v_val_3157_, v___x_3163_);
return v___x_3164_;
}
else
{
lean_object* v_val_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3186_; 
v_val_3165_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3167_ = v___x_3158_;
v_isShared_3168_ = v_isSharedCheck_3186_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_val_3165_);
lean_dec(v___x_3158_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3186_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v_leftCount_3169_; lean_object* v_rightCount_3170_; lean_object* v_rightIndex_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3184_; 
v_leftCount_3169_ = lean_ctor_get(v_val_3165_, 0);
v_rightCount_3170_ = lean_ctor_get(v_val_3165_, 2);
v_rightIndex_3171_ = lean_ctor_get(v_val_3165_, 3);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_val_3165_);
if (v_isSharedCheck_3184_ == 0)
{
lean_object* v_unused_3185_; 
v_unused_3185_ = lean_ctor_get(v_val_3165_, 1);
lean_dec(v_unused_3185_);
v___x_3173_ = v_val_3165_;
v_isShared_3174_ = v_isSharedCheck_3184_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_rightIndex_3171_);
lean_inc(v_rightCount_3170_);
lean_inc(v_leftCount_3169_);
lean_dec(v_val_3165_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3184_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3175_ = lean_unsigned_to_nat(1u);
v___x_3176_ = lean_nat_add(v_leftCount_3169_, v___x_3175_);
lean_dec(v_leftCount_3169_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 0, v_index_3156_);
v___x_3178_ = v___x_3167_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_index_3156_);
v___x_3178_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3180_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 1, v___x_3178_);
lean_ctor_set(v___x_3173_, 0, v___x_3176_);
v___x_3180_ = v___x_3173_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3182_, 2, v_rightCount_3170_);
lean_ctor_set(v_reuseFailAlloc_3182_, 3, v_rightIndex_3171_);
v___x_3180_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3155_, v_val_3157_, v___x_3180_);
return v___x_3181_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(lean_object* v_upperBound_3187_, lean_object* v_fst_3188_, lean_object* v___x_3189_, lean_object* v_fst_3190_, lean_object* v_a_3191_, lean_object* v_b_3192_){
_start:
{
uint8_t v___x_3193_; 
v___x_3193_ = lean_nat_dec_lt(v_a_3191_, v_upperBound_3187_);
if (v___x_3193_ == 0)
{
lean_dec(v_a_3191_);
return v_b_3192_;
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3194_ = l_Subarray_get___redArg(v_fst_3190_, v_a_3191_);
lean_inc(v_a_3191_);
v___x_3195_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_b_3192_, v_a_3191_, v___x_3194_);
v___x_3196_ = lean_unsigned_to_nat(1u);
v___x_3197_ = lean_nat_add(v_a_3191_, v___x_3196_);
lean_dec(v_a_3191_);
v_a_3191_ = v___x_3197_;
v_b_3192_ = v___x_3195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_upperBound_3199_, lean_object* v_fst_3200_, lean_object* v___x_3201_, lean_object* v_fst_3202_, lean_object* v_a_3203_, lean_object* v_b_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3199_, v_fst_3200_, v___x_3201_, v_fst_3202_, v_a_3203_, v_b_3204_);
lean_dec_ref(v_fst_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_fst_3200_);
lean_dec(v_upperBound_3199_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(lean_object* v_as_x27_3206_, lean_object* v_b_3207_){
_start:
{
if (lean_obj_tag(v_as_x27_3206_) == 0)
{
return v_b_3207_;
}
else
{
lean_object* v_head_3208_; lean_object* v_snd_3209_; lean_object* v_leftIndex_3210_; 
v_head_3208_ = lean_ctor_get(v_as_x27_3206_, 0);
v_snd_3209_ = lean_ctor_get(v_head_3208_, 1);
v_leftIndex_3210_ = lean_ctor_get(v_snd_3209_, 1);
if (lean_obj_tag(v_leftIndex_3210_) == 1)
{
lean_object* v_rightIndex_3211_; 
v_rightIndex_3211_ = lean_ctor_get(v_snd_3209_, 3);
if (lean_obj_tag(v_rightIndex_3211_) == 1)
{
if (lean_obj_tag(v_b_3207_) == 0)
{
lean_object* v_tail_3212_; lean_object* v_fst_3213_; lean_object* v_leftCount_3214_; lean_object* v_rightCount_3215_; lean_object* v_val_3216_; lean_object* v_val_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_tail_3212_ = lean_ctor_get(v_as_x27_3206_, 1);
v_fst_3213_ = lean_ctor_get(v_head_3208_, 0);
v_leftCount_3214_ = lean_ctor_get(v_snd_3209_, 0);
v_rightCount_3215_ = lean_ctor_get(v_snd_3209_, 2);
v_val_3216_ = lean_ctor_get(v_leftIndex_3210_, 0);
v_val_3217_ = lean_ctor_get(v_rightIndex_3211_, 0);
v___x_3218_ = lean_nat_add(v_leftCount_3214_, v_rightCount_3215_);
lean_inc(v_val_3217_);
lean_inc(v_val_3216_);
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_val_3216_);
lean_ctor_set(v___x_3219_, 1, v_val_3217_);
lean_inc(v_fst_3213_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_fst_3213_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3218_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
v_as_x27_3206_ = v_tail_3212_;
v_b_3207_ = v___x_3222_;
goto _start;
}
else
{
lean_object* v_val_3224_; lean_object* v_tail_3225_; lean_object* v_fst_3226_; lean_object* v_leftCount_3227_; lean_object* v_rightCount_3228_; lean_object* v_val_3229_; lean_object* v_val_3230_; lean_object* v_fst_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3252_; 
v_val_3224_ = lean_ctor_get(v_b_3207_, 0);
lean_inc(v_val_3224_);
v_tail_3225_ = lean_ctor_get(v_as_x27_3206_, 1);
v_fst_3226_ = lean_ctor_get(v_head_3208_, 0);
v_leftCount_3227_ = lean_ctor_get(v_snd_3209_, 0);
v_rightCount_3228_ = lean_ctor_get(v_snd_3209_, 2);
v_val_3229_ = lean_ctor_get(v_leftIndex_3210_, 0);
v_val_3230_ = lean_ctor_get(v_rightIndex_3211_, 0);
v_fst_3231_ = lean_ctor_get(v_val_3224_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_val_3224_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v_val_3224_, 1);
lean_dec(v_unused_3253_);
v___x_3233_ = v_val_3224_;
v_isShared_3234_ = v_isSharedCheck_3252_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_fst_3231_);
lean_dec(v_val_3224_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3252_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = lean_nat_add(v_leftCount_3227_, v_rightCount_3228_);
v___x_3236_ = lean_nat_dec_lt(v___x_3235_, v_fst_3231_);
lean_dec(v_fst_3231_);
if (v___x_3236_ == 0)
{
lean_dec(v___x_3235_);
lean_del_object(v___x_3233_);
v_as_x27_3206_ = v_tail_3225_;
goto _start;
}
else
{
lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3250_; 
v_isSharedCheck_3250_ = !lean_is_exclusive(v_b_3207_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v_b_3207_, 0);
lean_dec(v_unused_3251_);
v___x_3239_ = v_b_3207_;
v_isShared_3240_ = v_isSharedCheck_3250_;
goto v_resetjp_3238_;
}
else
{
lean_dec(v_b_3207_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3250_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
lean_inc(v_val_3230_);
lean_inc(v_val_3229_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v_val_3230_);
lean_ctor_set(v___x_3233_, 0, v_val_3229_);
v___x_3242_ = v___x_3233_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_val_3229_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_val_3230_);
v___x_3242_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
lean_inc(v_fst_3226_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v_fst_3226_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3235_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___x_3244_);
v___x_3246_ = v___x_3239_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
v_as_x27_3206_ = v_tail_3225_;
v_b_3207_ = v___x_3246_;
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
lean_object* v_tail_3254_; 
v_tail_3254_ = lean_ctor_get(v_as_x27_3206_, 1);
v_as_x27_3206_ = v_tail_3254_;
goto _start;
}
}
else
{
lean_object* v_tail_3256_; 
v_tail_3256_ = lean_ctor_get(v_as_x27_3206_, 1);
v_as_x27_3206_ = v_tail_3256_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg___boxed(lean_object* v_as_x27_3258_, lean_object* v_b_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3258_, v_b_3259_);
lean_dec(v_as_x27_3258_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(lean_object* v_histogram_3261_, lean_object* v_index_3262_, lean_object* v_val_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3261_, v_val_3263_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3265_ = lean_unsigned_to_nat(0u);
v___x_3266_ = lean_box(0);
v___x_3267_ = lean_unsigned_to_nat(1u);
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_index_3262_);
v___x_3269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3265_);
lean_ctor_set(v___x_3269_, 1, v___x_3266_);
lean_ctor_set(v___x_3269_, 2, v___x_3267_);
lean_ctor_set(v___x_3269_, 3, v___x_3268_);
v___x_3270_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3261_, v_val_3263_, v___x_3269_);
return v___x_3270_;
}
else
{
lean_object* v_val_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3292_; 
v_val_3271_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3273_ = v___x_3264_;
v_isShared_3274_ = v_isSharedCheck_3292_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_val_3271_);
lean_dec(v___x_3264_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3292_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v_leftCount_3275_; lean_object* v_leftIndex_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3289_; 
v_leftCount_3275_ = lean_ctor_get(v_val_3271_, 0);
v_leftIndex_3276_ = lean_ctor_get(v_val_3271_, 1);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_val_3271_);
if (v_isSharedCheck_3289_ == 0)
{
lean_object* v_unused_3290_; lean_object* v_unused_3291_; 
v_unused_3290_ = lean_ctor_get(v_val_3271_, 3);
lean_dec(v_unused_3290_);
v_unused_3291_ = lean_ctor_get(v_val_3271_, 2);
lean_dec(v_unused_3291_);
v___x_3278_ = v_val_3271_;
v_isShared_3279_ = v_isSharedCheck_3289_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_leftIndex_3276_);
lean_inc(v_leftCount_3275_);
lean_dec(v_val_3271_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3289_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3280_ = lean_unsigned_to_nat(1u);
v___x_3281_ = lean_nat_add(v_leftCount_3275_, v___x_3280_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v_index_3262_);
v___x_3283_ = v___x_3273_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_index_3262_);
v___x_3283_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3285_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 3, v___x_3283_);
lean_ctor_set(v___x_3278_, 2, v___x_3281_);
v___x_3285_ = v___x_3278_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_leftCount_3275_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_leftIndex_3276_);
lean_ctor_set(v_reuseFailAlloc_3287_, 2, v___x_3281_);
lean_ctor_set(v_reuseFailAlloc_3287_, 3, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3261_, v_val_3263_, v___x_3285_);
return v___x_3286_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(lean_object* v_upperBound_3293_, lean_object* v___x_3294_, lean_object* v_fst_3295_, lean_object* v___x_3296_, lean_object* v_a_3297_, lean_object* v_b_3298_){
_start:
{
uint8_t v___x_3299_; 
v___x_3299_ = lean_nat_dec_lt(v_a_3297_, v_upperBound_3293_);
if (v___x_3299_ == 0)
{
lean_dec(v_a_3297_);
return v_b_3298_;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3300_ = l_Subarray_get___redArg(v_fst_3295_, v_a_3297_);
lean_inc(v_a_3297_);
v___x_3301_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_b_3298_, v_a_3297_, v___x_3300_);
v___x_3302_ = lean_unsigned_to_nat(1u);
v___x_3303_ = lean_nat_add(v_a_3297_, v___x_3302_);
lean_dec(v_a_3297_);
v_a_3297_ = v___x_3303_;
v_b_3298_ = v___x_3301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg___boxed(lean_object* v_upperBound_3305_, lean_object* v___x_3306_, lean_object* v_fst_3307_, lean_object* v___x_3308_, lean_object* v_a_3309_, lean_object* v_b_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3305_, v___x_3306_, v_fst_3307_, v___x_3308_, v_a_3309_, v_b_3310_);
lean_dec(v___x_3308_);
lean_dec_ref(v_fst_3307_);
lean_dec(v___x_3306_);
lean_dec(v_upperBound_3305_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(lean_object* v_a_3312_, lean_object* v_b_3313_){
_start:
{
lean_object* v_array_3314_; lean_object* v_start_3315_; lean_object* v_stop_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3329_; 
v_array_3314_ = lean_ctor_get(v_a_3312_, 0);
v_start_3315_ = lean_ctor_get(v_a_3312_, 1);
v_stop_3316_ = lean_ctor_get(v_a_3312_, 2);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_a_3312_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3318_ = v_a_3312_;
v_isShared_3319_ = v_isSharedCheck_3329_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_stop_3316_);
lean_inc(v_start_3315_);
lean_inc(v_array_3314_);
lean_dec(v_a_3312_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3329_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
uint8_t v___x_3320_; 
v___x_3320_ = lean_nat_dec_lt(v_start_3315_, v_stop_3316_);
if (v___x_3320_ == 0)
{
lean_del_object(v___x_3318_);
lean_dec(v_stop_3316_);
lean_dec(v_start_3315_);
lean_dec_ref(v_array_3314_);
return v_b_3313_;
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
v___x_3321_ = lean_unsigned_to_nat(1u);
v___x_3322_ = lean_nat_add(v_start_3315_, v___x_3321_);
lean_inc_ref(v_array_3314_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 1, v___x_3322_);
v___x_3324_ = v___x_3318_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_array_3314_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3328_, 2, v_stop_3316_);
v___x_3324_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = lean_array_fget(v_array_3314_, v_start_3315_);
lean_dec(v_start_3315_);
lean_dec_ref(v_array_3314_);
v___x_3326_ = lean_array_push(v_b_3313_, v___x_3325_);
v_a_3312_ = v___x_3324_;
v_b_3313_ = v___x_3326_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(lean_object* v_left_3330_, lean_object* v_right_3331_, lean_object* v_i_3332_){
_start:
{
lean_object* v_start_3333_; lean_object* v_stop_3334_; lean_object* v_start_3335_; lean_object* v_stop_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; uint8_t v___y_3341_; 
v_start_3333_ = lean_ctor_get(v_left_3330_, 1);
v_stop_3334_ = lean_ctor_get(v_left_3330_, 2);
v_start_3335_ = lean_ctor_get(v_right_3331_, 1);
v_stop_3336_ = lean_ctor_get(v_right_3331_, 2);
v___x_3337_ = lean_nat_sub(v_stop_3334_, v_start_3333_);
v___x_3338_ = lean_nat_dec_lt(v_i_3332_, v___x_3337_);
v___x_3339_ = lean_nat_sub(v_stop_3336_, v_start_3335_);
if (v___x_3338_ == 0)
{
v___y_3341_ = v___x_3338_;
goto v___jp_3340_;
}
else
{
uint8_t v___x_3368_; 
v___x_3368_ = lean_nat_dec_lt(v_i_3332_, v___x_3339_);
v___y_3341_ = v___x_3368_;
goto v___jp_3340_;
}
v___jp_3340_:
{
if (v___y_3341_ == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3342_ = lean_nat_sub(v___x_3337_, v_i_3332_);
lean_dec(v___x_3337_);
lean_inc_ref(v_left_3330_);
v___x_3343_ = l_Subarray_take___redArg(v_left_3330_, v___x_3342_);
v___x_3344_ = lean_nat_sub(v___x_3339_, v_i_3332_);
lean_dec(v_i_3332_);
lean_dec(v___x_3339_);
v___x_3345_ = l_Subarray_take___redArg(v_right_3331_, v___x_3344_);
lean_dec(v___x_3344_);
v___x_3346_ = l_Subarray_drop___redArg(v_left_3330_, v___x_3342_);
lean_dec(v___x_3342_);
v___x_3347_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3348_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3346_, v___x_3347_);
v___x_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3345_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3343_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
return v___x_3350_;
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3351_ = lean_nat_sub(v___x_3337_, v_i_3332_);
lean_dec(v___x_3337_);
v___x_3352_ = lean_unsigned_to_nat(1u);
v___x_3353_ = lean_nat_sub(v___x_3351_, v___x_3352_);
v___x_3354_ = l_Subarray_get___redArg(v_left_3330_, v___x_3353_);
lean_dec(v___x_3353_);
v___x_3355_ = lean_nat_sub(v___x_3339_, v_i_3332_);
lean_dec(v___x_3339_);
v___x_3356_ = lean_nat_sub(v___x_3355_, v___x_3352_);
v___x_3357_ = l_Subarray_get___redArg(v_right_3331_, v___x_3356_);
lean_dec(v___x_3356_);
v___x_3358_ = lean_string_dec_eq(v___x_3354_, v___x_3357_);
lean_dec(v___x_3357_);
lean_dec(v___x_3354_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
lean_dec(v_i_3332_);
lean_inc_ref(v_left_3330_);
v___x_3359_ = l_Subarray_take___redArg(v_left_3330_, v___x_3351_);
v___x_3360_ = l_Subarray_take___redArg(v_right_3331_, v___x_3355_);
lean_dec(v___x_3355_);
v___x_3361_ = l_Subarray_drop___redArg(v_left_3330_, v___x_3351_);
lean_dec(v___x_3351_);
v___x_3362_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3363_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3361_, v___x_3362_);
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3360_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3359_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; 
lean_dec(v___x_3355_);
lean_dec(v___x_3351_);
v___x_3366_ = lean_nat_add(v_i_3332_, v___x_3352_);
lean_dec(v_i_3332_);
v_i_3332_ = v___x_3366_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(lean_object* v_left_3369_, lean_object* v_right_3370_){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_unsigned_to_nat(0u);
v___x_3372_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(v_left_3369_, v_right_3370_, v___x_3371_);
return v___x_3372_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = lean_box(0);
v___x_3374_ = lean_unsigned_to_nat(16u);
v___x_3375_ = lean_mk_array(v___x_3374_, v___x_3373_);
return v___x_3375_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v_hist_3378_; 
v___x_3376_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0);
v___x_3377_ = lean_unsigned_to_nat(0u);
v_hist_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3378_, 0, v___x_3377_);
lean_ctor_set(v_hist_3378_, 1, v___x_3376_);
return v_hist_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_left_3379_, lean_object* v_right_3380_){
_start:
{
lean_object* v___x_3381_; lean_object* v_snd_3382_; lean_object* v_fst_3383_; lean_object* v_fst_3384_; lean_object* v_snd_3385_; lean_object* v___x_3386_; lean_object* v_snd_3387_; lean_object* v_fst_3388_; lean_object* v_fst_3389_; lean_object* v_snd_3390_; lean_object* v_start_3391_; lean_object* v_stop_3392_; lean_object* v___x_3393_; lean_object* v_hist_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v_start_3397_; lean_object* v_stop_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v_buckets_3401_; lean_object* v___x_3402_; lean_object* v___y_3404_; lean_object* v___x_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3381_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(v_left_3379_, v_right_3380_);
v_snd_3382_ = lean_ctor_get(v___x_3381_, 1);
lean_inc(v_snd_3382_);
v_fst_3383_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_fst_3383_);
lean_dec_ref(v___x_3381_);
v_fst_3384_ = lean_ctor_get(v_snd_3382_, 0);
lean_inc(v_fst_3384_);
v_snd_3385_ = lean_ctor_get(v_snd_3382_, 1);
lean_inc(v_snd_3385_);
lean_dec(v_snd_3382_);
v___x_3386_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(v_fst_3384_, v_snd_3385_);
v_snd_3387_ = lean_ctor_get(v___x_3386_, 1);
lean_inc(v_snd_3387_);
v_fst_3388_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_fst_3388_);
lean_dec_ref(v___x_3386_);
v_fst_3389_ = lean_ctor_get(v_snd_3387_, 0);
lean_inc(v_fst_3389_);
v_snd_3390_ = lean_ctor_get(v_snd_3387_, 1);
lean_inc(v_snd_3390_);
lean_dec(v_snd_3387_);
v_start_3391_ = lean_ctor_get(v_fst_3388_, 1);
v_stop_3392_ = lean_ctor_get(v_fst_3388_, 2);
v___x_3393_ = lean_unsigned_to_nat(0u);
v_hist_3394_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1);
v___x_3395_ = lean_nat_sub(v_stop_3392_, v_start_3391_);
v___x_3396_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v___x_3395_, v_fst_3389_, v___x_3395_, v_fst_3388_, v___x_3393_, v_hist_3394_);
v_start_3397_ = lean_ctor_get(v_fst_3389_, 1);
v_stop_3398_ = lean_ctor_get(v_fst_3389_, 2);
v___x_3399_ = lean_nat_sub(v_stop_3398_, v_start_3397_);
v___x_3400_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v___x_3399_, v___x_3399_, v_fst_3389_, v___x_3395_, v___x_3393_, v___x_3396_);
lean_dec(v___x_3395_);
lean_dec(v___x_3399_);
v_buckets_3401_ = lean_ctor_get(v___x_3400_, 1);
lean_inc_ref(v_buckets_3401_);
lean_dec_ref(v___x_3400_);
v___x_3402_ = lean_box(0);
v___x_3430_ = lean_box(0);
v___x_3431_ = lean_array_get_size(v_buckets_3401_);
v___x_3432_ = lean_nat_dec_lt(v___x_3393_, v___x_3431_);
if (v___x_3432_ == 0)
{
lean_dec_ref(v_buckets_3401_);
v___y_3404_ = v___x_3430_;
goto v___jp_3403_;
}
else
{
size_t v___x_3433_; size_t v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = lean_usize_of_nat(v___x_3431_);
v___x_3434_ = ((size_t)0ULL);
v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_buckets_3401_, v___x_3433_, v___x_3434_, v___x_3430_);
lean_dec_ref(v_buckets_3401_);
v___y_3404_ = v___x_3435_;
goto v___jp_3403_;
}
v___jp_3403_:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v___y_3404_, v___x_3402_);
lean_dec(v___y_3404_);
if (lean_obj_tag(v___x_3405_) == 1)
{
lean_object* v_val_3406_; lean_object* v_snd_3407_; lean_object* v_snd_3408_; lean_object* v_fst_3409_; lean_object* v_fst_3410_; lean_object* v_snd_3411_; lean_object* v___x_3412_; lean_object* v_fst_3413_; lean_object* v_snd_3414_; lean_object* v___x_3415_; lean_object* v_fst_3416_; lean_object* v_snd_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_val_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_val_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v_snd_3407_ = lean_ctor_get(v_val_3406_, 1);
lean_inc(v_snd_3407_);
lean_dec(v_val_3406_);
v_snd_3408_ = lean_ctor_get(v_snd_3407_, 1);
lean_inc(v_snd_3408_);
v_fst_3409_ = lean_ctor_get(v_snd_3407_, 0);
lean_inc(v_fst_3409_);
lean_dec(v_snd_3407_);
v_fst_3410_ = lean_ctor_get(v_snd_3408_, 0);
lean_inc(v_fst_3410_);
v_snd_3411_ = lean_ctor_get(v_snd_3408_, 1);
lean_inc(v_snd_3411_);
lean_dec(v_snd_3408_);
v___x_3412_ = l_Subarray_split___redArg(v_fst_3388_, v_fst_3410_);
lean_dec(v_fst_3410_);
v_fst_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_fst_3413_);
v_snd_3414_ = lean_ctor_get(v___x_3412_, 1);
lean_inc(v_snd_3414_);
lean_dec_ref(v___x_3412_);
v___x_3415_ = l_Subarray_split___redArg(v_fst_3389_, v_snd_3411_);
lean_dec(v_snd_3411_);
v_fst_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_fst_3416_);
v_snd_3417_ = lean_ctor_get(v___x_3415_, 1);
lean_inc(v_snd_3417_);
lean_dec_ref(v___x_3415_);
v___x_3418_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_fst_3413_, v_fst_3416_);
v___x_3419_ = l_Array_append___redArg(v_fst_3383_, v___x_3418_);
lean_dec_ref(v___x_3418_);
v___x_3420_ = lean_unsigned_to_nat(1u);
v___x_3421_ = lean_mk_empty_array_with_capacity(v___x_3420_);
v___x_3422_ = lean_array_push(v___x_3421_, v_fst_3409_);
v___x_3423_ = l_Array_append___redArg(v___x_3419_, v___x_3422_);
lean_dec_ref(v___x_3422_);
v___x_3424_ = l_Subarray_drop___redArg(v_snd_3414_, v___x_3420_);
v___x_3425_ = l_Subarray_drop___redArg(v_snd_3417_, v___x_3420_);
v___x_3426_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3424_, v___x_3425_);
v___x_3427_ = l_Array_append___redArg(v___x_3423_, v___x_3426_);
lean_dec_ref(v___x_3426_);
v___x_3428_ = l_Array_append___redArg(v___x_3427_, v_snd_3390_);
lean_dec(v_snd_3390_);
return v___x_3428_;
}
else
{
lean_object* v___x_3429_; 
lean_dec(v___x_3405_);
lean_dec(v_fst_3389_);
lean_dec(v_fst_3388_);
v___x_3429_ = l_Array_append___redArg(v_fst_3383_, v_snd_3390_);
lean_dec(v_snd_3390_);
return v___x_3429_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3436_, size_t v_i_3437_, lean_object* v_bs_3438_){
_start:
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_usize_dec_lt(v_i_3437_, v_sz_3436_);
if (v___x_3439_ == 0)
{
return v_bs_3438_;
}
else
{
lean_object* v_v_3440_; lean_object* v___x_3441_; lean_object* v_bs_x27_3442_; uint8_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; size_t v___x_3446_; size_t v___x_3447_; lean_object* v___x_3448_; 
v_v_3440_ = lean_array_uget(v_bs_3438_, v_i_3437_);
v___x_3441_ = lean_unsigned_to_nat(0u);
v_bs_x27_3442_ = lean_array_uset(v_bs_3438_, v_i_3437_, v___x_3441_);
v___x_3443_ = 1;
v___x_3444_ = lean_box(v___x_3443_);
v___x_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
lean_ctor_set(v___x_3445_, 1, v_v_3440_);
v___x_3446_ = ((size_t)1ULL);
v___x_3447_ = lean_usize_add(v_i_3437_, v___x_3446_);
v___x_3448_ = lean_array_uset(v_bs_x27_3442_, v_i_3437_, v___x_3445_);
v_i_3437_ = v___x_3447_;
v_bs_3438_ = v___x_3448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3450_, lean_object* v_i_3451_, lean_object* v_bs_3452_){
_start:
{
size_t v_sz_boxed_3453_; size_t v_i_boxed_3454_; lean_object* v_res_3455_; 
v_sz_boxed_3453_ = lean_unbox_usize(v_sz_3450_);
lean_dec(v_sz_3450_);
v_i_boxed_3454_ = lean_unbox_usize(v_i_3451_);
lean_dec(v_i_3451_);
v_res_3455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3453_, v_i_boxed_3454_, v_bs_3452_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3463_, lean_object* v_edited_3464_){
_start:
{
lean_object* v_i_3465_; lean_object* v___x_3466_; uint8_t v___x_3467_; 
v_i_3465_ = lean_unsigned_to_nat(0u);
v___x_3466_ = lean_array_get_size(v_original_3463_);
v___x_3467_ = lean_nat_dec_lt(v_i_3465_, v___x_3466_);
if (v___x_3467_ == 0)
{
size_t v_sz_3468_; size_t v___x_3469_; lean_object* v___x_3470_; 
lean_dec_ref(v_original_3463_);
v_sz_3468_ = lean_array_size(v_edited_3464_);
v___x_3469_ = ((size_t)0ULL);
v___x_3470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3468_, v___x_3469_, v_edited_3464_);
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; uint8_t v___x_3472_; 
v___x_3471_ = lean_array_get_size(v_edited_3464_);
v___x_3472_ = lean_nat_dec_lt(v_i_3465_, v___x_3471_);
if (v___x_3472_ == 0)
{
size_t v_sz_3473_; size_t v___x_3474_; lean_object* v___x_3475_; 
lean_dec_ref(v_edited_3464_);
v_sz_3473_ = lean_array_size(v_original_3463_);
v___x_3474_ = ((size_t)0ULL);
v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3473_, v___x_3474_, v_original_3463_);
return v___x_3475_;
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v_ds_3478_; lean_object* v___x_3479_; size_t v_sz_3480_; size_t v___x_3481_; lean_object* v___x_3482_; lean_object* v_snd_3483_; lean_object* v_fst_3484_; lean_object* v_fst_3485_; lean_object* v_snd_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3505_; 
lean_inc_ref(v_original_3463_);
v___x_3476_ = l_Array_toSubarray___redArg(v_original_3463_, v_i_3465_, v___x_3466_);
lean_inc_ref(v_edited_3464_);
v___x_3477_ = l_Array_toSubarray___redArg(v_edited_3464_, v_i_3465_, v___x_3471_);
v_ds_3478_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3476_, v___x_3477_);
v___x_3479_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3480_ = lean_array_size(v_ds_3478_);
v___x_3481_ = ((size_t)0ULL);
v___x_3482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_3471_, v_edited_3464_, v___x_3466_, v_original_3463_, v_ds_3478_, v_sz_3480_, v___x_3481_, v___x_3479_);
lean_dec_ref(v_ds_3478_);
v_snd_3483_ = lean_ctor_get(v___x_3482_, 1);
lean_inc(v_snd_3483_);
v_fst_3484_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_fst_3484_);
lean_dec_ref(v___x_3482_);
v_fst_3485_ = lean_ctor_get(v_snd_3483_, 0);
v_snd_3486_ = lean_ctor_get(v_snd_3483_, 1);
v_isSharedCheck_3505_ = !lean_is_exclusive(v_snd_3483_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3488_ = v_snd_3483_;
v_isShared_3489_ = v_isSharedCheck_3505_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_snd_3486_);
lean_inc(v_fst_3485_);
lean_dec(v_snd_3483_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3505_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 1, v_fst_3485_);
lean_ctor_set(v___x_3488_, 0, v_fst_3484_);
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_fst_3484_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_fst_3485_);
v___x_3491_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; lean_object* v_fst_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3502_; 
v___x_3492_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3466_, v_original_3463_, v___x_3491_);
lean_dec_ref(v_original_3463_);
v_fst_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; 
v_unused_3503_ = lean_ctor_get(v___x_3492_, 1);
lean_dec(v_unused_3503_);
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3502_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_fst_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3502_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 1, v_snd_3486_);
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_fst_3493_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_snd_3486_);
v___x_3498_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3499_; lean_object* v_fst_3500_; 
v___x_3499_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3471_, v_edited_3464_, v___x_3498_);
lean_dec_ref(v_edited_3464_);
v_fst_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_fst_3500_);
lean_dec_ref(v___x_3499_);
return v_fst_3500_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3506_, lean_object* v_x_3507_, lean_object* v_x_3508_){
_start:
{
if (lean_obj_tag(v_x_3507_) == 0)
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = l_List_reverse___redArg(v_x_3508_);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
return v___x_3511_;
}
else
{
lean_object* v_head_3512_; lean_object* v_tail_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3522_; 
v_head_3512_ = lean_ctor_get(v_x_3507_, 0);
v_tail_3513_ = lean_ctor_get(v_x_3507_, 1);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_x_3507_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3515_ = v_x_3507_;
v_isShared_3516_ = v_isSharedCheck_3522_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_tail_3513_);
lean_inc(v_head_3512_);
lean_dec(v_x_3507_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3522_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
v___x_3517_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3512_, v___y_3506_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 1, v_x_3508_);
lean_ctor_set(v___x_3515_, 0, v___x_3517_);
v___x_3519_ = v___x_3515_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_x_3508_);
v___x_3519_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
v_x_3507_ = v_tail_3513_;
v_x_3508_ = v___x_3519_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3523_, lean_object* v_x_3524_, lean_object* v_x_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3523_, v_x_3524_, v_x_3525_);
lean_dec(v___y_3523_);
return v_res_3527_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3534_ = l_Lean_stringToMessageData(v___x_3533_);
return v___x_3534_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = l_Lean_MessageLog_empty;
v___x_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_){
_start:
{
lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3548_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
lean_inc(v_x_3544_);
v___x_3549_ = l_Lean_Syntax_isOfKind(v_x_3544_, v___x_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; 
lean_dec(v_x_3544_);
v___x_3550_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3550_;
}
else
{
lean_object* v___x_3551_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; uint8_t v___y_3592_; uint8_t v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; uint8_t v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; uint8_t v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v_dc_x3f_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v___x_3551_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3800_ = lean_unsigned_to_nat(0u);
v___x_3801_ = l_Lean_Syntax_getArg(v_x_3544_, v___x_3800_);
v___x_3802_ = l_Lean_Syntax_isNone(v___x_3801_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3803_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3801_);
v___x_3804_ = l_Lean_Syntax_matchesNull(v___x_3801_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3805_; 
lean_dec(v___x_3801_);
lean_dec(v_x_3544_);
v___x_3805_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3805_;
}
else
{
lean_object* v_dc_x3f_3806_; 
v_dc_x3f_3806_ = l_Lean_Syntax_getArg(v___x_3801_, v___x_3800_);
lean_dec(v___x_3801_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3809_; uint8_t v___x_3810_; 
v___x_3809_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3806_);
v___x_3810_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3806_, v___x_3809_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; 
lean_dec(v_dc_x3f_3806_);
lean_dec(v_x_3544_);
v___x_3811_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3811_;
}
else
{
goto v___jp_3807_;
}
}
else
{
goto v___jp_3807_;
}
v___jp_3807_:
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v_dc_x3f_3806_);
v_dc_x3f_3781_ = v___x_3808_;
v___y_3782_ = v_a_3545_;
v___y_3783_ = v_a_3546_;
goto v___jp_3780_;
}
}
}
else
{
lean_object* v___x_3812_; 
lean_dec(v___x_3801_);
v___x_3812_ = lean_box(0);
v_dc_x3f_3781_ = v___x_3812_;
v___y_3782_ = v_a_3545_;
v___y_3783_ = v_a_3546_;
goto v___jp_3780_;
}
v___jp_3552_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3558_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3559_ = l_Lean_stringToMessageData(v___y_3557_);
v___x_3560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3558_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3555_, v___x_3560_, v___y_3553_, v___y_3554_);
lean_dec(v___y_3555_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3581_; 
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3581_ == 0)
{
lean_object* v_unused_3582_; 
v_unused_3582_ = lean_ctor_get(v___x_3561_, 0);
lean_dec(v_unused_3582_);
v___x_3563_ = v___x_3561_;
v_isShared_3564_ = v_isSharedCheck_3581_;
goto v_resetjp_3562_;
}
else
{
lean_dec(v___x_3561_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3581_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_Elab_Command_getRef___redArg(v___y_3553_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3565_, 1);
v___x_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3551_);
lean_ctor_set(v___x_3567_, 1, v___y_3556_);
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v_a_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set_tag(v___x_3563_, 10);
lean_ctor_set(v___x_3563_, 0, v___x_3568_);
v___x_3570_ = v___x_3563_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3570_, v___y_3553_, v___y_3554_);
return v___x_3571_;
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
lean_del_object(v___x_3563_);
lean_dec_ref(v___y_3556_);
v_a_3573_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3565_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3565_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3556_);
return v___x_3561_;
}
}
v___jp_3583_:
{
if (v___y_3592_ == 0)
{
lean_object* v___x_3593_; lean_object* v_env_3594_; lean_object* v_scopes_3595_; lean_object* v_usedQuotCtxts_3596_; lean_object* v_nextMacroScope_3597_; lean_object* v_maxRecDepth_3598_; lean_object* v_ngen_3599_; lean_object* v_auxDeclNGen_3600_; lean_object* v_infoState_3601_; lean_object* v_traceState_3602_; lean_object* v_snapshotTasks_3603_; lean_object* v_prevLinterStates_3604_; lean_object* v_codeQualityEntryTasks_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v___y_3585_);
v___x_3593_ = lean_st_ref_take(v___y_3587_);
v_env_3594_ = lean_ctor_get(v___x_3593_, 0);
v_scopes_3595_ = lean_ctor_get(v___x_3593_, 2);
v_usedQuotCtxts_3596_ = lean_ctor_get(v___x_3593_, 3);
v_nextMacroScope_3597_ = lean_ctor_get(v___x_3593_, 4);
v_maxRecDepth_3598_ = lean_ctor_get(v___x_3593_, 5);
v_ngen_3599_ = lean_ctor_get(v___x_3593_, 6);
v_auxDeclNGen_3600_ = lean_ctor_get(v___x_3593_, 7);
v_infoState_3601_ = lean_ctor_get(v___x_3593_, 8);
v_traceState_3602_ = lean_ctor_get(v___x_3593_, 9);
v_snapshotTasks_3603_ = lean_ctor_get(v___x_3593_, 10);
v_prevLinterStates_3604_ = lean_ctor_get(v___x_3593_, 11);
v_codeQualityEntryTasks_3605_ = lean_ctor_get(v___x_3593_, 12);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3630_ == 0)
{
lean_object* v_unused_3631_; 
v_unused_3631_ = lean_ctor_get(v___x_3593_, 1);
lean_dec(v_unused_3631_);
v___x_3607_ = v___x_3593_;
v_isShared_3608_ = v_isSharedCheck_3630_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3605_);
lean_inc(v_prevLinterStates_3604_);
lean_inc(v_snapshotTasks_3603_);
lean_inc(v_traceState_3602_);
lean_inc(v_infoState_3601_);
lean_inc(v_auxDeclNGen_3600_);
lean_inc(v_ngen_3599_);
lean_inc(v_maxRecDepth_3598_);
lean_inc(v_nextMacroScope_3597_);
lean_inc(v_usedQuotCtxts_3596_);
lean_inc(v_scopes_3595_);
lean_inc(v_env_3594_);
lean_dec(v___x_3593_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3630_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 1, v___y_3591_);
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_env_3594_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v___y_3591_);
lean_ctor_set(v_reuseFailAlloc_3629_, 2, v_scopes_3595_);
lean_ctor_set(v_reuseFailAlloc_3629_, 3, v_usedQuotCtxts_3596_);
lean_ctor_set(v_reuseFailAlloc_3629_, 4, v_nextMacroScope_3597_);
lean_ctor_set(v_reuseFailAlloc_3629_, 5, v_maxRecDepth_3598_);
lean_ctor_set(v_reuseFailAlloc_3629_, 6, v_ngen_3599_);
lean_ctor_set(v_reuseFailAlloc_3629_, 7, v_auxDeclNGen_3600_);
lean_ctor_set(v_reuseFailAlloc_3629_, 8, v_infoState_3601_);
lean_ctor_set(v_reuseFailAlloc_3629_, 9, v_traceState_3602_);
lean_ctor_set(v_reuseFailAlloc_3629_, 10, v_snapshotTasks_3603_);
lean_ctor_set(v_reuseFailAlloc_3629_, 11, v_prevLinterStates_3604_);
lean_ctor_set(v_reuseFailAlloc_3629_, 12, v_codeQualityEntryTasks_3605_);
v___x_3610_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v_scopes_3614_; lean_object* v___x_3615_; lean_object* v_opts_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v___x_3611_ = lean_st_ref_put(v___y_3587_, v___x_3610_);
v___x_3612_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3613_ = lean_st_ref_get(v___y_3587_);
v_scopes_3614_ = lean_ctor_get(v___x_3613_, 2);
lean_inc(v_scopes_3614_);
lean_dec(v___x_3613_);
v___x_3615_ = l_List_head_x21___redArg(v___x_3612_, v_scopes_3614_);
lean_dec(v_scopes_3614_);
v_opts_3616_ = lean_ctor_get(v___x_3615_, 1);
lean_inc_ref(v_opts_3616_);
lean_dec(v___x_3615_);
v___x_3617_ = l_Lean_guard__msgs_diff;
v___x_3618_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3616_, v___x_3617_);
lean_dec_ref(v_opts_3616_);
if (v___x_3618_ == 0)
{
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3586_);
lean_inc_ref(v___y_3590_);
v___y_3553_ = v___y_3584_;
v___y_3554_ = v___y_3587_;
v___y_3555_ = v___y_3589_;
v___y_3556_ = v___y_3590_;
v___y_3557_ = v___y_3590_;
goto v___jp_3552_;
}
else
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3619_ = lean_string_utf8_byte_size(v___y_3586_);
lean_inc(v___y_3588_);
lean_inc_ref(v___y_3586_);
v___x_3620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3620_, 0, v___y_3586_);
lean_ctor_set(v___x_3620_, 1, v___y_3588_);
lean_ctor_set(v___x_3620_, 2, v___x_3619_);
v___x_3621_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
v___x_3622_ = lean_mk_empty_array_with_capacity(v___y_3588_);
lean_inc_ref(v___x_3622_);
v___x_3623_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3586_, v___x_3620_, v___x_3619_, v___x_3621_, v___x_3622_);
lean_dec_ref_known(v___x_3620_, 3);
v___x_3624_ = lean_string_utf8_byte_size(v___y_3590_);
lean_inc_ref_n(v___y_3590_, 2);
v___x_3625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3625_, 0, v___y_3590_);
lean_ctor_set(v___x_3625_, 1, v___y_3588_);
lean_ctor_set(v___x_3625_, 2, v___x_3624_);
v___x_3626_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3590_, v___x_3625_, v___x_3624_, v___x_3621_, v___x_3622_);
lean_dec_ref_known(v___x_3625_, 3);
v___x_3627_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3623_, v___x_3626_);
v___x_3628_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3627_);
lean_dec_ref(v___x_3627_);
v___y_3553_ = v___y_3584_;
v___y_3554_ = v___y_3587_;
v___y_3555_ = v___y_3589_;
v___y_3556_ = v___y_3590_;
v___y_3557_ = v___x_3628_;
goto v___jp_3552_;
}
}
}
}
else
{
lean_object* v___x_3632_; lean_object* v_env_3633_; lean_object* v_scopes_3634_; lean_object* v_usedQuotCtxts_3635_; lean_object* v_nextMacroScope_3636_; lean_object* v_maxRecDepth_3637_; lean_object* v_ngen_3638_; lean_object* v_auxDeclNGen_3639_; lean_object* v_infoState_3640_; lean_object* v_traceState_3641_; lean_object* v_snapshotTasks_3642_; lean_object* v_prevLinterStates_3643_; lean_object* v_codeQualityEntryTasks_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3654_; 
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3586_);
v___x_3632_ = lean_st_ref_take(v___y_3587_);
v_env_3633_ = lean_ctor_get(v___x_3632_, 0);
v_scopes_3634_ = lean_ctor_get(v___x_3632_, 2);
v_usedQuotCtxts_3635_ = lean_ctor_get(v___x_3632_, 3);
v_nextMacroScope_3636_ = lean_ctor_get(v___x_3632_, 4);
v_maxRecDepth_3637_ = lean_ctor_get(v___x_3632_, 5);
v_ngen_3638_ = lean_ctor_get(v___x_3632_, 6);
v_auxDeclNGen_3639_ = lean_ctor_get(v___x_3632_, 7);
v_infoState_3640_ = lean_ctor_get(v___x_3632_, 8);
v_traceState_3641_ = lean_ctor_get(v___x_3632_, 9);
v_snapshotTasks_3642_ = lean_ctor_get(v___x_3632_, 10);
v_prevLinterStates_3643_ = lean_ctor_get(v___x_3632_, 11);
v_codeQualityEntryTasks_3644_ = lean_ctor_get(v___x_3632_, 12);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3654_ == 0)
{
lean_object* v_unused_3655_; 
v_unused_3655_ = lean_ctor_get(v___x_3632_, 1);
lean_dec(v_unused_3655_);
v___x_3646_ = v___x_3632_;
v_isShared_3647_ = v_isSharedCheck_3654_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3644_);
lean_inc(v_prevLinterStates_3643_);
lean_inc(v_snapshotTasks_3642_);
lean_inc(v_traceState_3641_);
lean_inc(v_infoState_3640_);
lean_inc(v_auxDeclNGen_3639_);
lean_inc(v_ngen_3638_);
lean_inc(v_maxRecDepth_3637_);
lean_inc(v_nextMacroScope_3636_);
lean_inc(v_usedQuotCtxts_3635_);
lean_inc(v_scopes_3634_);
lean_inc(v_env_3633_);
lean_dec(v___x_3632_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3654_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3648_ = lean_box(0);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 1, v___y_3585_);
v___x_3650_ = v___x_3646_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_env_3633_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___y_3585_);
lean_ctor_set(v_reuseFailAlloc_3653_, 2, v_scopes_3634_);
lean_ctor_set(v_reuseFailAlloc_3653_, 3, v_usedQuotCtxts_3635_);
lean_ctor_set(v_reuseFailAlloc_3653_, 4, v_nextMacroScope_3636_);
lean_ctor_set(v_reuseFailAlloc_3653_, 5, v_maxRecDepth_3637_);
lean_ctor_set(v_reuseFailAlloc_3653_, 6, v_ngen_3638_);
lean_ctor_set(v_reuseFailAlloc_3653_, 7, v_auxDeclNGen_3639_);
lean_ctor_set(v_reuseFailAlloc_3653_, 8, v_infoState_3640_);
lean_ctor_set(v_reuseFailAlloc_3653_, 9, v_traceState_3641_);
lean_ctor_set(v_reuseFailAlloc_3653_, 10, v_snapshotTasks_3642_);
lean_ctor_set(v_reuseFailAlloc_3653_, 11, v_prevLinterStates_3643_);
lean_ctor_set(v_reuseFailAlloc_3653_, 12, v_codeQualityEntryTasks_3644_);
v___x_3650_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = lean_st_ref_put(v___y_3587_, v___x_3650_);
v___x_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3648_);
return v___x_3652_;
}
}
}
}
v___jp_3656_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v_a_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v_str_3679_; lean_object* v_startInclusive_3680_; lean_object* v_endExclusive_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3696_; 
v___x_3669_ = l_Lean_MessageLog_toList(v___y_3660_);
lean_dec(v___y_3660_);
v___x_3670_ = lean_box(0);
v___x_3671_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3668_, v___x_3669_, v___x_3670_);
lean_dec(v___y_3668_);
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref(v___x_3671_);
v___x_3673_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3667_, v_a_3672_);
v___x_3674_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4));
v___x_3675_ = l_String_intercalate(v___x_3674_, v___x_3673_);
v___x_3676_ = lean_string_utf8_byte_size(v___x_3675_);
lean_inc(v___y_3664_);
v___x_3677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3675_);
lean_ctor_set(v___x_3677_, 1, v___y_3664_);
lean_ctor_set(v___x_3677_, 2, v___x_3676_);
v___x_3678_ = l_String_Slice_trimAscii(v___x_3677_);
v_str_3679_ = lean_ctor_get(v___x_3678_, 0);
v_startInclusive_3680_ = lean_ctor_get(v___x_3678_, 1);
v_endExclusive_3681_ = lean_ctor_get(v___x_3678_, 2);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3683_ = v___x_3678_;
v_isShared_3684_ = v_isSharedCheck_3696_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_endExclusive_3681_);
lean_inc(v_startInclusive_3680_);
lean_inc(v_str_3679_);
lean_dec(v___x_3678_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3696_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; 
v___x_3685_ = lean_string_utf8_extract_fast(v_str_3679_, v_startInclusive_3680_, v_endExclusive_3681_);
lean_dec(v_endExclusive_3681_);
lean_dec(v_startInclusive_3680_);
lean_dec_ref(v_str_3679_);
if (v___y_3657_ == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
lean_del_object(v___x_3683_);
lean_inc_ref(v___y_3662_);
v___x_3686_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3661_, v___y_3662_);
lean_inc_ref(v___x_3685_);
v___x_3687_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3661_, v___x_3685_);
v___x_3688_ = lean_string_dec_eq(v___x_3686_, v___x_3687_);
lean_dec_ref(v___x_3687_);
lean_dec_ref(v___x_3686_);
v___y_3584_ = v___y_3658_;
v___y_3585_ = v___y_3659_;
v___y_3586_ = v___y_3662_;
v___y_3587_ = v___y_3663_;
v___y_3588_ = v___y_3664_;
v___y_3589_ = v___y_3665_;
v___y_3590_ = v___x_3685_;
v___y_3591_ = v___y_3666_;
v___y_3592_ = v___x_3688_;
goto v___jp_3583_;
}
else
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
lean_inc_ref(v___x_3685_);
v___x_3689_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3661_, v___x_3685_);
lean_inc_ref(v___y_3662_);
v___x_3690_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3661_, v___y_3662_);
v___x_3691_ = lean_string_utf8_byte_size(v___x_3689_);
lean_inc(v___y_3664_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 2, v___x_3691_);
lean_ctor_set(v___x_3683_, 1, v___y_3664_);
lean_ctor_set(v___x_3683_, 0, v___x_3689_);
v___x_3693_ = v___x_3683_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v___y_3664_);
lean_ctor_set(v_reuseFailAlloc_3695_, 2, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
uint8_t v___x_3694_; 
v___x_3694_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3690_, v___x_3693_);
lean_dec_ref(v___x_3693_);
v___y_3584_ = v___y_3658_;
v___y_3585_ = v___y_3659_;
v___y_3586_ = v___y_3662_;
v___y_3587_ = v___y_3663_;
v___y_3588_ = v___y_3664_;
v___y_3589_ = v___y_3665_;
v___y_3590_ = v___x_3685_;
v___y_3591_ = v___y_3666_;
v___y_3592_ = v___x_3694_;
goto v___jp_3583_;
}
}
}
}
v___jp_3697_:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v_str_3708_; lean_object* v_startInclusive_3709_; lean_object* v_endExclusive_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3704_ = lean_unsigned_to_nat(0u);
v___x_3705_ = lean_string_utf8_byte_size(v___y_3703_);
v___x_3706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3706_, 0, v___y_3703_);
lean_ctor_set(v___x_3706_, 1, v___x_3704_);
lean_ctor_set(v___x_3706_, 2, v___x_3705_);
v___x_3707_ = l_String_Slice_trimAscii(v___x_3706_);
v_str_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc_ref(v_str_3708_);
v_startInclusive_3709_ = lean_ctor_get(v___x_3707_, 1);
lean_inc(v_startInclusive_3709_);
v_endExclusive_3710_ = lean_ctor_get(v___x_3707_, 2);
lean_inc(v_endExclusive_3710_);
lean_dec_ref(v___x_3707_);
v___x_3711_ = lean_string_utf8_extract_fast(v_str_3708_, v_startInclusive_3709_, v_endExclusive_3710_);
lean_dec(v_endExclusive_3710_);
lean_dec(v_startInclusive_3709_);
lean_dec_ref(v_str_3708_);
v___x_3712_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3711_);
v___x_3713_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3698_, v___y_3699_, v___y_3701_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v_filterFn_3715_; uint8_t v_whitespace_3716_; uint8_t v_ordering_3717_; uint8_t v_reportPositions_3718_; uint8_t v_substring_3719_; lean_object* v___x_3720_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v_filterFn_3715_ = lean_ctor_get(v_a_3714_, 0);
lean_inc_ref(v_filterFn_3715_);
v_whitespace_3716_ = lean_ctor_get_uint8(v_a_3714_, sizeof(void*)*1);
v_ordering_3717_ = lean_ctor_get_uint8(v_a_3714_, sizeof(void*)*1 + 1);
v_reportPositions_3718_ = lean_ctor_get_uint8(v_a_3714_, sizeof(void*)*1 + 2);
v_substring_3719_ = lean_ctor_get_uint8(v_a_3714_, sizeof(void*)*1 + 3);
lean_dec(v_a_3714_);
v___x_3720_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3700_, v___y_3699_, v___y_3701_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v_a_3725_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___x_3720_, 1);
v___x_3722_ = l_Lean_MessageLog_toList(v_a_3721_);
v___x_3723_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5);
v___x_3724_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3715_, v___x_3722_, v___x_3723_);
lean_dec(v___x_3722_);
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref(v___x_3724_);
if (v_reportPositions_3718_ == 0)
{
lean_object* v_fst_3726_; lean_object* v_snd_3727_; lean_object* v___x_3728_; 
v_fst_3726_ = lean_ctor_get(v_a_3725_, 0);
lean_inc(v_fst_3726_);
v_snd_3727_ = lean_ctor_get(v_a_3725_, 1);
lean_inc(v_snd_3727_);
lean_dec(v_a_3725_);
v___x_3728_ = lean_box(0);
v___y_3657_ = v_substring_3719_;
v___y_3658_ = v___y_3699_;
v___y_3659_ = v_snd_3727_;
v___y_3660_ = v_fst_3726_;
v___y_3661_ = v_whitespace_3716_;
v___y_3662_ = v___x_3712_;
v___y_3663_ = v___y_3701_;
v___y_3664_ = v___x_3704_;
v___y_3665_ = v___y_3702_;
v___y_3666_ = v_a_3721_;
v___y_3667_ = v_ordering_3717_;
v___y_3668_ = v___x_3728_;
goto v___jp_3656_;
}
else
{
lean_object* v_fst_3729_; lean_object* v_snd_3730_; uint8_t v___x_3731_; lean_object* v___x_3732_; 
v_fst_3729_ = lean_ctor_get(v_a_3725_, 0);
lean_inc(v_fst_3729_);
v_snd_3730_ = lean_ctor_get(v_a_3725_, 1);
lean_inc(v_snd_3730_);
lean_dec(v_a_3725_);
v___x_3731_ = 0;
v___x_3732_ = l_Lean_Syntax_getPos_x3f(v___y_3702_, v___x_3731_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_box(0);
v___y_3657_ = v_substring_3719_;
v___y_3658_ = v___y_3699_;
v___y_3659_ = v_snd_3730_;
v___y_3660_ = v_fst_3729_;
v___y_3661_ = v_whitespace_3716_;
v___y_3662_ = v___x_3712_;
v___y_3663_ = v___y_3701_;
v___y_3664_ = v___x_3704_;
v___y_3665_ = v___y_3702_;
v___y_3666_ = v_a_3721_;
v___y_3667_ = v_ordering_3717_;
v___y_3668_ = v___x_3733_;
goto v___jp_3656_;
}
else
{
lean_object* v_val_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3744_; 
v_val_3734_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3736_ = v___x_3732_;
v_isShared_3737_ = v_isSharedCheck_3744_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_val_3734_);
lean_dec(v___x_3732_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3744_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v_fileMap_3738_; lean_object* v___x_3739_; lean_object* v_line_3740_; lean_object* v___x_3742_; 
v_fileMap_3738_ = lean_ctor_get(v___y_3699_, 1);
lean_inc_ref(v_fileMap_3738_);
v___x_3739_ = l_Lean_FileMap_toPosition(v_fileMap_3738_, v_val_3734_);
lean_dec(v_val_3734_);
v_line_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_line_3740_);
lean_dec_ref(v___x_3739_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v_line_3740_);
v___x_3742_ = v___x_3736_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_line_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
v___y_3657_ = v_substring_3719_;
v___y_3658_ = v___y_3699_;
v___y_3659_ = v_snd_3730_;
v___y_3660_ = v_fst_3729_;
v___y_3661_ = v_whitespace_3716_;
v___y_3662_ = v___x_3712_;
v___y_3663_ = v___y_3701_;
v___y_3664_ = v___x_3704_;
v___y_3665_ = v___y_3702_;
v___y_3666_ = v_a_3721_;
v___y_3667_ = v_ordering_3717_;
v___y_3668_ = v___x_3742_;
goto v___jp_3656_;
}
}
}
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec_ref(v_filterFn_3715_);
lean_dec_ref(v___x_3712_);
lean_dec(v___y_3702_);
v_a_3745_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3720_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3720_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_dec_ref(v___x_3712_);
lean_dec(v___y_3702_);
lean_dec(v___y_3700_);
v_a_3753_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3713_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3713_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
v___jp_3761_:
{
if (lean_obj_tag(v___y_3763_) == 0)
{
lean_object* v___x_3768_; 
v___x_3768_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_3698_ = v___y_3767_;
v___y_3699_ = v___y_3762_;
v___y_3700_ = v___y_3764_;
v___y_3701_ = v___y_3765_;
v___y_3702_ = v___y_3766_;
v___y_3703_ = v___x_3768_;
goto v___jp_3697_;
}
else
{
lean_object* v_val_3769_; lean_object* v___x_3770_; 
v_val_3769_ = lean_ctor_get(v___y_3763_, 0);
lean_inc(v_val_3769_);
lean_dec_ref_known(v___y_3763_, 1);
v___x_3770_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3769_, v___y_3762_, v___y_3765_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref_known(v___x_3770_, 1);
v___y_3698_ = v___y_3767_;
v___y_3699_ = v___y_3762_;
v___y_3700_ = v___y_3764_;
v___y_3701_ = v___y_3765_;
v___y_3702_ = v___y_3766_;
v___y_3703_ = v_a_3771_;
goto v___jp_3697_;
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec(v___y_3767_);
lean_dec(v___y_3766_);
lean_dec(v___y_3764_);
v_a_3772_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3770_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3770_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
v___jp_3780_:
{
lean_object* v___x_3784_; lean_object* v_tk_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3784_ = lean_unsigned_to_nat(1u);
v_tk_3785_ = l_Lean_Syntax_getArg(v_x_3544_, v___x_3784_);
v___x_3786_ = lean_unsigned_to_nat(2u);
v___x_3787_ = l_Lean_Syntax_getArg(v_x_3544_, v___x_3786_);
v___x_3788_ = lean_unsigned_to_nat(4u);
v___x_3789_ = l_Lean_Syntax_getArg(v_x_3544_, v___x_3788_);
lean_dec(v_x_3544_);
v___x_3790_ = l_Lean_Syntax_getOptional_x3f(v___x_3787_);
lean_dec(v___x_3787_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v___x_3791_; 
v___x_3791_ = lean_box(0);
v___y_3762_ = v___y_3782_;
v___y_3763_ = v_dc_x3f_3781_;
v___y_3764_ = v___x_3789_;
v___y_3765_ = v___y_3783_;
v___y_3766_ = v_tk_3785_;
v___y_3767_ = v___x_3791_;
goto v___jp_3761_;
}
else
{
lean_object* v_val_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
v_val_3792_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3790_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_val_3792_);
lean_dec(v___x_3790_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_val_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
v___y_3762_ = v___y_3782_;
v___y_3763_ = v_dc_x3f_3781_;
v___y_3764_ = v___x_3789_;
v___y_3765_ = v___y_3783_;
v___y_3766_ = v_tk_3785_;
v___y_3767_ = v___x_3797_;
goto v___jp_3761_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3813_, v_a_3814_, v_a_3815_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3818_, lean_object* v_as_3819_, lean_object* v_as_x27_3820_, lean_object* v_b_3821_, lean_object* v_a_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v___x_3826_; 
v___x_3826_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3818_, v_as_x27_3820_, v_b_3821_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3827_, lean_object* v_as_3828_, lean_object* v_as_x27_3829_, lean_object* v_b_3830_, lean_object* v_a_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3827_, v_as_3828_, v_as_x27_3829_, v_b_3830_, v_a_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v_as_x27_3829_);
lean_dec(v_as_3828_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3836_, lean_object* v_x_3837_, lean_object* v_x_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3836_, v_x_3837_, v_x_3838_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3843_, lean_object* v_x_3844_, lean_object* v_x_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3843_, v_x_3844_, v_x_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3843_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3850_, v___y_3852_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3855_, v___y_3856_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3860_, lean_object* v___x_3861_, lean_object* v___x_3862_, lean_object* v_inst_3863_, lean_object* v_R_3864_, lean_object* v_a_3865_, lean_object* v_b_3866_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3860_, v___x_3861_, v___x_3862_, v_a_3865_, v_b_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3868_, lean_object* v___x_3869_, lean_object* v___x_3870_, lean_object* v_inst_3871_, lean_object* v_R_3872_, lean_object* v_a_3873_, lean_object* v_b_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3868_, v___x_3869_, v___x_3870_, v_inst_3871_, v_R_3872_, v_a_3873_, v_b_3874_);
lean_dec_ref(v___x_3869_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3876_, v___y_3878_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3881_, v___y_3882_, v___y_3883_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3886_, lean_object* v___x_3887_, lean_object* v___x_3888_, lean_object* v_inst_3889_, lean_object* v_R_3890_, lean_object* v_a_3891_, lean_object* v_b_3892_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3886_, v___x_3887_, v___x_3888_, v_a_3891_, v_b_3892_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3894_, lean_object* v___x_3895_, lean_object* v___x_3896_, lean_object* v_inst_3897_, lean_object* v_R_3898_, lean_object* v_a_3899_, lean_object* v_b_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3894_, v___x_3895_, v___x_3896_, v_inst_3897_, v_R_3898_, v_a_3899_, v_b_3900_);
lean_dec_ref(v___x_3895_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v___x_3902_, lean_object* v_original_3903_, lean_object* v_a_3904_, lean_object* v_inst_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_3902_, v_original_3903_, v_a_3904_, v_a_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___boxed(lean_object* v___x_3908_, lean_object* v_original_3909_, lean_object* v_a_3910_, lean_object* v_inst_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3908_, v_original_3909_, v_a_3910_, v_inst_3911_, v_a_3912_);
lean_dec_ref(v_a_3910_);
lean_dec_ref(v_original_3909_);
lean_dec(v___x_3908_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v___x_3914_, lean_object* v_edited_3915_, lean_object* v_a_3916_, lean_object* v_inst_3917_, lean_object* v_a_3918_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_3914_, v_edited_3915_, v_a_3916_, v_a_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v___x_3920_, lean_object* v_edited_3921_, lean_object* v_a_3922_, lean_object* v_inst_3923_, lean_object* v_a_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v___x_3920_, v_edited_3921_, v_a_3922_, v_inst_3923_, v_a_3924_);
lean_dec_ref(v_a_3922_);
lean_dec_ref(v_edited_3921_);
lean_dec(v___x_3920_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3926_, lean_object* v_original_3927_, lean_object* v_inst_3928_, lean_object* v_a_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3926_, v_original_3927_, v_a_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3931_, lean_object* v_original_3932_, lean_object* v_inst_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3931_, v_original_3932_, v_inst_3933_, v_a_3934_);
lean_dec_ref(v_original_3932_);
lean_dec(v___x_3931_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3936_, lean_object* v_edited_3937_, lean_object* v_inst_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3936_, v_edited_3937_, v_a_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3941_, lean_object* v_edited_3942_, lean_object* v_inst_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3941_, v_edited_3942_, v_inst_3943_, v_a_3944_);
lean_dec_ref(v_edited_3942_);
lean_dec(v___x_3941_);
return v_res_3945_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3946_, lean_object* v_inst_3947_, lean_object* v_R_3948_, lean_object* v_a_3949_, uint8_t v_b_3950_, lean_object* v_c_3951_){
_start:
{
uint8_t v___x_3952_; 
v___x_3952_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3946_, v_a_3949_, v_b_3950_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3953_, lean_object* v_inst_3954_, lean_object* v_R_3955_, lean_object* v_a_3956_, lean_object* v_b_3957_, lean_object* v_c_3958_){
_start:
{
uint8_t v_b_boxed_3959_; uint8_t v_res_3960_; lean_object* v_r_3961_; 
v_b_boxed_3959_ = lean_unbox(v_b_3957_);
v_res_3960_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3953_, v_inst_3954_, v_R_3955_, v_a_3956_, v_b_boxed_3959_, v_c_3958_);
lean_dec_ref(v_s_3953_);
v_r_3961_ = lean_box(v_res_3960_);
return v_r_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3962_, lean_object* v_ref_3963_, lean_object* v_msg_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3963_, v_msg_3964_, v___y_3965_, v___y_3966_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3969_, lean_object* v_ref_3970_, lean_object* v_msg_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3969_, v_ref_3970_, v_msg_3971_, v___y_3972_, v___y_3973_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v_ref_3970_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(lean_object* v_as_3976_, lean_object* v_as_x27_3977_, lean_object* v_b_3978_, lean_object* v_a_3979_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3977_, v_b_3978_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___boxed(lean_object* v_as_3981_, lean_object* v_as_x27_3982_, lean_object* v_b_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(v_as_3981_, v_as_x27_3982_, v_b_3983_, v_a_3984_);
lean_dec(v_as_x27_3982_);
lean_dec(v_as_3981_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(lean_object* v_lsize_3986_, lean_object* v_rsize_3987_, lean_object* v_histogram_3988_, lean_object* v_index_3989_, lean_object* v_val_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_histogram_3988_, v_index_3989_, v_val_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___boxed(lean_object* v_lsize_3992_, lean_object* v_rsize_3993_, lean_object* v_histogram_3994_, lean_object* v_index_3995_, lean_object* v_val_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(v_lsize_3992_, v_rsize_3993_, v_histogram_3994_, v_index_3995_, v_val_3996_);
lean_dec(v_rsize_3993_);
lean_dec(v_lsize_3992_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(lean_object* v_upperBound_3998_, lean_object* v___x_3999_, lean_object* v_fst_4000_, lean_object* v___x_4001_, lean_object* v_inst_4002_, lean_object* v_R_4003_, lean_object* v_a_4004_, lean_object* v_b_4005_, lean_object* v_c_4006_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3998_, v___x_3999_, v_fst_4000_, v___x_4001_, v_a_4004_, v_b_4005_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___boxed(lean_object* v_upperBound_4008_, lean_object* v___x_4009_, lean_object* v_fst_4010_, lean_object* v___x_4011_, lean_object* v_inst_4012_, lean_object* v_R_4013_, lean_object* v_a_4014_, lean_object* v_b_4015_, lean_object* v_c_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(v_upperBound_4008_, v___x_4009_, v_fst_4010_, v___x_4011_, v_inst_4012_, v_R_4013_, v_a_4014_, v_b_4015_, v_c_4016_);
lean_dec(v___x_4011_);
lean_dec_ref(v_fst_4010_);
lean_dec(v___x_4009_);
lean_dec(v_upperBound_4008_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(lean_object* v_lsize_4018_, lean_object* v_rsize_4019_, lean_object* v_histogram_4020_, lean_object* v_index_4021_, lean_object* v_val_4022_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_histogram_4020_, v_index_4021_, v_val_4022_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___boxed(lean_object* v_lsize_4024_, lean_object* v_rsize_4025_, lean_object* v_histogram_4026_, lean_object* v_index_4027_, lean_object* v_val_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(v_lsize_4024_, v_rsize_4025_, v_histogram_4026_, v_index_4027_, v_val_4028_);
lean_dec(v_rsize_4025_);
lean_dec(v_lsize_4024_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(lean_object* v_upperBound_4030_, lean_object* v_fst_4031_, lean_object* v___x_4032_, lean_object* v_fst_4033_, lean_object* v_inst_4034_, lean_object* v_R_4035_, lean_object* v_a_4036_, lean_object* v_b_4037_, lean_object* v_c_4038_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_4030_, v_fst_4031_, v___x_4032_, v_fst_4033_, v_a_4036_, v_b_4037_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___boxed(lean_object* v_upperBound_4040_, lean_object* v_fst_4041_, lean_object* v___x_4042_, lean_object* v_fst_4043_, lean_object* v_inst_4044_, lean_object* v_R_4045_, lean_object* v_a_4046_, lean_object* v_b_4047_, lean_object* v_c_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(v_upperBound_4040_, v_fst_4041_, v___x_4042_, v_fst_4043_, v_inst_4044_, v_R_4045_, v_a_4046_, v_b_4047_, v_c_4048_);
lean_dec_ref(v_fst_4043_);
lean_dec(v___x_4042_);
lean_dec_ref(v_fst_4041_);
lean_dec(v_upperBound_4040_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_4050_, lean_object* v_msg_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_4051_, v___y_4052_, v___y_4053_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_4056_, lean_object* v_msg_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_4056_, v_msg_4057_, v___y_4058_, v___y_4059_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(lean_object* v_00_u03b2_4062_, lean_object* v_m_4063_, lean_object* v_a_4064_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_4063_, v_a_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___boxed(lean_object* v_00_u03b2_4066_, lean_object* v_m_4067_, lean_object* v_a_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(v_00_u03b2_4066_, v_m_4067_, v_a_4068_);
lean_dec_ref(v_a_4068_);
lean_dec_ref(v_m_4067_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26(lean_object* v_00_u03b2_4070_, lean_object* v_m_4071_, lean_object* v_a_4072_, lean_object* v_b_4073_){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_m_4071_, v_a_4072_, v_b_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_4075_, lean_object* v_macroStack_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_4075_, v_macroStack_4076_, v___y_4078_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4081_, lean_object* v_macroStack_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4081_, v_macroStack_4082_, v___y_4083_, v___y_4084_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29(lean_object* v_inst_4087_, lean_object* v_R_4088_, lean_object* v_a_4089_, lean_object* v_b_4090_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v_a_4089_, v_b_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(lean_object* v_00_u03b2_4092_, lean_object* v_a_4093_, lean_object* v_x_4094_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_4093_, v_x_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___boxed(lean_object* v_00_u03b2_4096_, lean_object* v_a_4097_, lean_object* v_x_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(v_00_u03b2_4096_, v_a_4097_, v_x_4098_);
lean_dec(v_x_4098_);
lean_dec_ref(v_a_4097_);
return v_res_4099_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(lean_object* v_00_u03b2_4100_, lean_object* v_a_4101_, lean_object* v_x_4102_){
_start:
{
uint8_t v___x_4103_; 
v___x_4103_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_4101_, v_x_4102_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___boxed(lean_object* v_00_u03b2_4104_, lean_object* v_a_4105_, lean_object* v_x_4106_){
_start:
{
uint8_t v_res_4107_; lean_object* v_r_4108_; 
v_res_4107_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(v_00_u03b2_4104_, v_a_4105_, v_x_4106_);
lean_dec(v_x_4106_);
lean_dec_ref(v_a_4105_);
v_r_4108_ = lean_box(v_res_4107_);
return v_r_4108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38(lean_object* v_00_u03b2_4109_, lean_object* v_data_4110_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_data_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39(lean_object* v_00_u03b2_4112_, lean_object* v_a_4113_, lean_object* v_b_4114_, lean_object* v_x_4115_){
_start:
{
lean_object* v___x_4116_; 
v___x_4116_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_4113_, v_b_4114_, v_x_4115_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44(lean_object* v_00_u03b2_4117_, lean_object* v_i_4118_, lean_object* v_source_4119_, lean_object* v_target_4120_){
_start:
{
lean_object* v___x_4121_; 
v___x_4121_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v_i_4118_, v_source_4119_, v_target_4120_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4122_, lean_object* v_x_4123_, lean_object* v_x_4124_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_x_4123_, v_x_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4134_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4135_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
v___x_4136_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4137_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4138_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4134_, v___x_4135_, v___x_4136_, v___x_4137_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4167_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4168_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4169_ = l_Lean_addBuiltinDeclarationRanges(v___x_4167_, v___x_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4172_){
_start:
{
lean_object* v_doc_4174_; lean_object* v___x_4175_; 
v_doc_4174_ = lean_ctor_get(v___y_4172_, 1);
lean_inc_ref(v_doc_4174_);
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v_doc_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4176_);
lean_dec_ref(v___y_4176_);
return v_res_4178_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4179_, lean_object* v_a_4180_, uint8_t v_b_4181_){
_start:
{
lean_object* v_str_4182_; lean_object* v_startInclusive_4183_; lean_object* v_endExclusive_4184_; lean_object* v___x_4185_; uint8_t v_decide_4186_; 
v_str_4182_ = lean_ctor_get(v_s_4179_, 0);
v_startInclusive_4183_ = lean_ctor_get(v_s_4179_, 1);
v_endExclusive_4184_ = lean_ctor_get(v_s_4179_, 2);
v___x_4185_ = lean_nat_sub(v_endExclusive_4184_, v_startInclusive_4183_);
v_decide_4186_ = lean_nat_dec_eq(v_a_4180_, v___x_4185_);
lean_dec(v___x_4185_);
if (v_decide_4186_ == 0)
{
lean_object* v___x_4187_; uint32_t v___x_4188_; uint32_t v___x_4189_; uint8_t v___x_4190_; 
v___x_4187_ = lean_nat_add(v_startInclusive_4183_, v_a_4180_);
lean_dec(v_a_4180_);
v___x_4188_ = lean_string_utf8_get_fast(v_str_4182_, v___x_4187_);
v___x_4189_ = 10;
v___x_4190_ = lean_uint32_dec_eq(v___x_4188_, v___x_4189_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4191_ = lean_string_utf8_next_fast(v_str_4182_, v___x_4187_);
lean_dec(v___x_4187_);
v___x_4192_ = lean_nat_sub(v___x_4191_, v_startInclusive_4183_);
v_a_4180_ = v___x_4192_;
v_b_4181_ = v___x_4190_;
goto _start;
}
else
{
lean_dec(v___x_4187_);
return v___x_4190_;
}
}
else
{
lean_dec(v_a_4180_);
return v_b_4181_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4194_, lean_object* v_a_4195_, lean_object* v_b_4196_){
_start:
{
uint8_t v_b_boxed_4197_; uint8_t v_res_4198_; lean_object* v_r_4199_; 
v_b_boxed_4197_ = lean_unbox(v_b_4196_);
v_res_4198_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4194_, v_a_4195_, v_b_boxed_4197_);
lean_dec_ref(v_s_4194_);
v_r_4199_ = lean_box(v_res_4198_);
return v_r_4199_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4200_){
_start:
{
lean_object* v_searcher_4201_; uint8_t v___x_4202_; uint8_t v___x_4203_; 
v_searcher_4201_ = lean_unsigned_to_nat(0u);
v___x_4202_ = 0;
v___x_4203_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4200_, v_searcher_4201_, v___x_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4204_){
_start:
{
uint8_t v_res_4205_; lean_object* v_r_4206_; 
v_res_4205_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4204_);
lean_dec_ref(v_s_4204_);
v_r_4206_ = lean_box(v_res_4205_);
return v_r_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4218_, lean_object* v_fst_4219_, uint8_t v___x_4220_, lean_object* v_a_4221_, lean_object* v___x_4222_, lean_object* v___x_4223_, lean_object* v___x_4224_, lean_object* v___x_4225_, lean_object* v___x_4226_, lean_object* v___x_4227_, lean_object* v___x_4228_, lean_object* v___x_4229_, lean_object* v_snd_4230_, lean_object* v___x_4231_){
_start:
{
if (lean_obj_tag(v___x_4218_) == 1)
{
lean_object* v_val_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4294_; 
v_val_4233_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4235_ = v___x_4218_;
v_isShared_4236_ = v_isSharedCheck_4294_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_val_4233_);
lean_dec(v___x_4218_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4294_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4237_ = lean_unsigned_to_nat(0u);
v___x_4238_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4239_ = l_Lean_Syntax_setArg(v_fst_4219_, v___x_4237_, v___x_4238_);
v___x_4240_ = l_Lean_Syntax_getPos_x3f(v___x_4239_, v___x_4220_);
lean_dec(v___x_4239_);
if (lean_obj_tag(v___x_4240_) == 1)
{
lean_object* v_val_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4290_; 
lean_dec_ref(v___x_4231_);
v_val_4241_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4243_ = v___x_4240_;
v_isShared_4244_ = v_isSharedCheck_4290_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_val_4241_);
lean_dec(v___x_4240_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4290_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___y_4246_; lean_object* v___x_4272_; lean_object* v___x_4278_; uint8_t v___x_4279_; 
v___x_4272_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4230_);
v___x_4278_ = lean_string_utf8_byte_size(v___x_4272_);
v___x_4279_ = lean_nat_dec_eq(v___x_4278_, v___x_4237_);
if (v___x_4279_ == 0)
{
lean_object* v___x_4280_; lean_object* v___x_4281_; uint8_t v___x_4282_; 
v___x_4280_ = lean_string_length(v___x_4272_);
v___x_4281_ = lean_unsigned_to_nat(93u);
v___x_4282_ = lean_nat_dec_le(v___x_4280_, v___x_4281_);
if (v___x_4282_ == 0)
{
goto v___jp_4273_;
}
else
{
lean_object* v___x_4283_; uint8_t v___x_4284_; 
lean_inc_ref(v___x_4272_);
v___x_4283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4272_);
lean_ctor_set(v___x_4283_, 1, v___x_4237_);
lean_ctor_set(v___x_4283_, 2, v___x_4278_);
v___x_4284_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4283_);
lean_dec_ref_known(v___x_4283_, 3);
if (v___x_4284_ == 0)
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4285_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4286_ = lean_string_append(v___x_4285_, v___x_4272_);
lean_dec_ref(v___x_4272_);
v___x_4287_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4288_ = lean_string_append(v___x_4286_, v___x_4287_);
v___y_4246_ = v___x_4288_;
goto v___jp_4245_;
}
else
{
goto v___jp_4273_;
}
}
}
else
{
lean_object* v___x_4289_; 
lean_dec_ref(v___x_4272_);
v___x_4289_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_4246_ = v___x_4289_;
goto v___jp_4245_;
}
v___jp_4245_:
{
lean_object* v_toEditableDocumentCore_4247_; lean_object* v_meta_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4268_; 
v_toEditableDocumentCore_4247_ = lean_ctor_get(v_a_4221_, 0);
lean_inc_ref(v_toEditableDocumentCore_4247_);
v_meta_4248_ = lean_ctor_get(v_toEditableDocumentCore_4247_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v_toEditableDocumentCore_4247_);
if (v_isSharedCheck_4268_ == 0)
{
lean_object* v_unused_4269_; lean_object* v_unused_4270_; lean_object* v_unused_4271_; 
v_unused_4269_ = lean_ctor_get(v_toEditableDocumentCore_4247_, 3);
lean_dec(v_unused_4269_);
v_unused_4270_ = lean_ctor_get(v_toEditableDocumentCore_4247_, 2);
lean_dec(v_unused_4270_);
v_unused_4271_ = lean_ctor_get(v_toEditableDocumentCore_4247_, 1);
lean_dec(v_unused_4271_);
v___x_4250_ = v_toEditableDocumentCore_4247_;
v_isShared_4251_ = v_isSharedCheck_4268_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_meta_4248_);
lean_dec(v_toEditableDocumentCore_4247_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4268_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v_text_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4258_; 
v_text_4252_ = lean_ctor_get(v_meta_4248_, 3);
lean_inc_ref(v_text_4252_);
lean_dec_ref(v_meta_4248_);
v___x_4253_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4221_);
v___x_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4254_, 0, v_val_4233_);
lean_ctor_set(v___x_4254_, 1, v_val_4241_);
v___x_4255_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4252_, v___x_4254_);
v___x_4256_ = lean_box(0);
lean_inc(v___x_4222_);
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 3, v___x_4222_);
lean_ctor_set(v___x_4250_, 2, v___x_4256_);
lean_ctor_set(v___x_4250_, 1, v___y_4246_);
lean_ctor_set(v___x_4250_, 0, v___x_4255_);
v___x_4258_ = v___x_4250_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4255_);
lean_ctor_set(v_reuseFailAlloc_4267_, 1, v___y_4246_);
lean_ctor_set(v_reuseFailAlloc_4267_, 2, v___x_4256_);
lean_ctor_set(v_reuseFailAlloc_4267_, 3, v___x_4222_);
v___x_4258_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
lean_object* v___x_4259_; lean_object* v___x_4261_; 
v___x_4259_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4253_, v___x_4258_);
if (v_isShared_4244_ == 0)
{
lean_ctor_set(v___x_4243_, 0, v___x_4259_);
v___x_4261_ = v___x_4243_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4259_);
v___x_4261_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
lean_object* v___x_4262_; lean_object* v___x_4264_; 
lean_inc(v___x_4222_);
v___x_4262_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4222_);
lean_ctor_set(v___x_4262_, 1, v___x_4222_);
lean_ctor_set(v___x_4262_, 2, v___x_4223_);
lean_ctor_set(v___x_4262_, 3, v___x_4224_);
lean_ctor_set(v___x_4262_, 4, v___x_4225_);
lean_ctor_set(v___x_4262_, 5, v___x_4226_);
lean_ctor_set(v___x_4262_, 6, v___x_4227_);
lean_ctor_set(v___x_4262_, 7, v___x_4261_);
lean_ctor_set(v___x_4262_, 8, v___x_4228_);
lean_ctor_set(v___x_4262_, 9, v___x_4229_);
if (v_isShared_4236_ == 0)
{
lean_ctor_set_tag(v___x_4235_, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4262_);
v___x_4264_ = v___x_4235_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4262_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
v___jp_4273_:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4274_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4275_ = lean_string_append(v___x_4274_, v___x_4272_);
lean_dec_ref(v___x_4272_);
v___x_4276_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4277_ = lean_string_append(v___x_4275_, v___x_4276_);
v___y_4246_ = v___x_4277_;
goto v___jp_4245_;
}
}
}
else
{
lean_object* v___x_4292_; 
lean_dec(v___x_4240_);
lean_dec(v_val_4233_);
lean_dec_ref(v_snd_4230_);
lean_dec(v___x_4229_);
lean_dec(v___x_4228_);
lean_dec(v___x_4227_);
lean_dec(v___x_4226_);
lean_dec(v___x_4225_);
lean_dec(v___x_4224_);
lean_dec_ref(v___x_4223_);
lean_dec(v___x_4222_);
lean_dec_ref(v_a_4221_);
if (v_isShared_4236_ == 0)
{
lean_ctor_set_tag(v___x_4235_, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4231_);
v___x_4292_ = v___x_4235_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4231_);
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
else
{
lean_object* v___x_4295_; 
lean_dec_ref(v_snd_4230_);
lean_dec(v___x_4229_);
lean_dec(v___x_4228_);
lean_dec(v___x_4227_);
lean_dec(v___x_4226_);
lean_dec(v___x_4225_);
lean_dec(v___x_4224_);
lean_dec_ref(v___x_4223_);
lean_dec(v___x_4222_);
lean_dec_ref(v_a_4221_);
lean_dec(v_fst_4219_);
lean_dec(v___x_4218_);
v___x_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4231_);
return v___x_4295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4296_, lean_object* v_fst_4297_, lean_object* v___x_4298_, lean_object* v_a_4299_, lean_object* v___x_4300_, lean_object* v___x_4301_, lean_object* v___x_4302_, lean_object* v___x_4303_, lean_object* v___x_4304_, lean_object* v___x_4305_, lean_object* v___x_4306_, lean_object* v___x_4307_, lean_object* v_snd_4308_, lean_object* v___x_4309_, lean_object* v___y_4310_){
_start:
{
uint8_t v___x_4489__boxed_4311_; lean_object* v_res_4312_; 
v___x_4489__boxed_4311_ = lean_unbox(v___x_4298_);
v_res_4312_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4296_, v_fst_4297_, v___x_4489__boxed_4311_, v_a_4299_, v___x_4300_, v___x_4301_, v___x_4302_, v___x_4303_, v___x_4304_, v___x_4305_, v___x_4306_, v___x_4307_, v_snd_4308_, v___x_4309_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4316_, size_t v_sz_4317_, size_t v_i_4318_, lean_object* v_b_4319_){
_start:
{
lean_object* v_a_4321_; uint8_t v___x_4325_; 
v___x_4325_ = lean_usize_dec_lt(v_i_4318_, v_sz_4317_);
if (v___x_4325_ == 0)
{
lean_inc_ref(v_b_4319_);
return v_b_4319_;
}
else
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v_a_4328_; 
v___x_4326_ = lean_box(0);
v___x_4327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4328_ = lean_array_uget(v_as_4316_, v_i_4318_);
if (lean_obj_tag(v_a_4328_) == 1)
{
lean_object* v_i_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4363_; 
v_i_4329_ = lean_ctor_get(v_a_4328_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v_a_4328_);
if (v_isSharedCheck_4363_ == 0)
{
lean_object* v_unused_4364_; 
v_unused_4364_ = lean_ctor_get(v_a_4328_, 1);
lean_dec(v_unused_4364_);
v___x_4331_ = v_a_4328_;
v_isShared_4332_ = v_isSharedCheck_4363_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_i_4329_);
lean_dec(v_a_4328_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4363_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
if (lean_obj_tag(v_i_4329_) == 10)
{
lean_object* v_i_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4362_; 
v_i_4333_ = lean_ctor_get(v_i_4329_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v_i_4329_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4335_ = v_i_4329_;
v_isShared_4336_ = v_isSharedCheck_4362_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_i_4333_);
lean_dec(v_i_4329_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4362_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v_stx_4337_; lean_object* v_value_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4361_; 
v_stx_4337_ = lean_ctor_get(v_i_4333_, 0);
v_value_4338_ = lean_ctor_get(v_i_4333_, 1);
v_isSharedCheck_4361_ = !lean_is_exclusive(v_i_4333_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4340_ = v_i_4333_;
v_isShared_4341_ = v_isSharedCheck_4361_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_value_4338_);
lean_inc(v_stx_4337_);
lean_dec(v_i_4333_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4361_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4342_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4343_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4338_, v___x_4342_);
lean_dec(v_value_4338_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_del_object(v___x_4340_);
lean_dec(v_stx_4337_);
lean_del_object(v___x_4335_);
lean_del_object(v___x_4331_);
v_a_4321_ = v___x_4327_;
goto v___jp_4320_;
}
else
{
lean_object* v_val_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4360_; 
v_val_4344_ = lean_ctor_get(v___x_4343_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4346_ = v___x_4343_;
v_isShared_4347_ = v_isSharedCheck_4360_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_val_4344_);
lean_dec(v___x_4343_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4360_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 1, v_val_4344_);
v___x_4349_ = v___x_4340_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_stx_4337_);
lean_ctor_set(v_reuseFailAlloc_4359_, 1, v_val_4344_);
v___x_4349_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
lean_object* v___x_4351_; 
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 0, v___x_4349_);
v___x_4351_ = v___x_4346_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4349_);
v___x_4351_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
lean_object* v___x_4353_; 
if (v_isShared_4336_ == 0)
{
lean_ctor_set_tag(v___x_4335_, 1);
lean_ctor_set(v___x_4335_, 0, v___x_4351_);
v___x_4353_ = v___x_4335_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4351_);
v___x_4353_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
lean_object* v___x_4355_; 
if (v_isShared_4332_ == 0)
{
lean_ctor_set_tag(v___x_4331_, 0);
lean_ctor_set(v___x_4331_, 1, v___x_4326_);
lean_ctor_set(v___x_4331_, 0, v___x_4353_);
v___x_4355_ = v___x_4331_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v___x_4353_);
lean_ctor_set(v_reuseFailAlloc_4356_, 1, v___x_4326_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
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
lean_del_object(v___x_4331_);
lean_dec_ref(v_i_4329_);
v_a_4321_ = v___x_4327_;
goto v___jp_4320_;
}
}
}
else
{
lean_dec(v_a_4328_);
v_a_4321_ = v___x_4327_;
goto v___jp_4320_;
}
}
v___jp_4320_:
{
size_t v___x_4322_; size_t v___x_4323_; 
v___x_4322_ = ((size_t)1ULL);
v___x_4323_ = lean_usize_add(v_i_4318_, v___x_4322_);
v_i_4318_ = v___x_4323_;
v_b_4319_ = v_a_4321_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4365_, lean_object* v_sz_4366_, lean_object* v_i_4367_, lean_object* v_b_4368_){
_start:
{
size_t v_sz_boxed_4369_; size_t v_i_boxed_4370_; lean_object* v_res_4371_; 
v_sz_boxed_4369_ = lean_unbox_usize(v_sz_4366_);
lean_dec(v_sz_4366_);
v_i_boxed_4370_ = lean_unbox_usize(v_i_4367_);
lean_dec(v_i_4367_);
v_res_4371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4365_, v_sz_boxed_4369_, v_i_boxed_4370_, v_b_4368_);
lean_dec_ref(v_b_4368_);
lean_dec_ref(v_as_4365_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4372_, size_t v_sz_4373_, size_t v_i_4374_, lean_object* v_b_4375_){
_start:
{
lean_object* v_a_4377_; uint8_t v___x_4381_; 
v___x_4381_ = lean_usize_dec_lt(v_i_4374_, v_sz_4373_);
if (v___x_4381_ == 0)
{
lean_inc_ref(v_b_4375_);
return v_b_4375_;
}
else
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v_a_4384_; 
v___x_4382_ = lean_box(0);
v___x_4383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4384_ = lean_array_uget(v_as_4372_, v_i_4374_);
if (lean_obj_tag(v_a_4384_) == 1)
{
lean_object* v_i_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4419_; 
v_i_4385_ = lean_ctor_get(v_a_4384_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v_a_4384_);
if (v_isSharedCheck_4419_ == 0)
{
lean_object* v_unused_4420_; 
v_unused_4420_ = lean_ctor_get(v_a_4384_, 1);
lean_dec(v_unused_4420_);
v___x_4387_ = v_a_4384_;
v_isShared_4388_ = v_isSharedCheck_4419_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_i_4385_);
lean_dec(v_a_4384_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4419_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
if (lean_obj_tag(v_i_4385_) == 10)
{
lean_object* v_i_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4418_; 
v_i_4389_ = lean_ctor_get(v_i_4385_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v_i_4385_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4391_ = v_i_4385_;
v_isShared_4392_ = v_isSharedCheck_4418_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_i_4389_);
lean_dec(v_i_4385_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4418_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v_stx_4393_; lean_object* v_value_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4417_; 
v_stx_4393_ = lean_ctor_get(v_i_4389_, 0);
v_value_4394_ = lean_ctor_get(v_i_4389_, 1);
v_isSharedCheck_4417_ = !lean_is_exclusive(v_i_4389_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4396_ = v_i_4389_;
v_isShared_4397_ = v_isSharedCheck_4417_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_value_4394_);
lean_inc(v_stx_4393_);
lean_dec(v_i_4389_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4417_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4398_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4399_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4394_, v___x_4398_);
lean_dec(v_value_4394_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_del_object(v___x_4396_);
lean_dec(v_stx_4393_);
lean_del_object(v___x_4391_);
lean_del_object(v___x_4387_);
v_a_4377_ = v___x_4383_;
goto v___jp_4376_;
}
else
{
lean_object* v_val_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4416_; 
v_val_4400_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4402_ = v___x_4399_;
v_isShared_4403_ = v_isSharedCheck_4416_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_val_4400_);
lean_dec(v___x_4399_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4416_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 1, v_val_4400_);
v___x_4405_ = v___x_4396_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_stx_4393_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_val_4400_);
v___x_4405_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
lean_object* v___x_4407_; 
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 0, v___x_4405_);
v___x_4407_ = v___x_4402_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
lean_object* v___x_4409_; 
if (v_isShared_4392_ == 0)
{
lean_ctor_set_tag(v___x_4391_, 1);
lean_ctor_set(v___x_4391_, 0, v___x_4407_);
v___x_4409_ = v___x_4391_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4407_);
v___x_4409_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
lean_object* v___x_4411_; 
if (v_isShared_4388_ == 0)
{
lean_ctor_set_tag(v___x_4387_, 0);
lean_ctor_set(v___x_4387_, 1, v___x_4382_);
lean_ctor_set(v___x_4387_, 0, v___x_4409_);
v___x_4411_ = v___x_4387_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4409_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v___x_4382_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
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
lean_del_object(v___x_4387_);
lean_dec_ref(v_i_4385_);
v_a_4377_ = v___x_4383_;
goto v___jp_4376_;
}
}
}
else
{
lean_dec(v_a_4384_);
v_a_4377_ = v___x_4383_;
goto v___jp_4376_;
}
}
v___jp_4376_:
{
size_t v___x_4378_; size_t v___x_4379_; lean_object* v___x_4380_; 
v___x_4378_ = ((size_t)1ULL);
v___x_4379_ = lean_usize_add(v_i_4374_, v___x_4378_);
v___x_4380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4372_, v_sz_4373_, v___x_4379_, v_a_4377_);
return v___x_4380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4421_, lean_object* v_sz_4422_, lean_object* v_i_4423_, lean_object* v_b_4424_){
_start:
{
size_t v_sz_boxed_4425_; size_t v_i_boxed_4426_; lean_object* v_res_4427_; 
v_sz_boxed_4425_ = lean_unbox_usize(v_sz_4422_);
lean_dec(v_sz_4422_);
v_i_boxed_4426_ = lean_unbox_usize(v_i_4423_);
lean_dec(v_i_4423_);
v_res_4427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4421_, v_sz_boxed_4425_, v_i_boxed_4426_, v_b_4424_);
lean_dec_ref(v_b_4424_);
lean_dec_ref(v_as_4421_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4428_){
_start:
{
if (lean_obj_tag(v_x_4428_) == 0)
{
lean_object* v_cs_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; size_t v_sz_4432_; size_t v___x_4433_; lean_object* v___x_4434_; lean_object* v_fst_4435_; 
v_cs_4429_ = lean_ctor_get(v_x_4428_, 0);
v___x_4430_ = lean_box(0);
v___x_4431_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4432_ = lean_array_size(v_cs_4429_);
v___x_4433_ = ((size_t)0ULL);
v___x_4434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4429_, v_sz_4432_, v___x_4433_, v___x_4431_);
v_fst_4435_ = lean_ctor_get(v___x_4434_, 0);
lean_inc(v_fst_4435_);
lean_dec_ref(v___x_4434_);
if (lean_obj_tag(v_fst_4435_) == 0)
{
return v___x_4430_;
}
else
{
lean_object* v_val_4436_; 
v_val_4436_ = lean_ctor_get(v_fst_4435_, 0);
lean_inc(v_val_4436_);
lean_dec_ref_known(v_fst_4435_, 1);
return v_val_4436_;
}
}
else
{
lean_object* v_vs_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; size_t v_sz_4440_; size_t v___x_4441_; lean_object* v___x_4442_; lean_object* v_fst_4443_; 
v_vs_4437_ = lean_ctor_get(v_x_4428_, 0);
v___x_4438_ = lean_box(0);
v___x_4439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4440_ = lean_array_size(v_vs_4437_);
v___x_4441_ = ((size_t)0ULL);
v___x_4442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4437_, v_sz_4440_, v___x_4441_, v___x_4439_);
v_fst_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_fst_4443_);
lean_dec_ref(v___x_4442_);
if (lean_obj_tag(v_fst_4443_) == 0)
{
return v___x_4438_;
}
else
{
lean_object* v_val_4444_; 
v_val_4444_ = lean_ctor_get(v_fst_4443_, 0);
lean_inc(v_val_4444_);
lean_dec_ref_known(v_fst_4443_, 1);
return v_val_4444_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4445_, size_t v_sz_4446_, size_t v_i_4447_, lean_object* v_b_4448_){
_start:
{
uint8_t v___x_4449_; 
v___x_4449_ = lean_usize_dec_lt(v_i_4447_, v_sz_4446_);
if (v___x_4449_ == 0)
{
lean_inc_ref(v_b_4448_);
return v_b_4448_;
}
else
{
lean_object* v___x_4450_; lean_object* v_a_4451_; lean_object* v___x_4452_; 
v___x_4450_ = lean_box(0);
v_a_4451_ = lean_array_uget_borrowed(v_as_4445_, v_i_4447_);
v___x_4452_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4451_);
if (lean_obj_tag(v___x_4452_) == 1)
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
v___x_4454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
lean_ctor_set(v___x_4454_, 1, v___x_4450_);
return v___x_4454_;
}
else
{
lean_object* v___x_4455_; size_t v___x_4456_; size_t v___x_4457_; 
lean_dec(v___x_4452_);
v___x_4455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4456_ = ((size_t)1ULL);
v___x_4457_ = lean_usize_add(v_i_4447_, v___x_4456_);
v_i_4447_ = v___x_4457_;
v_b_4448_ = v___x_4455_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4459_, lean_object* v_sz_4460_, lean_object* v_i_4461_, lean_object* v_b_4462_){
_start:
{
size_t v_sz_boxed_4463_; size_t v_i_boxed_4464_; lean_object* v_res_4465_; 
v_sz_boxed_4463_ = lean_unbox_usize(v_sz_4460_);
lean_dec(v_sz_4460_);
v_i_boxed_4464_ = lean_unbox_usize(v_i_4461_);
lean_dec(v_i_4461_);
v_res_4465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4459_, v_sz_boxed_4463_, v_i_boxed_4464_, v_b_4462_);
lean_dec_ref(v_b_4462_);
lean_dec_ref(v_as_4459_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4466_);
lean_dec_ref(v_x_4466_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4468_){
_start:
{
lean_object* v_root_4469_; lean_object* v_tail_4470_; lean_object* v___x_4471_; 
v_root_4469_ = lean_ctor_get(v_t_4468_, 0);
v_tail_4470_ = lean_ctor_get(v_t_4468_, 1);
v___x_4471_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4469_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v___x_4472_; size_t v_sz_4473_; size_t v___x_4474_; lean_object* v___x_4475_; lean_object* v_fst_4476_; 
v___x_4472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4473_ = lean_array_size(v_tail_4470_);
v___x_4474_ = ((size_t)0ULL);
v___x_4475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4470_, v_sz_4473_, v___x_4474_, v___x_4472_);
v_fst_4476_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_fst_4476_);
lean_dec_ref(v___x_4475_);
if (lean_obj_tag(v_fst_4476_) == 0)
{
return v___x_4471_;
}
else
{
lean_object* v_val_4477_; 
v_val_4477_ = lean_ctor_get(v_fst_4476_, 0);
lean_inc(v_val_4477_);
lean_dec_ref_known(v_fst_4476_, 1);
return v_val_4477_;
}
}
else
{
return v___x_4471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4478_);
lean_dec_ref(v_t_4478_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4494_, lean_object* v_a_4495_){
_start:
{
if (lean_obj_tag(v_node_4494_) == 1)
{
lean_object* v_children_4497_; lean_object* v_res_4498_; 
v_children_4497_ = lean_ctor_get(v_node_4494_, 1);
v_res_4498_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4497_);
if (lean_obj_tag(v_res_4498_) == 1)
{
lean_object* v_val_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4536_; 
v_val_4499_ = lean_ctor_get(v_res_4498_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v_res_4498_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4501_ = v_res_4498_;
v_isShared_4502_ = v_isSharedCheck_4536_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_val_4499_);
lean_dec(v_res_4498_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4536_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v_fst_4503_; lean_object* v_snd_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4535_; 
v_fst_4503_ = lean_ctor_get(v_val_4499_, 0);
v_snd_4504_ = lean_ctor_get(v_val_4499_, 1);
v_isSharedCheck_4535_ = !lean_is_exclusive(v_val_4499_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4506_ = v_val_4499_;
v_isShared_4507_ = v_isSharedCheck_4535_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_snd_4504_);
lean_inc(v_fst_4503_);
lean_dec(v_val_4499_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4535_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4508_; lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4534_; 
v___x_4508_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4495_);
v_a_4509_ = lean_ctor_get(v___x_4508_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4511_ = v___x_4508_;
v_isShared_4512_ = v_isSharedCheck_4534_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4508_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4534_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; uint8_t v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___y_4521_; lean_object* v___x_4523_; 
v___x_4513_ = lean_box(0);
v___x_4514_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4515_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4516_ = 1;
v___x_4517_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4518_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4519_ = l_Lean_Syntax_getPos_x3f(v_fst_4503_, v___x_4516_);
v___x_4520_ = lean_box(v___x_4516_);
v___y_4521_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4521_, 0, v___x_4519_);
lean_closure_set(v___y_4521_, 1, v_fst_4503_);
lean_closure_set(v___y_4521_, 2, v___x_4520_);
lean_closure_set(v___y_4521_, 3, v_a_4509_);
lean_closure_set(v___y_4521_, 4, v___x_4513_);
lean_closure_set(v___y_4521_, 5, v___x_4514_);
lean_closure_set(v___y_4521_, 6, v___x_4515_);
lean_closure_set(v___y_4521_, 7, v___x_4513_);
lean_closure_set(v___y_4521_, 8, v___x_4517_);
lean_closure_set(v___y_4521_, 9, v___x_4513_);
lean_closure_set(v___y_4521_, 10, v___x_4513_);
lean_closure_set(v___y_4521_, 11, v___x_4513_);
lean_closure_set(v___y_4521_, 12, v_snd_4504_);
lean_closure_set(v___y_4521_, 13, v___x_4518_);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 0, v___y_4521_);
v___x_4523_ = v___x_4501_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___y_4521_);
v___x_4523_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4525_; 
if (v_isShared_4507_ == 0)
{
lean_ctor_set(v___x_4506_, 1, v___x_4523_);
lean_ctor_set(v___x_4506_, 0, v___x_4518_);
v___x_4525_ = v___x_4506_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4518_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v___x_4523_);
v___x_4525_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4530_; 
v___x_4526_ = lean_unsigned_to_nat(1u);
v___x_4527_ = lean_mk_empty_array_with_capacity(v___x_4526_);
v___x_4528_ = lean_array_push(v___x_4527_, v___x_4525_);
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 0, v___x_4528_);
v___x_4530_ = v___x_4511_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4528_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
lean_dec(v_res_4498_);
v___x_4537_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4537_);
return v___x_4538_;
}
}
else
{
lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4539_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
return v___x_4540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4541_, v_a_4542_);
lean_dec_ref(v_a_4542_);
lean_dec_ref(v_node_4541_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4545_, lean_object* v_x_4546_, lean_object* v_x_4547_, lean_object* v_node_4548_, lean_object* v_a_4549_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4548_, v_a_4549_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4552_, lean_object* v_x_4553_, lean_object* v_x_4554_, lean_object* v_node_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4552_, v_x_4553_, v_x_4554_, v_node_4555_, v_a_4556_);
lean_dec_ref(v_a_4556_);
lean_dec_ref(v_node_4555_);
lean_dec_ref(v_x_4554_);
lean_dec_ref(v_x_4553_);
lean_dec_ref(v_x_4552_);
return v_res_4558_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4559_, lean_object* v_inst_4560_, lean_object* v_R_4561_, lean_object* v_a_4562_, uint8_t v_b_4563_, lean_object* v_c_4564_){
_start:
{
uint8_t v___x_4565_; 
v___x_4565_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4559_, v_a_4562_, v_b_4563_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4566_, lean_object* v_inst_4567_, lean_object* v_R_4568_, lean_object* v_a_4569_, lean_object* v_b_4570_, lean_object* v_c_4571_){
_start:
{
uint8_t v_b_boxed_4572_; uint8_t v_res_4573_; lean_object* v_r_4574_; 
v_b_boxed_4572_ = lean_unbox(v_b_4570_);
v_res_4573_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4566_, v_inst_4567_, v_R_4568_, v_a_4569_, v_b_boxed_4572_, v_c_4571_);
lean_dec_ref(v_s_4566_);
v_r_4574_ = lean_box(v_res_4573_);
return v_r_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_(){
_start:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4580_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_));
v___x_4581_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4582_ = l_Lean_CodeAction_insertBuiltin(v___x_4580_, v___x_4581_);
return v___x_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355____boxed(lean_object* v_a_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_();
return v_res_4584_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4586_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4587_ = lean_string_utf8_byte_size(v___x_4586_);
return v___x_4587_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; uint8_t v___x_4590_; 
v___x_4588_ = lean_unsigned_to_nat(0u);
v___x_4589_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4590_ = lean_nat_dec_eq(v___x_4589_, v___x_4588_);
return v___x_4590_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4591_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4592_ = lean_unsigned_to_nat(0u);
v___x_4593_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4594_, 0, v___x_4593_);
lean_ctor_set(v___x_4594_, 1, v___x_4592_);
lean_ctor_set(v___x_4594_, 2, v___x_4591_);
return v___x_4594_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4(void){
_start:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4596_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4595_);
return v___x_4596_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4597_ = lean_unsigned_to_nat(0u);
v___x_4598_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4);
v___x_4599_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4600_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4599_);
lean_ctor_set(v___x_4600_, 1, v___x_4598_);
lean_ctor_set(v___x_4600_, 2, v___x_4597_);
lean_ctor_set(v___x_4600_, 3, v___x_4597_);
return v___x_4600_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4601_){
_start:
{
lean_object* v___y_4603_; uint8_t v___x_4606_; 
v___x_4606_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
if (v___x_4606_ == 0)
{
lean_object* v___x_4607_; 
v___x_4607_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5);
v___y_4603_ = v___x_4607_;
goto v___jp_4602_;
}
else
{
lean_object* v___x_4608_; 
v___x_4608_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_4603_ = v___x_4608_;
goto v___jp_4602_;
}
v___jp_4602_:
{
uint8_t v___x_4604_; uint8_t v___x_4605_; 
v___x_4604_ = 0;
lean_inc(v___y_4603_);
v___x_4605_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4601_, v___y_4603_, v___x_4604_);
return v___x_4605_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4609_){
_start:
{
uint8_t v_res_4610_; lean_object* v_r_4611_; 
v_res_4610_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4609_);
lean_dec_ref(v_s_4609_);
v_r_4611_ = lean_box(v_res_4610_);
return v_r_4611_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4612_, lean_object* v_as_x27_4613_, uint8_t v_b_4614_){
_start:
{
if (lean_obj_tag(v_as_x27_4613_) == 0)
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = lean_box(v_b_4614_);
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
return v___x_4617_;
}
else
{
lean_object* v_head_4618_; uint8_t v_isSilent_4619_; 
v_head_4618_ = lean_ctor_get(v_as_x27_4613_, 0);
v_isSilent_4619_ = lean_ctor_get_uint8(v_head_4618_, sizeof(void*)*5 + 2);
if (v_isSilent_4619_ == 0)
{
lean_object* v_tail_4620_; lean_object* v_data_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; uint8_t v___x_4626_; 
v_tail_4620_ = lean_ctor_get(v_as_x27_4613_, 1);
v_data_4621_ = lean_ctor_get(v_head_4618_, 4);
lean_inc(v_data_4621_);
v___x_4622_ = l_Lean_MessageData_toString(v_data_4621_);
v___x_4623_ = lean_unsigned_to_nat(0u);
v___x_4624_ = lean_string_utf8_byte_size(v___x_4622_);
v___x_4625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4622_);
lean_ctor_set(v___x_4625_, 1, v___x_4623_);
lean_ctor_set(v___x_4625_, 2, v___x_4624_);
v___x_4626_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4625_);
lean_dec_ref_known(v___x_4625_, 3);
if (v___x_4626_ == 0)
{
v_as_x27_4613_ = v_tail_4620_;
goto _start;
}
else
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4628_ = lean_box(v_foundPanic_4612_);
v___x_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4628_);
return v___x_4629_;
}
}
else
{
lean_object* v_tail_4630_; 
v_tail_4630_ = lean_ctor_get(v_as_x27_4613_, 1);
v_as_x27_4613_ = v_tail_4630_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4632_, lean_object* v_as_x27_4633_, lean_object* v_b_4634_, lean_object* v___y_4635_){
_start:
{
uint8_t v_foundPanic_boxed_4636_; uint8_t v_b_boxed_4637_; lean_object* v_res_4638_; 
v_foundPanic_boxed_4636_ = lean_unbox(v_foundPanic_4632_);
v_b_boxed_4637_ = lean_unbox(v_b_4634_);
v_res_4638_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4636_, v_as_x27_4633_, v_b_boxed_4637_);
lean_dec(v_as_x27_4633_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4639_, uint8_t v_severity_4640_, uint8_t v_isSilent_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v___x_4645_; 
v___x_4645_ = l_Lean_Elab_Command_getRef___redArg(v___y_4642_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v___x_4647_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref_known(v___x_4645_, 1);
v___x_4647_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4646_, v_msgData_4639_, v_severity_4640_, v_isSilent_4641_, v___y_4642_, v___y_4643_);
lean_dec(v_a_4646_);
return v___x_4647_;
}
else
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
lean_dec_ref(v_msgData_4639_);
v_a_4648_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v___x_4645_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4645_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4651_ == 0)
{
v___x_4653_ = v___x_4650_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4648_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4656_, lean_object* v_severity_4657_, lean_object* v_isSilent_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
uint8_t v_severity_boxed_4662_; uint8_t v_isSilent_boxed_4663_; lean_object* v_res_4664_; 
v_severity_boxed_4662_ = lean_unbox(v_severity_4657_);
v_isSilent_boxed_4663_ = lean_unbox(v_isSilent_4658_);
v_res_4664_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4656_, v_severity_boxed_4662_, v_isSilent_boxed_4663_, v___y_4659_, v___y_4660_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
uint8_t v___x_4669_; uint8_t v___x_4670_; lean_object* v___x_4671_; 
v___x_4669_ = 2;
v___x_4670_ = 0;
v___x_4671_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4665_, v___x_4669_, v___x_4670_, v___y_4666_, v___y_4667_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4672_, v___y_4673_, v___y_4674_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
return v_res_4676_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4684_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4685_ = l_Lean_MessageData_ofFormat(v___x_4684_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v___x_4690_; uint8_t v_foundPanic_4691_; 
v___x_4690_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4686_);
v_foundPanic_4691_ = l_Lean_Syntax_isOfKind(v_x_4686_, v___x_4690_);
if (v_foundPanic_4691_ == 0)
{
lean_object* v___x_4692_; 
lean_dec(v_x_4686_);
v___x_4692_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4692_;
}
else
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4693_ = lean_unsigned_to_nat(2u);
v___x_4694_ = l_Lean_Syntax_getArg(v_x_4686_, v___x_4693_);
lean_dec(v_x_4686_);
v___x_4695_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4694_, v_a_4687_, v_a_4688_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; uint8_t v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4756_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4695_, 1);
v___x_4697_ = 0;
v___x_4698_ = l_Lean_MessageLog_toList(v_a_4696_);
v___x_4699_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4691_, v___x_4698_, v___x_4697_);
lean_dec(v___x_4698_);
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4702_ = v___x_4699_;
v_isShared_4703_ = v_isSharedCheck_4756_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4699_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4756_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
uint8_t v___x_4704_; 
v___x_4704_ = lean_unbox(v_a_4700_);
lean_dec(v_a_4700_);
if (v___x_4704_ == 0)
{
lean_object* v___x_4705_; lean_object* v_env_4706_; lean_object* v_scopes_4707_; lean_object* v_usedQuotCtxts_4708_; lean_object* v_nextMacroScope_4709_; lean_object* v_maxRecDepth_4710_; lean_object* v_ngen_4711_; lean_object* v_auxDeclNGen_4712_; lean_object* v_infoState_4713_; lean_object* v_traceState_4714_; lean_object* v_snapshotTasks_4715_; lean_object* v_prevLinterStates_4716_; lean_object* v_codeQualityEntryTasks_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4727_; 
lean_del_object(v___x_4702_);
v___x_4705_ = lean_st_ref_take(v_a_4688_);
v_env_4706_ = lean_ctor_get(v___x_4705_, 0);
v_scopes_4707_ = lean_ctor_get(v___x_4705_, 2);
v_usedQuotCtxts_4708_ = lean_ctor_get(v___x_4705_, 3);
v_nextMacroScope_4709_ = lean_ctor_get(v___x_4705_, 4);
v_maxRecDepth_4710_ = lean_ctor_get(v___x_4705_, 5);
v_ngen_4711_ = lean_ctor_get(v___x_4705_, 6);
v_auxDeclNGen_4712_ = lean_ctor_get(v___x_4705_, 7);
v_infoState_4713_ = lean_ctor_get(v___x_4705_, 8);
v_traceState_4714_ = lean_ctor_get(v___x_4705_, 9);
v_snapshotTasks_4715_ = lean_ctor_get(v___x_4705_, 10);
v_prevLinterStates_4716_ = lean_ctor_get(v___x_4705_, 11);
v_codeQualityEntryTasks_4717_ = lean_ctor_get(v___x_4705_, 12);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4727_ == 0)
{
lean_object* v_unused_4728_; 
v_unused_4728_ = lean_ctor_get(v___x_4705_, 1);
lean_dec(v_unused_4728_);
v___x_4719_ = v___x_4705_;
v_isShared_4720_ = v_isSharedCheck_4727_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4717_);
lean_inc(v_prevLinterStates_4716_);
lean_inc(v_snapshotTasks_4715_);
lean_inc(v_traceState_4714_);
lean_inc(v_infoState_4713_);
lean_inc(v_auxDeclNGen_4712_);
lean_inc(v_ngen_4711_);
lean_inc(v_maxRecDepth_4710_);
lean_inc(v_nextMacroScope_4709_);
lean_inc(v_usedQuotCtxts_4708_);
lean_inc(v_scopes_4707_);
lean_inc(v_env_4706_);
lean_dec(v___x_4705_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4727_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
lean_ctor_set(v___x_4719_, 1, v_a_4696_);
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_env_4706_);
lean_ctor_set(v_reuseFailAlloc_4726_, 1, v_a_4696_);
lean_ctor_set(v_reuseFailAlloc_4726_, 2, v_scopes_4707_);
lean_ctor_set(v_reuseFailAlloc_4726_, 3, v_usedQuotCtxts_4708_);
lean_ctor_set(v_reuseFailAlloc_4726_, 4, v_nextMacroScope_4709_);
lean_ctor_set(v_reuseFailAlloc_4726_, 5, v_maxRecDepth_4710_);
lean_ctor_set(v_reuseFailAlloc_4726_, 6, v_ngen_4711_);
lean_ctor_set(v_reuseFailAlloc_4726_, 7, v_auxDeclNGen_4712_);
lean_ctor_set(v_reuseFailAlloc_4726_, 8, v_infoState_4713_);
lean_ctor_set(v_reuseFailAlloc_4726_, 9, v_traceState_4714_);
lean_ctor_set(v_reuseFailAlloc_4726_, 10, v_snapshotTasks_4715_);
lean_ctor_set(v_reuseFailAlloc_4726_, 11, v_prevLinterStates_4716_);
lean_ctor_set(v_reuseFailAlloc_4726_, 12, v_codeQualityEntryTasks_4717_);
v___x_4722_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4723_ = lean_st_ref_put(v_a_4688_, v___x_4722_);
v___x_4724_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4725_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4724_, v_a_4687_, v_a_4688_);
return v___x_4725_;
}
}
}
else
{
lean_object* v___x_4729_; lean_object* v_env_4730_; lean_object* v_scopes_4731_; lean_object* v_usedQuotCtxts_4732_; lean_object* v_nextMacroScope_4733_; lean_object* v_maxRecDepth_4734_; lean_object* v_ngen_4735_; lean_object* v_auxDeclNGen_4736_; lean_object* v_infoState_4737_; lean_object* v_traceState_4738_; lean_object* v_snapshotTasks_4739_; lean_object* v_prevLinterStates_4740_; lean_object* v_codeQualityEntryTasks_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4754_; 
lean_dec(v_a_4696_);
v___x_4729_ = lean_st_ref_take(v_a_4688_);
v_env_4730_ = lean_ctor_get(v___x_4729_, 0);
v_scopes_4731_ = lean_ctor_get(v___x_4729_, 2);
v_usedQuotCtxts_4732_ = lean_ctor_get(v___x_4729_, 3);
v_nextMacroScope_4733_ = lean_ctor_get(v___x_4729_, 4);
v_maxRecDepth_4734_ = lean_ctor_get(v___x_4729_, 5);
v_ngen_4735_ = lean_ctor_get(v___x_4729_, 6);
v_auxDeclNGen_4736_ = lean_ctor_get(v___x_4729_, 7);
v_infoState_4737_ = lean_ctor_get(v___x_4729_, 8);
v_traceState_4738_ = lean_ctor_get(v___x_4729_, 9);
v_snapshotTasks_4739_ = lean_ctor_get(v___x_4729_, 10);
v_prevLinterStates_4740_ = lean_ctor_get(v___x_4729_, 11);
v_codeQualityEntryTasks_4741_ = lean_ctor_get(v___x_4729_, 12);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4754_ == 0)
{
lean_object* v_unused_4755_; 
v_unused_4755_ = lean_ctor_get(v___x_4729_, 1);
lean_dec(v_unused_4755_);
v___x_4743_ = v___x_4729_;
v_isShared_4744_ = v_isSharedCheck_4754_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4741_);
lean_inc(v_prevLinterStates_4740_);
lean_inc(v_snapshotTasks_4739_);
lean_inc(v_traceState_4738_);
lean_inc(v_infoState_4737_);
lean_inc(v_auxDeclNGen_4736_);
lean_inc(v_ngen_4735_);
lean_inc(v_maxRecDepth_4734_);
lean_inc(v_nextMacroScope_4733_);
lean_inc(v_usedQuotCtxts_4732_);
lean_inc(v_scopes_4731_);
lean_inc(v_env_4730_);
lean_dec(v___x_4729_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4754_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4748_; 
v___x_4745_ = lean_box(0);
v___x_4746_ = l_Lean_MessageLog_empty;
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 1, v___x_4746_);
v___x_4748_ = v___x_4743_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_env_4730_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v___x_4746_);
lean_ctor_set(v_reuseFailAlloc_4753_, 2, v_scopes_4731_);
lean_ctor_set(v_reuseFailAlloc_4753_, 3, v_usedQuotCtxts_4732_);
lean_ctor_set(v_reuseFailAlloc_4753_, 4, v_nextMacroScope_4733_);
lean_ctor_set(v_reuseFailAlloc_4753_, 5, v_maxRecDepth_4734_);
lean_ctor_set(v_reuseFailAlloc_4753_, 6, v_ngen_4735_);
lean_ctor_set(v_reuseFailAlloc_4753_, 7, v_auxDeclNGen_4736_);
lean_ctor_set(v_reuseFailAlloc_4753_, 8, v_infoState_4737_);
lean_ctor_set(v_reuseFailAlloc_4753_, 9, v_traceState_4738_);
lean_ctor_set(v_reuseFailAlloc_4753_, 10, v_snapshotTasks_4739_);
lean_ctor_set(v_reuseFailAlloc_4753_, 11, v_prevLinterStates_4740_);
lean_ctor_set(v_reuseFailAlloc_4753_, 12, v_codeQualityEntryTasks_4741_);
v___x_4748_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
lean_object* v___x_4749_; lean_object* v___x_4751_; 
v___x_4749_ = lean_st_ref_put(v_a_4688_, v___x_4748_);
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 0, v___x_4745_);
v___x_4751_ = v___x_4702_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4745_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
}
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
v_a_4757_ = lean_ctor_get(v___x_4695_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4759_ = v___x_4695_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4695_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4757_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4765_, v_a_4766_, v_a_4767_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4770_, lean_object* v_as_4771_, lean_object* v_as_x27_4772_, uint8_t v_b_4773_, lean_object* v_a_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4770_, v_as_x27_4772_, v_b_4773_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4779_, lean_object* v_as_4780_, lean_object* v_as_x27_4781_, lean_object* v_b_4782_, lean_object* v_a_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_){
_start:
{
uint8_t v_foundPanic_boxed_4787_; uint8_t v_b_boxed_4788_; lean_object* v_res_4789_; 
v_foundPanic_boxed_4787_ = lean_unbox(v_foundPanic_4779_);
v_b_boxed_4788_ = lean_unbox(v_b_4782_);
v_res_4789_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4787_, v_as_4780_, v_as_x27_4781_, v_b_boxed_4788_, v_a_4783_, v___y_4784_, v___y_4785_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
lean_dec(v_as_x27_4781_);
lean_dec(v_as_4780_);
return v_res_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4798_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4799_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4800_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4801_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4802_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4798_, v___x_4799_, v___x_4800_, v___x_4801_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4803_){
_start:
{
lean_object* v_res_4804_; 
v_res_4804_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4804_;
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
