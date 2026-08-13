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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_127_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v___y_123_, v_pos_116_);
v___x_128_ = lean_string_append(v___x_126_, v___x_127_);
lean_dec_ref(v___x_127_);
v___x_129_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2));
v___x_130_ = lean_string_append(v___x_128_, v___x_129_);
v___x_131_ = lean_string_append(v___x_130_, v___y_125_);
lean_dec_ref(v___y_125_);
v___x_132_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_133_ = lean_string_append(v___x_131_, v___x_132_);
v___x_134_ = lean_string_append(v___x_133_, v___y_124_);
lean_dec_ref(v___y_124_);
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
v___y_123_ = v_val_137_;
v___y_124_ = v_str_136_;
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
v___y_123_ = v_val_140_;
v___y_124_ = v_str_136_;
v___y_125_ = v___x_145_;
goto v___jp_122_;
}
else
{
lean_object* v___x_146_; 
lean_inc(v_column_142_);
lean_dec(v_val_139_);
v___x_146_ = l_Nat_reprFast(v_column_142_);
v___y_123_ = v_val_140_;
v___y_124_ = v_str_136_;
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
v___x_1794_ = lean_st_ref_set(v_a_1752_, v___x_1793_);
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
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = lean_box(1);
v___x_1849_ = l_Lean_MessageData_ofFormat(v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1854_ = l_Lean_MessageData_ofFormat(v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
if (lean_obj_tag(v_x_1856_) == 0)
{
return v_x_1855_;
}
else
{
lean_object* v_head_1857_; lean_object* v_tail_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1880_; 
v_head_1857_ = lean_ctor_get(v_x_1856_, 0);
v_tail_1858_ = lean_ctor_get(v_x_1856_, 1);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_x_1856_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1860_ = v_x_1856_;
v_isShared_1861_ = v_isSharedCheck_1880_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_tail_1858_);
lean_inc(v_head_1857_);
lean_dec(v_x_1856_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1880_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v_before_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1878_; 
v_before_1862_ = lean_ctor_get(v_head_1857_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_head_1857_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v_head_1857_, 1);
lean_dec(v_unused_1879_);
v___x_1864_ = v_head_1857_;
v_isShared_1865_ = v_isSharedCheck_1878_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_before_1862_);
lean_dec(v_head_1857_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1878_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1866_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 7);
lean_ctor_set(v___x_1864_, 1, v___x_1866_);
lean_ctor_set(v___x_1864_, 0, v_x_1855_);
v___x_1868_ = v___x_1864_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_x_1855_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1869_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1861_ == 0)
{
lean_ctor_set_tag(v___x_1860_, 7);
lean_ctor_set(v___x_1860_, 1, v___x_1869_);
lean_ctor_set(v___x_1860_, 0, v___x_1868_);
v___x_1871_ = v___x_1860_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = l_Lean_MessageData_ofSyntax(v_before_1862_);
v___x_1873_ = l_Lean_indentD(v___x_1872_);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1871_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v_x_1855_ = v___x_1874_;
v_x_1856_ = v_tail_1858_;
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
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1885_ = l_Lean_MessageData_ofFormat(v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1886_, lean_object* v_macroStack_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v_scopes_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v_opts_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1890_ = lean_st_ref_get(v___y_1888_);
v_scopes_1891_ = lean_ctor_get(v___x_1890_, 2);
lean_inc(v_scopes_1891_);
lean_dec(v___x_1890_);
v___x_1892_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1893_ = l_List_head_x21___redArg(v___x_1892_, v_scopes_1891_);
lean_dec(v_scopes_1891_);
v_opts_1894_ = lean_ctor_get(v___x_1893_, 1);
lean_inc_ref(v_opts_1894_);
lean_dec(v___x_1893_);
v___x_1895_ = l_Lean_Elab_pp_macroStack;
v___x_1896_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1894_, v___x_1895_);
lean_dec_ref(v_opts_1894_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; 
lean_dec(v_macroStack_1887_);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v_msgData_1886_);
return v___x_1897_;
}
else
{
if (lean_obj_tag(v_macroStack_1887_) == 0)
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_msgData_1886_);
return v___x_1898_;
}
else
{
lean_object* v_head_1899_; lean_object* v_after_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1915_; 
v_head_1899_ = lean_ctor_get(v_macroStack_1887_, 0);
lean_inc(v_head_1899_);
v_after_1900_ = lean_ctor_get(v_head_1899_, 1);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_head_1899_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v_head_1899_, 0);
lean_dec(v_unused_1916_);
v___x_1902_ = v_head_1899_;
v_isShared_1903_ = v_isSharedCheck_1915_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_after_1900_);
lean_dec(v_head_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1915_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1903_ == 0)
{
lean_ctor_set_tag(v___x_1902_, 7);
lean_ctor_set(v___x_1902_, 1, v___x_1904_);
lean_ctor_set(v___x_1902_, 0, v_msgData_1886_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_msgData_1886_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_msgData_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1907_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = l_Lean_MessageData_ofSyntax(v_after_1900_);
v___x_1910_ = l_Lean_indentD(v___x_1909_);
v_msgData_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1911_, 0, v___x_1908_);
lean_ctor_set(v_msgData_1911_, 1, v___x_1910_);
v___x_1912_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1911_, v_macroStack_1887_);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1917_, lean_object* v_macroStack_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1917_, v_macroStack_1918_, v___y_1919_);
lean_dec(v___y_1919_);
return v_res_1921_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1922_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
return v___x_1924_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
lean_ctor_set(v___x_1927_, 2, v___x_1926_);
lean_ctor_set(v___x_1927_, 3, v___x_1926_);
lean_ctor_set(v___x_1927_, 4, v___x_1925_);
lean_ctor_set(v___x_1927_, 5, v___x_1925_);
lean_ctor_set(v___x_1927_, 6, v___x_1925_);
lean_ctor_set(v___x_1927_, 7, v___x_1925_);
lean_ctor_set(v___x_1927_, 8, v___x_1925_);
lean_ctor_set(v___x_1927_, 9, v___x_1925_);
return v___x_1927_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = lean_unsigned_to_nat(32u);
v___x_1929_ = lean_mk_empty_array_with_capacity(v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1931_ = ((size_t)5ULL);
v___x_1932_ = lean_unsigned_to_nat(0u);
v___x_1933_ = lean_unsigned_to_nat(32u);
v___x_1934_ = lean_mk_empty_array_with_capacity(v___x_1933_);
v___x_1935_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1936_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
lean_ctor_set(v___x_1936_, 1, v___x_1934_);
lean_ctor_set(v___x_1936_, 2, v___x_1932_);
lean_ctor_set(v___x_1936_, 3, v___x_1932_);
lean_ctor_set_usize(v___x_1936_, 4, v___x_1931_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1937_ = lean_box(1);
v___x_1938_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1939_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v___x_1938_);
lean_ctor_set(v___x_1940_, 2, v___x_1937_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; lean_object* v_env_1945_; lean_object* v___x_1946_; lean_object* v_scopes_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v_opts_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1944_ = lean_st_ref_get(v___y_1942_);
v_env_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc_ref(v_env_1945_);
lean_dec(v___x_1944_);
v___x_1946_ = lean_st_ref_get(v___y_1942_);
v_scopes_1947_ = lean_ctor_get(v___x_1946_, 2);
lean_inc(v_scopes_1947_);
lean_dec(v___x_1946_);
v___x_1948_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1949_ = l_List_head_x21___redArg(v___x_1948_, v_scopes_1947_);
lean_dec(v_scopes_1947_);
v_opts_1950_ = lean_ctor_get(v___x_1949_, 1);
lean_inc_ref(v_opts_1950_);
lean_dec(v___x_1949_);
v___x_1951_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1952_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1953_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1953_, 0, v_env_1945_);
lean_ctor_set(v___x_1953_, 1, v___x_1951_);
lean_ctor_set(v___x_1953_, 2, v___x_1952_);
lean_ctor_set(v___x_1953_, 3, v_opts_1950_);
v___x_1954_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set(v___x_1954_, 1, v_msgData_1941_);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1956_, v___y_1957_);
lean_dec(v___y_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Elab_Command_getRef___redArg(v___y_1961_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v_macroStack_1966_; lean_object* v___x_1967_; lean_object* v_a_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1979_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v_macroStack_1966_ = lean_ctor_get(v___y_1961_, 4);
v___x_1967_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1960_, v___y_1962_);
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1967_);
v___x_1969_ = l_Lean_Elab_getBetterRef(v_a_1965_, v_macroStack_1966_);
lean_dec(v_a_1965_);
lean_inc(v_macroStack_1966_);
v___x_1970_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1968_, v_macroStack_1966_, v___y_1962_);
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1969_);
lean_ctor_set(v___x_1975_, 1, v_a_1971_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set_tag(v___x_1973_, 1);
lean_ctor_set(v___x_1973_, 0, v___x_1975_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v_msg_1960_);
v_a_1980_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1964_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1964_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_1993_, lean_object* v_msg_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_Elab_Command_getRef___redArg(v___y_1995_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v_fileName_2000_; lean_object* v_fileMap_2001_; lean_object* v_currRecDepth_2002_; lean_object* v_cmdPos_2003_; lean_object* v_macroStack_2004_; lean_object* v_quotContext_x3f_2005_; lean_object* v_currMacroScope_2006_; lean_object* v_snap_x3f_2007_; lean_object* v_cancelTk_x3f_2008_; uint8_t v_suppressElabErrors_2009_; lean_object* v_ref_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v_fileName_2000_ = lean_ctor_get(v___y_1995_, 0);
v_fileMap_2001_ = lean_ctor_get(v___y_1995_, 1);
v_currRecDepth_2002_ = lean_ctor_get(v___y_1995_, 2);
v_cmdPos_2003_ = lean_ctor_get(v___y_1995_, 3);
v_macroStack_2004_ = lean_ctor_get(v___y_1995_, 4);
v_quotContext_x3f_2005_ = lean_ctor_get(v___y_1995_, 5);
v_currMacroScope_2006_ = lean_ctor_get(v___y_1995_, 6);
v_snap_x3f_2007_ = lean_ctor_get(v___y_1995_, 8);
v_cancelTk_x3f_2008_ = lean_ctor_get(v___y_1995_, 9);
v_suppressElabErrors_2009_ = lean_ctor_get_uint8(v___y_1995_, sizeof(void*)*10);
v_ref_2010_ = l_Lean_replaceRef(v_ref_1993_, v_a_1999_);
lean_dec(v_a_1999_);
lean_inc(v_cancelTk_x3f_2008_);
lean_inc(v_snap_x3f_2007_);
lean_inc(v_currMacroScope_2006_);
lean_inc(v_quotContext_x3f_2005_);
lean_inc(v_macroStack_2004_);
lean_inc(v_cmdPos_2003_);
lean_inc(v_currRecDepth_2002_);
lean_inc_ref(v_fileMap_2001_);
lean_inc_ref(v_fileName_2000_);
v___x_2011_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2011_, 0, v_fileName_2000_);
lean_ctor_set(v___x_2011_, 1, v_fileMap_2001_);
lean_ctor_set(v___x_2011_, 2, v_currRecDepth_2002_);
lean_ctor_set(v___x_2011_, 3, v_cmdPos_2003_);
lean_ctor_set(v___x_2011_, 4, v_macroStack_2004_);
lean_ctor_set(v___x_2011_, 5, v_quotContext_x3f_2005_);
lean_ctor_set(v___x_2011_, 6, v_currMacroScope_2006_);
lean_ctor_set(v___x_2011_, 7, v_ref_2010_);
lean_ctor_set(v___x_2011_, 8, v_snap_x3f_2007_);
lean_ctor_set(v___x_2011_, 9, v_cancelTk_x3f_2008_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*10, v_suppressElabErrors_2009_);
v___x_2012_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1994_, v___x_2011_, v___y_1996_);
lean_dec_ref_known(v___x_2011_, 10);
return v___x_2012_;
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_msg_1994_);
v_a_2013_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1998_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1998_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_2021_, lean_object* v_msg_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_2021_, v_msg_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v_ref_2021_);
return v_res_2026_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_2029_ = l_Lean_stringToMessageData(v___x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_val_2044_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_unsigned_to_nat(1u);
v___x_2052_ = l_Lean_Syntax_getArg(v_stx_2033_, v___x_2051_);
switch(lean_obj_tag(v___x_2052_))
{
case 2:
{
lean_object* v_val_2053_; 
lean_dec(v_stx_2033_);
v_val_2053_ = lean_ctor_get(v___x_2052_, 1);
lean_inc_ref(v_val_2053_);
lean_dec_ref_known(v___x_2052_, 2);
v_val_2044_ = v_val_2053_;
goto v___jp_2043_;
}
case 1:
{
lean_object* v_kind_2054_; 
v_kind_2054_ = lean_ctor_get(v___x_2052_, 1);
lean_inc(v_kind_2054_);
if (lean_obj_tag(v_kind_2054_) == 1)
{
lean_object* v_pre_2055_; 
v_pre_2055_ = lean_ctor_get(v_kind_2054_, 0);
lean_inc(v_pre_2055_);
if (lean_obj_tag(v_pre_2055_) == 1)
{
lean_object* v_pre_2056_; 
v_pre_2056_ = lean_ctor_get(v_pre_2055_, 0);
lean_inc(v_pre_2056_);
if (lean_obj_tag(v_pre_2056_) == 1)
{
lean_object* v_pre_2057_; 
v_pre_2057_ = lean_ctor_get(v_pre_2056_, 0);
lean_inc(v_pre_2057_);
if (lean_obj_tag(v_pre_2057_) == 1)
{
lean_object* v_pre_2058_; 
v_pre_2058_ = lean_ctor_get(v_pre_2057_, 0);
if (lean_obj_tag(v_pre_2058_) == 0)
{
lean_object* v_str_2059_; lean_object* v_str_2060_; lean_object* v_str_2061_; lean_object* v_str_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_str_2059_ = lean_ctor_get(v_kind_2054_, 1);
lean_inc_ref(v_str_2059_);
lean_dec_ref_known(v_kind_2054_, 2);
v_str_2060_ = lean_ctor_get(v_pre_2055_, 1);
lean_inc_ref(v_str_2060_);
lean_dec_ref_known(v_pre_2055_, 2);
v_str_2061_ = lean_ctor_get(v_pre_2056_, 1);
lean_inc_ref(v_str_2061_);
lean_dec_ref_known(v_pre_2056_, 2);
v_str_2062_ = lean_ctor_get(v_pre_2057_, 1);
lean_inc_ref(v_str_2062_);
lean_dec_ref_known(v_pre_2057_, 2);
v___x_2063_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_2064_ = lean_string_dec_eq(v_str_2062_, v___x_2063_);
lean_dec_ref(v_str_2062_);
if (v___x_2064_ == 0)
{
lean_dec_ref(v_str_2061_);
lean_dec_ref(v_str_2060_);
lean_dec_ref(v_str_2059_);
lean_dec_ref_known(v___x_2052_, 3);
goto v___jp_2037_;
}
else
{
lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2065_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2066_ = lean_string_dec_eq(v_str_2061_, v___x_2065_);
lean_dec_ref(v_str_2061_);
if (v___x_2066_ == 0)
{
lean_dec_ref(v_str_2060_);
lean_dec_ref(v_str_2059_);
lean_dec_ref_known(v___x_2052_, 3);
goto v___jp_2037_;
}
else
{
lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2067_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2068_ = lean_string_dec_eq(v_str_2060_, v___x_2067_);
lean_dec_ref(v_str_2060_);
if (v___x_2068_ == 0)
{
lean_dec_ref(v_str_2059_);
lean_dec_ref_known(v___x_2052_, 3);
goto v___jp_2037_;
}
else
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2070_ = lean_string_dec_eq(v_str_2059_, v___x_2069_);
lean_dec_ref(v_str_2059_);
if (v___x_2070_ == 0)
{
lean_dec_ref_known(v___x_2052_, 3);
goto v___jp_2037_;
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = l_Lean_Syntax_getArg(v___x_2052_, v___x_2071_);
lean_dec_ref_known(v___x_2052_, 3);
if (lean_obj_tag(v___x_2072_) == 2)
{
lean_object* v_val_2073_; 
lean_dec(v_stx_2033_);
v_val_2073_ = lean_ctor_get(v___x_2072_, 1);
lean_inc_ref(v_val_2073_);
lean_dec_ref_known(v___x_2072_, 2);
v_val_2044_ = v_val_2073_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec(v___x_2072_);
v___x_2074_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2033_);
v___x_2075_ = l_Lean_MessageData_ofSyntax(v_stx_2033_);
v___x_2076_ = l_Lean_indentD(v___x_2075_);
v___x_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2074_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2033_, v___x_2077_, v___y_2034_, v___y_2035_);
lean_dec(v_stx_2033_);
return v___x_2078_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2057_, 2);
lean_dec_ref_known(v_pre_2056_, 2);
lean_dec_ref_known(v_pre_2055_, 2);
lean_dec_ref_known(v_kind_2054_, 2);
lean_dec_ref_known(v___x_2052_, 3);
goto v___jp_2037_;
}
}
else
{
lean_dec_ref_known(v_pre_2056_, 2);
lean_dec(v_pre_2057_);
lean_dec_ref_known(v_pre_2055_, 2);
lean_dec_ref_known(v_kind_2054_, 2);
lean_dec_ref_known(v___x_2052_, 3);
goto v___jp_2037_;
}
}
else
{
lean_dec_ref_known(v_pre_2055_, 2);
lean_dec(v_pre_2056_);
lean_dec_ref_known(v_kind_2054_, 2);
lean_dec_ref_known(v___x_2052_, 3);
goto v___jp_2037_;
}
}
else
{
lean_dec_ref_known(v_kind_2054_, 2);
lean_dec(v_pre_2055_);
lean_dec_ref_known(v___x_2052_, 3);
goto v___jp_2037_;
}
}
else
{
lean_dec(v_kind_2054_);
lean_dec_ref_known(v___x_2052_, 3);
goto v___jp_2037_;
}
}
default: 
{
lean_dec(v___x_2052_);
goto v___jp_2037_;
}
}
v___jp_2037_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2038_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2033_);
v___x_2039_ = l_Lean_MessageData_ofSyntax(v_stx_2033_);
v___x_2040_ = l_Lean_indentD(v___x_2039_);
v___x_2041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2038_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2033_, v___x_2041_, v___y_2034_, v___y_2035_);
lean_dec(v_stx_2033_);
return v___x_2042_;
}
v___jp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = lean_string_utf8_byte_size(v_val_2044_);
v___x_2047_ = lean_unsigned_to_nat(2u);
v___x_2048_ = lean_nat_sub(v___x_2046_, v___x_2047_);
v___x_2049_ = lean_string_utf8_extract(v_val_2044_, v___x_2045_, v___x_2048_);
lean_dec(v___x_2048_);
lean_dec_ref(v_val_2044_);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
return v___x_2050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2084_, size_t v_sz_2085_, size_t v_i_2086_, lean_object* v_b_2087_){
_start:
{
lean_object* v_a_2089_; uint8_t v___x_2093_; 
v___x_2093_ = lean_usize_dec_lt(v_i_2086_, v_sz_2085_);
if (v___x_2093_ == 0)
{
return v_b_2087_;
}
else
{
lean_object* v_a_2094_; lean_object* v_fst_2095_; lean_object* v_snd_2096_; lean_object* v_out_2097_; uint8_t v___x_2098_; 
v_a_2094_ = lean_array_uget_borrowed(v_as_2084_, v_i_2086_);
v_fst_2095_ = lean_ctor_get(v_a_2094_, 0);
v_snd_2096_ = lean_ctor_get(v_a_2094_, 1);
v_out_2097_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2098_ = lean_string_dec_eq(v_snd_2096_, v_out_2097_);
if (v___x_2098_ == 0)
{
uint8_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2099_ = lean_unbox(v_fst_2095_);
v___x_2100_ = l_Lean_Diff_Action_linePrefix(v___x_2099_);
v___x_2101_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2102_ = lean_string_append(v___x_2100_, v___x_2101_);
v___x_2103_ = lean_string_append(v___x_2102_, v_snd_2096_);
v___x_2104_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2105_ = lean_string_append(v___x_2103_, v___x_2104_);
v___x_2106_ = lean_string_append(v_b_2087_, v___x_2105_);
lean_dec_ref(v___x_2105_);
v_a_2089_ = v___x_2106_;
goto v___jp_2088_;
}
else
{
uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2107_ = lean_unbox(v_fst_2095_);
v___x_2108_ = l_Lean_Diff_Action_linePrefix(v___x_2107_);
v___x_2109_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2110_ = lean_string_append(v___x_2108_, v___x_2109_);
v___x_2111_ = lean_string_append(v_b_2087_, v___x_2110_);
lean_dec_ref(v___x_2110_);
v_a_2089_ = v___x_2111_;
goto v___jp_2088_;
}
}
v___jp_2088_:
{
size_t v___x_2090_; size_t v___x_2091_; 
v___x_2090_ = ((size_t)1ULL);
v___x_2091_ = lean_usize_add(v_i_2086_, v___x_2090_);
v_i_2086_ = v___x_2091_;
v_b_2087_ = v_a_2089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2112_, lean_object* v_sz_2113_, lean_object* v_i_2114_, lean_object* v_b_2115_){
_start:
{
size_t v_sz_boxed_2116_; size_t v_i_boxed_2117_; lean_object* v_res_2118_; 
v_sz_boxed_2116_ = lean_unbox_usize(v_sz_2113_);
lean_dec(v_sz_2113_);
v_i_boxed_2117_ = lean_unbox_usize(v_i_2114_);
lean_dec(v_i_2114_);
v_res_2118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2112_, v_sz_boxed_2116_, v_i_boxed_2117_, v_b_2115_);
lean_dec_ref(v_as_2112_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2119_){
_start:
{
lean_object* v_out_2120_; size_t v_sz_2121_; size_t v___x_2122_; lean_object* v___x_2123_; 
v_out_2120_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v_sz_2121_ = lean_array_size(v_lines_2119_);
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2119_, v_sz_2121_, v___x_2122_, v_out_2120_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2124_);
lean_dec_ref(v_lines_2124_);
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2172_, lean_object* v_a_2173_, uint8_t v_b_2174_){
_start:
{
uint8_t v___x_2175_; 
v___x_2175_ = 0;
switch(lean_obj_tag(v_a_2173_))
{
case 0:
{
uint8_t v___x_2176_; 
lean_dec_ref_known(v_a_2173_, 1);
v___x_2176_ = 1;
return v___x_2176_;
}
case 1:
{
lean_object* v_pos_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2190_; 
v_pos_2177_ = lean_ctor_get(v_a_2173_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_a_2173_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2179_ = v_a_2173_;
v_isShared_2180_ = v_isSharedCheck_2190_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_pos_2177_);
lean_dec(v_a_2173_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2190_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_str_2181_; lean_object* v_startInclusive_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
v_str_2181_ = lean_ctor_get(v_s_2172_, 0);
v_startInclusive_2182_ = lean_ctor_get(v_s_2172_, 1);
v___x_2183_ = lean_nat_add(v_startInclusive_2182_, v_pos_2177_);
lean_dec(v_pos_2177_);
v___x_2184_ = lean_string_utf8_next_fast(v_str_2181_, v___x_2183_);
lean_dec(v___x_2183_);
v___x_2185_ = lean_nat_sub(v___x_2184_, v_startInclusive_2182_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set_tag(v___x_2179_, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2185_);
v___x_2187_ = v___x_2179_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
v_a_2173_ = v___x_2187_;
v_b_2174_ = v___x_2175_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2191_; lean_object* v_table_2192_; lean_object* v_stackPos_2193_; lean_object* v_needlePos_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2247_; 
v_needle_2191_ = lean_ctor_get(v_a_2173_, 0);
v_table_2192_ = lean_ctor_get(v_a_2173_, 1);
v_stackPos_2193_ = lean_ctor_get(v_a_2173_, 2);
v_needlePos_2194_ = lean_ctor_get(v_a_2173_, 3);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_a_2173_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2196_ = v_a_2173_;
v_isShared_2197_ = v_isSharedCheck_2247_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_needlePos_2194_);
lean_inc(v_stackPos_2193_);
lean_inc(v_table_2192_);
lean_inc(v_needle_2191_);
lean_dec(v_a_2173_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2247_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v_str_2198_; lean_object* v_startInclusive_2199_; lean_object* v_endExclusive_2200_; lean_object* v_str_2201_; lean_object* v_startInclusive_2202_; lean_object* v_endExclusive_2203_; lean_object* v_basePos_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v_str_2198_ = lean_ctor_get(v_needle_2191_, 0);
v_startInclusive_2199_ = lean_ctor_get(v_needle_2191_, 1);
v_endExclusive_2200_ = lean_ctor_get(v_needle_2191_, 2);
v_str_2201_ = lean_ctor_get(v_s_2172_, 0);
v_startInclusive_2202_ = lean_ctor_get(v_s_2172_, 1);
v_endExclusive_2203_ = lean_ctor_get(v_s_2172_, 2);
v_basePos_2204_ = lean_nat_sub(v_stackPos_2193_, v_needlePos_2194_);
v___x_2205_ = lean_nat_sub(v_endExclusive_2200_, v_startInclusive_2199_);
v___x_2206_ = lean_nat_add(v_basePos_2204_, v___x_2205_);
v___x_2207_ = lean_nat_sub(v_endExclusive_2203_, v_startInclusive_2202_);
v___x_2208_ = lean_nat_dec_le(v___x_2206_, v___x_2207_);
lean_dec(v___x_2206_);
if (v___x_2208_ == 0)
{
uint8_t v___x_2209_; 
lean_dec(v___x_2205_);
lean_del_object(v___x_2196_);
lean_dec(v_needlePos_2194_);
lean_dec(v_stackPos_2193_);
lean_dec_ref(v_table_2192_);
lean_dec_ref(v_needle_2191_);
v___x_2209_ = lean_nat_dec_lt(v_basePos_2204_, v___x_2207_);
lean_dec(v___x_2207_);
lean_dec(v_basePos_2204_);
if (v___x_2209_ == 0)
{
return v_b_2174_;
}
else
{
lean_object* v___x_2210_; 
v___x_2210_ = lean_box(3);
v_a_2173_ = v___x_2210_;
v_b_2174_ = v___x_2175_;
goto _start;
}
}
else
{
lean_object* v___x_2212_; uint8_t v_stackByte_2213_; lean_object* v___x_2214_; uint8_t v_patByte_2215_; uint8_t v___x_2216_; 
lean_dec(v___x_2207_);
lean_dec(v_basePos_2204_);
v___x_2212_ = lean_nat_add(v_startInclusive_2202_, v_stackPos_2193_);
v_stackByte_2213_ = lean_string_get_byte_fast(v_str_2201_, v___x_2212_);
v___x_2214_ = lean_nat_add(v_startInclusive_2199_, v_needlePos_2194_);
v_patByte_2215_ = lean_string_get_byte_fast(v_str_2198_, v___x_2214_);
v___x_2216_ = lean_uint8_dec_eq(v_stackByte_2213_, v_patByte_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; uint8_t v___x_2218_; 
lean_dec(v___x_2205_);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = lean_nat_dec_eq(v_needlePos_2194_, v___x_2217_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v_newNeedlePos_2221_; uint8_t v___x_2222_; 
v___x_2219_ = lean_unsigned_to_nat(1u);
v___x_2220_ = lean_nat_sub(v_needlePos_2194_, v___x_2219_);
lean_dec(v_needlePos_2194_);
v_newNeedlePos_2221_ = lean_array_fget_borrowed(v_table_2192_, v___x_2220_);
lean_dec(v___x_2220_);
v___x_2222_ = lean_nat_dec_eq(v_newNeedlePos_2221_, v___x_2217_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2224_; 
lean_inc(v_newNeedlePos_2221_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 3, v_newNeedlePos_2221_);
v___x_2224_ = v___x_2196_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_needle_2191_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_table_2192_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_stackPos_2193_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_newNeedlePos_2221_);
v___x_2224_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
v_a_2173_ = v___x_2224_;
v_b_2174_ = v___x_2175_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2227_; lean_object* v___x_2229_; 
v_nextStackPos_2227_ = l_String_Slice_posGE___redArg(v_s_2172_, v_stackPos_2193_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 3, v___x_2217_);
lean_ctor_set(v___x_2196_, 2, v_nextStackPos_2227_);
v___x_2229_ = v___x_2196_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_needle_2191_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_table_2192_);
lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_nextStackPos_2227_);
lean_ctor_set(v_reuseFailAlloc_2231_, 3, v___x_2217_);
v___x_2229_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
v_a_2173_ = v___x_2229_;
v_b_2174_ = v___x_2175_;
goto _start;
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v_nextStackPos_2234_; lean_object* v___x_2236_; 
lean_dec(v_needlePos_2194_);
v___x_2232_ = lean_unsigned_to_nat(1u);
v___x_2233_ = lean_nat_add(v_stackPos_2193_, v___x_2232_);
lean_dec(v_stackPos_2193_);
v_nextStackPos_2234_ = l_String_Slice_posGE___redArg(v_s_2172_, v___x_2233_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 3, v___x_2217_);
lean_ctor_set(v___x_2196_, 2, v_nextStackPos_2234_);
v___x_2236_ = v___x_2196_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_needle_2191_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_table_2192_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_nextStackPos_2234_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v___x_2217_);
v___x_2236_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
v_a_2173_ = v___x_2236_;
v_b_2174_ = v___x_2175_;
goto _start;
}
}
}
else
{
lean_object* v___x_2239_; lean_object* v_nextNeedlePos_2240_; uint8_t v___x_2241_; 
v___x_2239_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2240_ = lean_nat_add(v_needlePos_2194_, v___x_2239_);
lean_dec(v_needlePos_2194_);
v___x_2241_ = lean_nat_dec_eq(v_nextNeedlePos_2240_, v___x_2205_);
lean_dec(v___x_2205_);
if (v___x_2241_ == 0)
{
lean_object* v_nextStackPos_2242_; lean_object* v___x_2244_; 
v_nextStackPos_2242_ = lean_nat_add(v_stackPos_2193_, v___x_2239_);
lean_dec(v_stackPos_2193_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 3, v_nextNeedlePos_2240_);
lean_ctor_set(v___x_2196_, 2, v_nextStackPos_2242_);
v___x_2244_ = v___x_2196_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_needle_2191_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_table_2192_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_nextStackPos_2242_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v_nextNeedlePos_2240_);
v___x_2244_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
v_a_2173_ = v___x_2244_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2240_);
lean_del_object(v___x_2196_);
lean_dec(v_stackPos_2193_);
lean_dec_ref(v_table_2192_);
lean_dec_ref(v_needle_2191_);
return v___x_2241_;
}
}
}
}
}
default: 
{
return v_b_2174_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2248_, lean_object* v_a_2249_, lean_object* v_b_2250_){
_start:
{
uint8_t v_b_boxed_2251_; uint8_t v_res_2252_; lean_object* v_r_2253_; 
v_b_boxed_2251_ = lean_unbox(v_b_2250_);
v_res_2252_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2248_, v_a_2249_, v_b_boxed_2251_);
lean_dec_ref(v_s_2248_);
v_r_2253_ = lean_box(v_res_2252_);
return v_r_2253_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2254_, lean_object* v_s_2255_){
_start:
{
lean_object* v___y_2257_; lean_object* v___x_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2260_ = lean_unsigned_to_nat(0u);
v___x_2261_ = lean_string_utf8_byte_size(v___x_2254_);
v___x_2262_ = lean_nat_dec_eq(v___x_2261_, v___x_2260_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2254_);
lean_ctor_set(v___x_2263_, 1, v___x_2260_);
lean_ctor_set(v___x_2263_, 2, v___x_2261_);
v___x_2264_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2263_);
v___x_2265_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2263_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
lean_ctor_set(v___x_2265_, 2, v___x_2260_);
lean_ctor_set(v___x_2265_, 3, v___x_2260_);
v___y_2257_ = v___x_2265_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2266_; 
lean_dec_ref(v___x_2254_);
v___x_2266_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_2257_ = v___x_2266_;
goto v___jp_2256_;
}
v___jp_2256_:
{
uint8_t v___x_2258_; uint8_t v___x_2259_; 
v___x_2258_ = 0;
v___x_2259_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2255_, v___y_2257_, v___x_2258_);
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2267_, lean_object* v_s_2268_){
_start:
{
uint8_t v_res_2269_; lean_object* v_r_2270_; 
v_res_2269_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2267_, v_s_2268_);
lean_dec_ref(v_s_2268_);
v_r_2270_ = lean_box(v_res_2269_);
return v_r_2270_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v___y_2271_, uint8_t v_suppressElabErrors_2272_, lean_object* v_x_2273_){
_start:
{
if (lean_obj_tag(v_x_2273_) == 1)
{
lean_object* v_pre_2274_; 
v_pre_2274_ = lean_ctor_get(v_x_2273_, 0);
if (lean_obj_tag(v_pre_2274_) == 0)
{
lean_object* v_str_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v_str_2275_ = lean_ctor_get(v_x_2273_, 1);
v___x_2276_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2277_ = lean_string_dec_eq(v_str_2275_, v___x_2276_);
if (v___x_2277_ == 0)
{
return v___y_2271_;
}
else
{
return v_suppressElabErrors_2272_;
}
}
else
{
return v___y_2271_;
}
}
else
{
return v___y_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v___y_2278_, lean_object* v_suppressElabErrors_2279_, lean_object* v_x_2280_){
_start:
{
uint8_t v___y_29379__boxed_2281_; uint8_t v_suppressElabErrors_boxed_2282_; uint8_t v_res_2283_; lean_object* v_r_2284_; 
v___y_29379__boxed_2281_ = lean_unbox(v___y_2278_);
v_suppressElabErrors_boxed_2282_ = lean_unbox(v_suppressElabErrors_2279_);
v_res_2283_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v___y_29379__boxed_2281_, v_suppressElabErrors_boxed_2282_, v_x_2280_);
lean_dec(v_x_2280_);
v_r_2284_ = lean_box(v_res_2283_);
return v_r_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2285_, lean_object* v_msgData_2286_, uint8_t v_severity_2287_, uint8_t v_isSilent_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
uint8_t v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; uint8_t v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; uint8_t v___y_2357_; uint8_t v___y_2358_; lean_object* v___y_2359_; uint8_t v___y_2360_; lean_object* v___y_2361_; uint8_t v___y_2385_; lean_object* v___y_2386_; uint8_t v___y_2387_; uint8_t v___y_2388_; lean_object* v___y_2389_; uint8_t v___y_2393_; uint8_t v___y_2394_; uint8_t v___y_2395_; uint8_t v___x_2410_; uint8_t v___y_2412_; uint8_t v___y_2413_; uint8_t v___y_2414_; uint8_t v___y_2416_; uint8_t v___x_2428_; 
v___x_2410_ = 2;
v___x_2428_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2287_, v___x_2410_);
if (v___x_2428_ == 0)
{
v___y_2416_ = v___x_2428_;
goto v___jp_2415_;
}
else
{
uint8_t v___x_2429_; 
lean_inc_ref(v_msgData_2286_);
v___x_2429_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2286_);
v___y_2416_ = v___x_2429_;
goto v___jp_2415_;
}
v___jp_2292_:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_Elab_Command_getScope___redArg(v___y_2300_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = l_Lean_Elab_Command_getScope___redArg(v___y_2300_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2339_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2339_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2339_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v_currNamespace_2309_; lean_object* v_openDecls_2310_; lean_object* v_env_2311_; lean_object* v_messages_2312_; lean_object* v_scopes_2313_; lean_object* v_usedQuotCtxts_2314_; lean_object* v_nextMacroScope_2315_; lean_object* v_maxRecDepth_2316_; lean_object* v_ngen_2317_; lean_object* v_auxDeclNGen_2318_; lean_object* v_infoState_2319_; lean_object* v_traceState_2320_; lean_object* v_snapshotTasks_2321_; lean_object* v_prevLinterStates_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2338_; 
v___x_2308_ = lean_st_ref_take(v___y_2300_);
v_currNamespace_2309_ = lean_ctor_get(v_a_2302_, 2);
lean_inc(v_currNamespace_2309_);
lean_dec(v_a_2302_);
v_openDecls_2310_ = lean_ctor_get(v_a_2304_, 3);
lean_inc(v_openDecls_2310_);
lean_dec(v_a_2304_);
v_env_2311_ = lean_ctor_get(v___x_2308_, 0);
v_messages_2312_ = lean_ctor_get(v___x_2308_, 1);
v_scopes_2313_ = lean_ctor_get(v___x_2308_, 2);
v_usedQuotCtxts_2314_ = lean_ctor_get(v___x_2308_, 3);
v_nextMacroScope_2315_ = lean_ctor_get(v___x_2308_, 4);
v_maxRecDepth_2316_ = lean_ctor_get(v___x_2308_, 5);
v_ngen_2317_ = lean_ctor_get(v___x_2308_, 6);
v_auxDeclNGen_2318_ = lean_ctor_get(v___x_2308_, 7);
v_infoState_2319_ = lean_ctor_get(v___x_2308_, 8);
v_traceState_2320_ = lean_ctor_get(v___x_2308_, 9);
v_snapshotTasks_2321_ = lean_ctor_get(v___x_2308_, 10);
v_prevLinterStates_2322_ = lean_ctor_get(v___x_2308_, 11);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2324_ = v___x_2308_;
v_isShared_2325_ = v_isSharedCheck_2338_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_prevLinterStates_2322_);
lean_inc(v_snapshotTasks_2321_);
lean_inc(v_traceState_2320_);
lean_inc(v_infoState_2319_);
lean_inc(v_auxDeclNGen_2318_);
lean_inc(v_ngen_2317_);
lean_inc(v_maxRecDepth_2316_);
lean_inc(v_nextMacroScope_2315_);
lean_inc(v_usedQuotCtxts_2314_);
lean_inc(v_scopes_2313_);
lean_inc(v_messages_2312_);
lean_inc(v_env_2311_);
lean_dec(v___x_2308_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2338_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v_currNamespace_2309_);
lean_ctor_set(v___x_2326_, 1, v_openDecls_2310_);
v___x_2327_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___y_2294_);
lean_inc_ref(v___y_2299_);
lean_inc_ref(v___y_2295_);
v___x_2328_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2328_, 0, v___y_2295_);
lean_ctor_set(v___x_2328_, 1, v___y_2297_);
lean_ctor_set(v___x_2328_, 2, v___y_2296_);
lean_ctor_set(v___x_2328_, 3, v___y_2299_);
lean_ctor_set(v___x_2328_, 4, v___x_2327_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*5, v___y_2298_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*5 + 1, v___y_2293_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*5 + 2, v_isSilent_2288_);
v___x_2329_ = l_Lean_MessageLog_add(v___x_2328_, v_messages_2312_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 1, v___x_2329_);
v___x_2331_ = v___x_2324_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_env_2311_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_scopes_2313_);
lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_usedQuotCtxts_2314_);
lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_nextMacroScope_2315_);
lean_ctor_set(v_reuseFailAlloc_2337_, 5, v_maxRecDepth_2316_);
lean_ctor_set(v_reuseFailAlloc_2337_, 6, v_ngen_2317_);
lean_ctor_set(v_reuseFailAlloc_2337_, 7, v_auxDeclNGen_2318_);
lean_ctor_set(v_reuseFailAlloc_2337_, 8, v_infoState_2319_);
lean_ctor_set(v_reuseFailAlloc_2337_, 9, v_traceState_2320_);
lean_ctor_set(v_reuseFailAlloc_2337_, 10, v_snapshotTasks_2321_);
lean_ctor_set(v_reuseFailAlloc_2337_, 11, v_prevLinterStates_2322_);
v___x_2331_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2332_ = lean_st_ref_set(v___y_2300_, v___x_2331_);
v___x_2333_ = lean_box(0);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2333_);
v___x_2335_ = v___x_2306_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
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
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_a_2302_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2294_);
v_a_2340_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2303_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2303_);
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
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2294_);
v_a_2348_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2301_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2301_);
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
v___jp_2356_:
{
lean_object* v_fileName_2362_; lean_object* v_fileMap_2363_; uint8_t v_suppressElabErrors_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2383_; 
v_fileName_2362_ = lean_ctor_get(v___y_2289_, 0);
v_fileMap_2363_ = lean_ctor_get(v___y_2289_, 1);
v_suppressElabErrors_2364_ = lean_ctor_get_uint8(v___y_2289_, sizeof(void*)*10);
v___x_2365_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2286_);
v___x_2366_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2365_, v___y_2290_);
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2383_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2383_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_inc_ref_n(v_fileMap_2363_, 2);
v___x_2371_ = l_Lean_FileMap_toPosition(v_fileMap_2363_, v___y_2359_);
lean_dec(v___y_2359_);
v___x_2372_ = l_Lean_FileMap_toPosition(v_fileMap_2363_, v___y_2361_);
lean_dec(v___y_2361_);
v___x_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
v___x_2374_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
if (v_suppressElabErrors_2364_ == 0)
{
lean_del_object(v___x_2369_);
v___y_2293_ = v___y_2358_;
v___y_2294_ = v_a_2367_;
v___y_2295_ = v_fileName_2362_;
v___y_2296_ = v___x_2373_;
v___y_2297_ = v___x_2371_;
v___y_2298_ = v___y_2360_;
v___y_2299_ = v___x_2374_;
v___y_2300_ = v___y_2290_;
goto v___jp_2292_;
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; uint8_t v___x_2378_; 
v___x_2375_ = lean_box(v___y_2357_);
v___x_2376_ = lean_box(v_suppressElabErrors_2364_);
v___f_2377_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2377_, 0, v___x_2375_);
lean_closure_set(v___f_2377_, 1, v___x_2376_);
lean_inc(v_a_2367_);
v___x_2378_ = l_Lean_MessageData_hasTag(v___f_2377_, v_a_2367_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
lean_dec_ref_known(v___x_2373_, 1);
lean_dec_ref(v___x_2371_);
lean_dec(v_a_2367_);
v___x_2379_ = lean_box(0);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2379_);
v___x_2381_ = v___x_2369_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
else
{
lean_del_object(v___x_2369_);
v___y_2293_ = v___y_2358_;
v___y_2294_ = v_a_2367_;
v___y_2295_ = v_fileName_2362_;
v___y_2296_ = v___x_2373_;
v___y_2297_ = v___x_2371_;
v___y_2298_ = v___y_2360_;
v___y_2299_ = v___x_2374_;
v___y_2300_ = v___y_2290_;
goto v___jp_2292_;
}
}
}
}
v___jp_2384_:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_Syntax_getTailPos_x3f(v___y_2386_, v___y_2388_);
lean_dec(v___y_2386_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_inc(v___y_2389_);
v___y_2357_ = v___y_2385_;
v___y_2358_ = v___y_2387_;
v___y_2359_ = v___y_2389_;
v___y_2360_ = v___y_2388_;
v___y_2361_ = v___y_2389_;
goto v___jp_2356_;
}
else
{
lean_object* v_val_2391_; 
v_val_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_val_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___y_2357_ = v___y_2385_;
v___y_2358_ = v___y_2387_;
v___y_2359_ = v___y_2389_;
v___y_2360_ = v___y_2388_;
v___y_2361_ = v_val_2391_;
goto v___jp_2356_;
}
}
v___jp_2392_:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_Elab_Command_getRef___redArg(v___y_2289_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v_ref_2398_; lean_object* v___x_2399_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v_ref_2398_ = l_Lean_replaceRef(v_ref_2285_, v_a_2397_);
lean_dec(v_a_2397_);
v___x_2399_ = l_Lean_Syntax_getPos_x3f(v_ref_2398_, v___y_2394_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_unsigned_to_nat(0u);
v___y_2385_ = v___y_2393_;
v___y_2386_ = v_ref_2398_;
v___y_2387_ = v___y_2395_;
v___y_2388_ = v___y_2394_;
v___y_2389_ = v___x_2400_;
goto v___jp_2384_;
}
else
{
lean_object* v_val_2401_; 
v_val_2401_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_val_2401_);
lean_dec_ref_known(v___x_2399_, 1);
v___y_2385_ = v___y_2393_;
v___y_2386_ = v_ref_2398_;
v___y_2387_ = v___y_2395_;
v___y_2388_ = v___y_2394_;
v___y_2389_ = v_val_2401_;
goto v___jp_2384_;
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref(v_msgData_2286_);
v_a_2402_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2396_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2396_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
v___jp_2411_:
{
if (v___y_2414_ == 0)
{
v___y_2393_ = v___y_2412_;
v___y_2394_ = v___y_2413_;
v___y_2395_ = v_severity_2287_;
goto v___jp_2392_;
}
else
{
v___y_2393_ = v___y_2412_;
v___y_2394_ = v___y_2413_;
v___y_2395_ = v___x_2410_;
goto v___jp_2392_;
}
}
v___jp_2415_:
{
if (v___y_2416_ == 0)
{
lean_object* v___x_2417_; lean_object* v_scopes_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v_opts_2421_; uint8_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2417_ = lean_st_ref_get(v___y_2290_);
v_scopes_2418_ = lean_ctor_get(v___x_2417_, 2);
lean_inc(v_scopes_2418_);
lean_dec(v___x_2417_);
v___x_2419_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2420_ = l_List_head_x21___redArg(v___x_2419_, v_scopes_2418_);
lean_dec(v_scopes_2418_);
v_opts_2421_ = lean_ctor_get(v___x_2420_, 1);
lean_inc_ref(v_opts_2421_);
lean_dec(v___x_2420_);
v___x_2422_ = 1;
v___x_2423_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2287_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_dec_ref(v_opts_2421_);
v___y_2412_ = v___y_2416_;
v___y_2413_ = v___y_2416_;
v___y_2414_ = v___x_2423_;
goto v___jp_2411_;
}
else
{
lean_object* v___x_2424_; uint8_t v___x_2425_; 
v___x_2424_ = l_Lean_warningAsError;
v___x_2425_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2421_, v___x_2424_);
lean_dec_ref(v_opts_2421_);
v___y_2412_ = v___y_2416_;
v___y_2413_ = v___y_2416_;
v___y_2414_ = v___x_2425_;
goto v___jp_2411_;
}
}
else
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
lean_dec_ref(v_msgData_2286_);
v___x_2426_ = lean_box(0);
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
return v___x_2427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2430_, lean_object* v_msgData_2431_, lean_object* v_severity_2432_, lean_object* v_isSilent_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
uint8_t v_severity_boxed_2437_; uint8_t v_isSilent_boxed_2438_; lean_object* v_res_2439_; 
v_severity_boxed_2437_ = lean_unbox(v_severity_2432_);
v_isSilent_boxed_2438_ = lean_unbox(v_isSilent_2433_);
v_res_2439_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2430_, v_msgData_2431_, v_severity_boxed_2437_, v_isSilent_boxed_2438_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v_ref_2430_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2440_, lean_object* v_msgData_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
uint8_t v___x_2445_; uint8_t v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = 2;
v___x_2446_ = 0;
v___x_2447_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2440_, v_msgData_2441_, v___x_2445_, v___x_2446_, v___y_2442_, v___y_2443_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2448_, lean_object* v_msgData_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2448_, v_msgData_2449_, v___y_2450_, v___y_2451_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v_ref_2448_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2454_, lean_object* v___x_2455_, lean_object* v___x_2456_, lean_object* v_a_2457_, lean_object* v_b_2458_){
_start:
{
lean_object* v_it_2460_; lean_object* v_startInclusive_2461_; lean_object* v_endExclusive_2462_; 
if (lean_obj_tag(v_a_2457_) == 0)
{
lean_object* v_currPos_2467_; lean_object* v_searcher_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2497_; 
v_currPos_2467_ = lean_ctor_get(v_a_2457_, 0);
v_searcher_2468_ = lean_ctor_get(v_a_2457_, 1);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_a_2457_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2470_ = v_a_2457_;
v_isShared_2471_ = v_isSharedCheck_2497_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_searcher_2468_);
lean_inc(v_currPos_2467_);
lean_dec(v_a_2457_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2497_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v_str_2472_; lean_object* v_startInclusive_2473_; lean_object* v_endExclusive_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v_str_2472_ = lean_ctor_get(v___x_2455_, 0);
v_startInclusive_2473_ = lean_ctor_get(v___x_2455_, 1);
v_endExclusive_2474_ = lean_ctor_get(v___x_2455_, 2);
v___x_2475_ = lean_nat_sub(v_endExclusive_2474_, v_startInclusive_2473_);
v___x_2476_ = lean_nat_dec_eq(v_searcher_2468_, v___x_2475_);
lean_dec(v___x_2475_);
if (v___x_2476_ == 0)
{
uint32_t v___x_2477_; lean_object* v___x_2478_; uint32_t v___x_2479_; uint8_t v___x_2480_; 
v___x_2477_ = 10;
v___x_2478_ = lean_nat_add(v_startInclusive_2473_, v_searcher_2468_);
v___x_2479_ = lean_string_utf8_get_fast(v_str_2472_, v___x_2478_);
v___x_2480_ = lean_uint32_dec_eq(v___x_2479_, v___x_2477_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
lean_dec(v_searcher_2468_);
v___x_2481_ = lean_string_utf8_next_fast(v_str_2472_, v___x_2478_);
lean_dec(v___x_2478_);
v___x_2482_ = lean_nat_sub(v___x_2481_, v_startInclusive_2473_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 1, v___x_2482_);
v___x_2484_ = v___x_2470_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_currPos_2467_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
v_a_2457_ = v___x_2484_;
goto _start;
}
}
else
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v_slice_2490_; lean_object* v_nextIt_2492_; 
v___x_2487_ = lean_string_utf8_next_fast(v_str_2472_, v___x_2478_);
v___x_2488_ = lean_nat_sub(v___x_2487_, v___x_2478_);
lean_dec(v___x_2478_);
v___x_2489_ = lean_nat_add(v_searcher_2468_, v___x_2488_);
lean_dec(v___x_2488_);
v_slice_2490_ = l_String_Slice_subslice_x21(v___x_2455_, v_currPos_2467_, v_searcher_2468_);
lean_inc(v___x_2489_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 1, v___x_2489_);
lean_ctor_set(v___x_2470_, 0, v___x_2489_);
v_nextIt_2492_ = v___x_2470_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v___x_2489_);
v_nextIt_2492_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v_startInclusive_2493_; lean_object* v_endExclusive_2494_; 
v_startInclusive_2493_ = lean_ctor_get(v_slice_2490_, 0);
lean_inc(v_startInclusive_2493_);
v_endExclusive_2494_ = lean_ctor_get(v_slice_2490_, 1);
lean_inc(v_endExclusive_2494_);
lean_dec_ref(v_slice_2490_);
v_it_2460_ = v_nextIt_2492_;
v_startInclusive_2461_ = v_startInclusive_2493_;
v_endExclusive_2462_ = v_endExclusive_2494_;
goto v___jp_2459_;
}
}
}
else
{
lean_object* v___x_2496_; 
lean_del_object(v___x_2470_);
lean_dec(v_searcher_2468_);
v___x_2496_ = lean_box(1);
lean_inc(v___x_2456_);
v_it_2460_ = v___x_2496_;
v_startInclusive_2461_ = v_currPos_2467_;
v_endExclusive_2462_ = v___x_2456_;
goto v___jp_2459_;
}
}
}
else
{
lean_dec(v___x_2456_);
lean_dec_ref(v___x_2454_);
return v_b_2458_;
}
v___jp_2459_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
lean_inc_ref(v___x_2454_);
v___x_2463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2454_);
lean_ctor_set(v___x_2463_, 1, v_startInclusive_2461_);
lean_ctor_set(v___x_2463_, 2, v_endExclusive_2462_);
v___x_2464_ = l_String_Slice_toString(v___x_2463_);
lean_dec_ref_known(v___x_2463_, 3);
v___x_2465_ = lean_array_push(v_b_2458_, v___x_2464_);
v_a_2457_ = v_it_2460_;
v_b_2458_ = v___x_2465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2498_, lean_object* v___x_2499_, lean_object* v___x_2500_, lean_object* v_a_2501_, lean_object* v_b_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2498_, v___x_2499_, v___x_2500_, v_a_2501_, v_b_2502_);
lean_dec_ref(v___x_2499_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2504_, lean_object* v___x_2505_, lean_object* v___x_2506_, lean_object* v_a_2507_, lean_object* v_b_2508_){
_start:
{
lean_object* v_it_2510_; lean_object* v_startInclusive_2511_; lean_object* v_endExclusive_2512_; 
if (lean_obj_tag(v_a_2507_) == 0)
{
lean_object* v_currPos_2517_; lean_object* v_searcher_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2547_; 
v_currPos_2517_ = lean_ctor_get(v_a_2507_, 0);
v_searcher_2518_ = lean_ctor_get(v_a_2507_, 1);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_a_2507_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2520_ = v_a_2507_;
v_isShared_2521_ = v_isSharedCheck_2547_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_searcher_2518_);
lean_inc(v_currPos_2517_);
lean_dec(v_a_2507_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2547_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v_str_2522_; lean_object* v_startInclusive_2523_; lean_object* v_endExclusive_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_str_2522_ = lean_ctor_get(v___x_2505_, 0);
v_startInclusive_2523_ = lean_ctor_get(v___x_2505_, 1);
v_endExclusive_2524_ = lean_ctor_get(v___x_2505_, 2);
v___x_2525_ = lean_nat_sub(v_endExclusive_2524_, v_startInclusive_2523_);
v___x_2526_ = lean_nat_dec_eq(v_searcher_2518_, v___x_2525_);
lean_dec(v___x_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; uint32_t v___x_2528_; uint32_t v___x_2529_; uint8_t v___x_2530_; 
v___x_2527_ = lean_nat_add(v_startInclusive_2523_, v_searcher_2518_);
v___x_2528_ = lean_string_utf8_get_fast(v_str_2522_, v___x_2527_);
v___x_2529_ = 10;
v___x_2530_ = lean_uint32_dec_eq(v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2534_; 
lean_dec(v_searcher_2518_);
v___x_2531_ = lean_string_utf8_next_fast(v_str_2522_, v___x_2527_);
lean_dec(v___x_2527_);
v___x_2532_ = lean_nat_sub(v___x_2531_, v_startInclusive_2523_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 1, v___x_2532_);
v___x_2534_ = v___x_2520_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_currPos_2517_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2535_; 
v___x_2535_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2504_, v___x_2505_, v___x_2506_, v___x_2534_, v_b_2508_);
return v___x_2535_;
}
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v_slice_2540_; lean_object* v_nextIt_2542_; 
v___x_2537_ = lean_string_utf8_next_fast(v_str_2522_, v___x_2527_);
v___x_2538_ = lean_nat_sub(v___x_2537_, v___x_2527_);
lean_dec(v___x_2527_);
v___x_2539_ = lean_nat_add(v_searcher_2518_, v___x_2538_);
lean_dec(v___x_2538_);
v_slice_2540_ = l_String_Slice_subslice_x21(v___x_2505_, v_currPos_2517_, v_searcher_2518_);
lean_inc(v___x_2539_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 1, v___x_2539_);
lean_ctor_set(v___x_2520_, 0, v___x_2539_);
v_nextIt_2542_ = v___x_2520_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___x_2539_);
v_nextIt_2542_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v_startInclusive_2543_; lean_object* v_endExclusive_2544_; 
v_startInclusive_2543_ = lean_ctor_get(v_slice_2540_, 0);
lean_inc(v_startInclusive_2543_);
v_endExclusive_2544_ = lean_ctor_get(v_slice_2540_, 1);
lean_inc(v_endExclusive_2544_);
lean_dec_ref(v_slice_2540_);
v_it_2510_ = v_nextIt_2542_;
v_startInclusive_2511_ = v_startInclusive_2543_;
v_endExclusive_2512_ = v_endExclusive_2544_;
goto v___jp_2509_;
}
}
}
else
{
lean_object* v___x_2546_; 
lean_del_object(v___x_2520_);
lean_dec(v_searcher_2518_);
v___x_2546_ = lean_box(1);
lean_inc(v___x_2506_);
v_it_2510_ = v___x_2546_;
v_startInclusive_2511_ = v_currPos_2517_;
v_endExclusive_2512_ = v___x_2506_;
goto v___jp_2509_;
}
}
}
else
{
lean_dec(v___x_2506_);
lean_dec_ref(v___x_2504_);
return v_b_2508_;
}
v___jp_2509_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_inc_ref(v___x_2504_);
v___x_2513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2504_);
lean_ctor_set(v___x_2513_, 1, v_startInclusive_2511_);
lean_ctor_set(v___x_2513_, 2, v_endExclusive_2512_);
v___x_2514_ = l_String_Slice_toString(v___x_2513_);
lean_dec_ref_known(v___x_2513_, 3);
v___x_2515_ = lean_array_push(v_b_2508_, v___x_2514_);
v___x_2516_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2504_, v___x_2505_, v___x_2506_, v_it_2510_, v___x_2515_);
return v___x_2516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2548_, lean_object* v___x_2549_, lean_object* v___x_2550_, lean_object* v_a_2551_, lean_object* v_b_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2548_, v___x_2549_, v___x_2550_, v_a_2551_, v_b_2552_);
lean_dec_ref(v___x_2549_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; lean_object* v_infoState_2558_; uint8_t v_enabled_2559_; 
v___x_2557_ = lean_st_ref_get(v___y_2555_);
v_infoState_2558_ = lean_ctor_get(v___x_2557_, 8);
lean_inc_ref(v_infoState_2558_);
lean_dec(v___x_2557_);
v_enabled_2559_ = lean_ctor_get_uint8(v_infoState_2558_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2558_);
if (v_enabled_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
lean_dec_ref(v_t_2554_);
v___x_2560_ = lean_box(0);
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
else
{
lean_object* v___x_2562_; lean_object* v_infoState_2563_; lean_object* v_env_2564_; lean_object* v_messages_2565_; lean_object* v_scopes_2566_; lean_object* v_usedQuotCtxts_2567_; lean_object* v_nextMacroScope_2568_; lean_object* v_maxRecDepth_2569_; lean_object* v_ngen_2570_; lean_object* v_auxDeclNGen_2571_; lean_object* v_traceState_2572_; lean_object* v_snapshotTasks_2573_; lean_object* v_prevLinterStates_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2596_; 
v___x_2562_ = lean_st_ref_take(v___y_2555_);
v_infoState_2563_ = lean_ctor_get(v___x_2562_, 8);
v_env_2564_ = lean_ctor_get(v___x_2562_, 0);
v_messages_2565_ = lean_ctor_get(v___x_2562_, 1);
v_scopes_2566_ = lean_ctor_get(v___x_2562_, 2);
v_usedQuotCtxts_2567_ = lean_ctor_get(v___x_2562_, 3);
v_nextMacroScope_2568_ = lean_ctor_get(v___x_2562_, 4);
v_maxRecDepth_2569_ = lean_ctor_get(v___x_2562_, 5);
v_ngen_2570_ = lean_ctor_get(v___x_2562_, 6);
v_auxDeclNGen_2571_ = lean_ctor_get(v___x_2562_, 7);
v_traceState_2572_ = lean_ctor_get(v___x_2562_, 9);
v_snapshotTasks_2573_ = lean_ctor_get(v___x_2562_, 10);
v_prevLinterStates_2574_ = lean_ctor_get(v___x_2562_, 11);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2576_ = v___x_2562_;
v_isShared_2577_ = v_isSharedCheck_2596_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_prevLinterStates_2574_);
lean_inc(v_snapshotTasks_2573_);
lean_inc(v_traceState_2572_);
lean_inc(v_infoState_2563_);
lean_inc(v_auxDeclNGen_2571_);
lean_inc(v_ngen_2570_);
lean_inc(v_maxRecDepth_2569_);
lean_inc(v_nextMacroScope_2568_);
lean_inc(v_usedQuotCtxts_2567_);
lean_inc(v_scopes_2566_);
lean_inc(v_messages_2565_);
lean_inc(v_env_2564_);
lean_dec(v___x_2562_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2596_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
uint8_t v_enabled_2578_; lean_object* v_assignment_2579_; lean_object* v_lazyAssignment_2580_; lean_object* v_trees_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2595_; 
v_enabled_2578_ = lean_ctor_get_uint8(v_infoState_2563_, sizeof(void*)*3);
v_assignment_2579_ = lean_ctor_get(v_infoState_2563_, 0);
v_lazyAssignment_2580_ = lean_ctor_get(v_infoState_2563_, 1);
v_trees_2581_ = lean_ctor_get(v_infoState_2563_, 2);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_infoState_2563_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2583_ = v_infoState_2563_;
v_isShared_2584_ = v_isSharedCheck_2595_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_trees_2581_);
lean_inc(v_lazyAssignment_2580_);
lean_inc(v_assignment_2579_);
lean_dec(v_infoState_2563_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2595_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2585_ = l_Lean_PersistentArray_push___redArg(v_trees_2581_, v_t_2554_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 2, v___x_2585_);
v___x_2587_ = v___x_2583_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_assignment_2579_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_lazyAssignment_2580_);
lean_ctor_set(v_reuseFailAlloc_2594_, 2, v___x_2585_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*3, v_enabled_2578_);
v___x_2587_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2589_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 8, v___x_2587_);
v___x_2589_ = v___x_2576_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_env_2564_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v_messages_2565_);
lean_ctor_set(v_reuseFailAlloc_2593_, 2, v_scopes_2566_);
lean_ctor_set(v_reuseFailAlloc_2593_, 3, v_usedQuotCtxts_2567_);
lean_ctor_set(v_reuseFailAlloc_2593_, 4, v_nextMacroScope_2568_);
lean_ctor_set(v_reuseFailAlloc_2593_, 5, v_maxRecDepth_2569_);
lean_ctor_set(v_reuseFailAlloc_2593_, 6, v_ngen_2570_);
lean_ctor_set(v_reuseFailAlloc_2593_, 7, v_auxDeclNGen_2571_);
lean_ctor_set(v_reuseFailAlloc_2593_, 8, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2593_, 9, v_traceState_2572_);
lean_ctor_set(v_reuseFailAlloc_2593_, 10, v_snapshotTasks_2573_);
lean_ctor_set(v_reuseFailAlloc_2593_, 11, v_prevLinterStates_2574_);
v___x_2589_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = lean_st_ref_set(v___y_2555_, v___x_2589_);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2597_, v___y_2598_);
lean_dec(v___y_2598_);
return v_res_2600_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = lean_unsigned_to_nat(32u);
v___x_2602_ = lean_mk_empty_array_with_capacity(v___x_2601_);
v___x_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2604_ = ((size_t)5ULL);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_unsigned_to_nat(32u);
v___x_2607_ = lean_mk_empty_array_with_capacity(v___x_2606_);
v___x_2608_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2609_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v___x_2607_);
lean_ctor_set(v___x_2609_, 2, v___x_2605_);
lean_ctor_set(v___x_2609_, 3, v___x_2605_);
lean_ctor_set_usize(v___x_2609_, 4, v___x_2604_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; lean_object* v_infoState_2615_; uint8_t v_enabled_2616_; 
v___x_2614_ = lean_st_ref_get(v___y_2612_);
v_infoState_2615_ = lean_ctor_get(v___x_2614_, 8);
lean_inc_ref(v_infoState_2615_);
lean_dec(v___x_2614_);
v_enabled_2616_ = lean_ctor_get_uint8(v_infoState_2615_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2615_);
if (v_enabled_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_dec_ref(v_t_2610_);
v___x_2617_ = lean_box(0);
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
return v___x_2618_;
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2619_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2620_, 0, v_t_2610_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2620_, v___y_2612_);
return v___x_2621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(lean_object* v_edited_2627_, lean_object* v___x_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v_fst_2631_; lean_object* v_snd_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2657_; 
v_fst_2631_ = lean_ctor_get(v_a_2630_, 0);
v_snd_2632_ = lean_ctor_get(v_a_2630_, 1);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_a_2630_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2634_ = v_a_2630_;
v_isShared_2635_ = v_isSharedCheck_2657_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_snd_2632_);
lean_inc(v_fst_2631_);
lean_dec(v_a_2630_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2657_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; uint8_t v___y_2638_; uint8_t v___x_2653_; 
v___x_2636_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2653_ = lean_nat_dec_lt(v_snd_2632_, v___x_2628_);
if (v___x_2653_ == 0)
{
v___y_2638_ = v___x_2653_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = lean_array_get_borrowed(v___x_2636_, v_edited_2627_, v_snd_2632_);
v___x_2655_ = lean_string_dec_eq(v___x_2654_, v_a_2629_);
if (v___x_2655_ == 0)
{
v___y_2638_ = v___x_2653_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2656_; 
lean_del_object(v___x_2634_);
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v_fst_2631_);
lean_ctor_set(v___x_2656_, 1, v_snd_2632_);
return v___x_2656_;
}
}
v___jp_2637_:
{
if (v___y_2638_ == 0)
{
lean_object* v___x_2640_; 
if (v_isShared_2635_ == 0)
{
v___x_2640_ = v___x_2634_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_fst_2631_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_snd_2632_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
else
{
uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2642_ = 0;
v___x_2643_ = lean_array_get_borrowed(v___x_2636_, v_edited_2627_, v_snd_2632_);
v___x_2644_ = lean_box(v___x_2642_);
lean_inc(v___x_2643_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 1, v___x_2643_);
lean_ctor_set(v___x_2634_, 0, v___x_2644_);
v___x_2646_ = v___x_2634_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v___x_2643_);
v___x_2646_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2647_ = lean_array_push(v_fst_2631_, v___x_2646_);
v___x_2648_ = lean_unsigned_to_nat(1u);
v___x_2649_ = lean_nat_add(v_snd_2632_, v___x_2648_);
lean_dec(v_snd_2632_);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2647_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v_a_2630_ = v___x_2650_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg___boxed(lean_object* v_edited_2658_, lean_object* v___x_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2658_, v___x_2659_, v_a_2660_, v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v___x_2659_);
lean_dec_ref(v_edited_2658_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v_original_2663_, lean_object* v___x_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v_fst_2667_; lean_object* v_snd_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2693_; 
v_fst_2667_ = lean_ctor_get(v_a_2666_, 0);
v_snd_2668_ = lean_ctor_get(v_a_2666_, 1);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_a_2666_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2670_ = v_a_2666_;
v_isShared_2671_ = v_isSharedCheck_2693_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_snd_2668_);
lean_inc(v_fst_2667_);
lean_dec(v_a_2666_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2693_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; uint8_t v___y_2674_; uint8_t v___x_2689_; 
v___x_2672_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2689_ = lean_nat_dec_lt(v_snd_2668_, v___x_2664_);
if (v___x_2689_ == 0)
{
v___y_2674_ = v___x_2689_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = lean_array_get_borrowed(v___x_2672_, v_original_2663_, v_snd_2668_);
v___x_2691_ = lean_string_dec_eq(v___x_2690_, v_a_2665_);
if (v___x_2691_ == 0)
{
v___y_2674_ = v___x_2689_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2692_; 
lean_del_object(v___x_2670_);
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v_fst_2667_);
lean_ctor_set(v___x_2692_, 1, v_snd_2668_);
return v___x_2692_;
}
}
v___jp_2673_:
{
if (v___y_2674_ == 0)
{
lean_object* v___x_2676_; 
if (v_isShared_2671_ == 0)
{
v___x_2676_ = v___x_2670_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_fst_2667_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_snd_2668_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
else
{
uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2678_ = 1;
v___x_2679_ = lean_array_get_borrowed(v___x_2672_, v_original_2663_, v_snd_2668_);
v___x_2680_ = lean_box(v___x_2678_);
lean_inc(v___x_2679_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___x_2679_);
lean_ctor_set(v___x_2670_, 0, v___x_2680_);
v___x_2682_ = v___x_2670_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v___x_2679_);
v___x_2682_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2683_ = lean_array_push(v_fst_2667_, v___x_2682_);
v___x_2684_ = lean_unsigned_to_nat(1u);
v___x_2685_ = lean_nat_add(v_snd_2668_, v___x_2684_);
lean_dec(v_snd_2668_);
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2683_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v_a_2666_ = v___x_2686_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v_original_2694_, lean_object* v___x_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2694_, v___x_2695_, v_a_2696_, v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v___x_2695_);
lean_dec_ref(v_original_2694_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v_original_2699_, lean_object* v___x_2700_, lean_object* v_edited_2701_, lean_object* v___x_2702_, lean_object* v_as_2703_, size_t v_sz_2704_, size_t v_i_2705_, lean_object* v_b_2706_){
_start:
{
uint8_t v___x_2707_; 
v___x_2707_ = lean_usize_dec_lt(v_i_2705_, v_sz_2704_);
if (v___x_2707_ == 0)
{
return v_b_2706_;
}
else
{
lean_object* v_snd_2708_; lean_object* v_fst_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2756_; 
v_snd_2708_ = lean_ctor_get(v_b_2706_, 1);
v_fst_2709_ = lean_ctor_get(v_b_2706_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_b_2706_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2711_ = v_b_2706_;
v_isShared_2712_ = v_isSharedCheck_2756_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_snd_2708_);
lean_inc(v_fst_2709_);
lean_dec(v_b_2706_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2756_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v_fst_2713_; lean_object* v_snd_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2755_; 
v_fst_2713_ = lean_ctor_get(v_snd_2708_, 0);
v_snd_2714_ = lean_ctor_get(v_snd_2708_, 1);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_snd_2708_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2716_ = v_snd_2708_;
v_isShared_2717_ = v_isSharedCheck_2755_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_snd_2714_);
lean_inc(v_fst_2713_);
lean_dec(v_snd_2708_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2755_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v_a_2718_; lean_object* v___x_2720_; 
v_a_2718_ = lean_array_uget_borrowed(v_as_2703_, v_i_2705_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 1, v_fst_2713_);
lean_ctor_set(v___x_2716_, 0, v_fst_2709_);
v___x_2720_ = v___x_2716_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_fst_2709_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_fst_2713_);
v___x_2720_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; lean_object* v_fst_2722_; lean_object* v_snd_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2753_; 
v___x_2721_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2699_, v___x_2700_, v_a_2718_, v___x_2720_);
v_fst_2722_ = lean_ctor_get(v___x_2721_, 0);
v_snd_2723_ = lean_ctor_get(v___x_2721_, 1);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2725_ = v___x_2721_;
v_isShared_2726_ = v_isSharedCheck_2753_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_snd_2723_);
lean_inc(v_fst_2722_);
lean_dec(v___x_2721_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2753_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 1, v_snd_2714_);
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_fst_2722_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_snd_2714_);
v___x_2728_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; lean_object* v_fst_2730_; lean_object* v_snd_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2751_; 
v___x_2729_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2701_, v___x_2702_, v_a_2718_, v___x_2728_);
v_fst_2730_ = lean_ctor_get(v___x_2729_, 0);
v_snd_2731_ = lean_ctor_get(v___x_2729_, 1);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2733_ = v___x_2729_;
v_isShared_2734_ = v_isSharedCheck_2751_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_snd_2731_);
lean_inc(v_fst_2730_);
lean_dec(v___x_2729_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2751_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
uint8_t v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2735_ = 2;
v___x_2736_ = lean_box(v___x_2735_);
lean_inc(v_a_2718_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v_a_2718_);
lean_ctor_set(v___x_2733_, 0, v___x_2736_);
v___x_2738_ = v___x_2733_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_a_2718_);
v___x_2738_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2739_ = lean_array_push(v_fst_2730_, v___x_2738_);
v___x_2740_ = lean_unsigned_to_nat(1u);
v___x_2741_ = lean_nat_add(v_snd_2723_, v___x_2740_);
lean_dec(v_snd_2723_);
v___x_2742_ = lean_nat_add(v_snd_2731_, v___x_2740_);
lean_dec(v_snd_2731_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v___x_2742_);
lean_ctor_set(v___x_2711_, 0, v___x_2741_);
v___x_2744_ = v___x_2711_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; size_t v___x_2746_; size_t v___x_2747_; 
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2739_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = ((size_t)1ULL);
v___x_2747_ = lean_usize_add(v_i_2705_, v___x_2746_);
v_i_2705_ = v___x_2747_;
v_b_2706_ = v___x_2745_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v_original_2757_, lean_object* v___x_2758_, lean_object* v_edited_2759_, lean_object* v___x_2760_, lean_object* v_as_2761_, lean_object* v_sz_2762_, lean_object* v_i_2763_, lean_object* v_b_2764_){
_start:
{
size_t v_sz_boxed_2765_; size_t v_i_boxed_2766_; lean_object* v_res_2767_; 
v_sz_boxed_2765_ = lean_unbox_usize(v_sz_2762_);
lean_dec(v_sz_2762_);
v_i_boxed_2766_ = lean_unbox_usize(v_i_2763_);
lean_dec(v_i_2763_);
v_res_2767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2757_, v___x_2758_, v_edited_2759_, v___x_2760_, v_as_2761_, v_sz_boxed_2765_, v_i_boxed_2766_, v_b_2764_);
lean_dec_ref(v_as_2761_);
lean_dec(v___x_2760_);
lean_dec_ref(v_edited_2759_);
lean_dec(v___x_2758_);
lean_dec_ref(v_original_2757_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v_edited_2768_, lean_object* v___x_2769_, lean_object* v_original_2770_, lean_object* v___x_2771_, lean_object* v_as_2772_, size_t v_sz_2773_, size_t v_i_2774_, lean_object* v_b_2775_){
_start:
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_usize_dec_lt(v_i_2774_, v_sz_2773_);
if (v___x_2776_ == 0)
{
return v_b_2775_;
}
else
{
lean_object* v_snd_2777_; lean_object* v_fst_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2825_; 
v_snd_2777_ = lean_ctor_get(v_b_2775_, 1);
v_fst_2778_ = lean_ctor_get(v_b_2775_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_b_2775_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2780_ = v_b_2775_;
v_isShared_2781_ = v_isSharedCheck_2825_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_snd_2777_);
lean_inc(v_fst_2778_);
lean_dec(v_b_2775_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2825_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v_fst_2782_; lean_object* v_snd_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2824_; 
v_fst_2782_ = lean_ctor_get(v_snd_2777_, 0);
v_snd_2783_ = lean_ctor_get(v_snd_2777_, 1);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_snd_2777_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2785_ = v_snd_2777_;
v_isShared_2786_ = v_isSharedCheck_2824_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_snd_2783_);
lean_inc(v_fst_2782_);
lean_dec(v_snd_2777_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2824_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v_a_2787_; lean_object* v___x_2789_; 
v_a_2787_ = lean_array_uget_borrowed(v_as_2772_, v_i_2774_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 1, v_fst_2782_);
lean_ctor_set(v___x_2785_, 0, v_fst_2778_);
v___x_2789_ = v___x_2785_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_fst_2778_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_fst_2782_);
v___x_2789_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2790_; lean_object* v_fst_2791_; lean_object* v_snd_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2822_; 
v___x_2790_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2770_, v___x_2771_, v_a_2787_, v___x_2789_);
v_fst_2791_ = lean_ctor_get(v___x_2790_, 0);
v_snd_2792_ = lean_ctor_get(v___x_2790_, 1);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2794_ = v___x_2790_;
v_isShared_2795_ = v_isSharedCheck_2822_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_snd_2792_);
lean_inc(v_fst_2791_);
lean_dec(v___x_2790_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2822_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 1, v_snd_2783_);
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_fst_2791_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_snd_2783_);
v___x_2797_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v_fst_2799_; lean_object* v_snd_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2820_; 
v___x_2798_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2768_, v___x_2769_, v_a_2787_, v___x_2797_);
v_fst_2799_ = lean_ctor_get(v___x_2798_, 0);
v_snd_2800_ = lean_ctor_get(v___x_2798_, 1);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2802_ = v___x_2798_;
v_isShared_2803_ = v_isSharedCheck_2820_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_snd_2800_);
lean_inc(v_fst_2799_);
lean_dec(v___x_2798_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2820_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2804_ = 2;
v___x_2805_ = lean_box(v___x_2804_);
lean_inc(v_a_2787_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 1, v_a_2787_);
lean_ctor_set(v___x_2802_, 0, v___x_2805_);
v___x_2807_ = v___x_2802_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2805_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_a_2787_);
v___x_2807_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2808_ = lean_array_push(v_fst_2799_, v___x_2807_);
v___x_2809_ = lean_unsigned_to_nat(1u);
v___x_2810_ = lean_nat_add(v_snd_2792_, v___x_2809_);
lean_dec(v_snd_2792_);
v___x_2811_ = lean_nat_add(v_snd_2800_, v___x_2809_);
lean_dec(v_snd_2800_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 1, v___x_2811_);
lean_ctor_set(v___x_2780_, 0, v___x_2810_);
v___x_2813_ = v___x_2780_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; size_t v___x_2815_; size_t v___x_2816_; lean_object* v___x_2817_; 
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2808_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = ((size_t)1ULL);
v___x_2816_ = lean_usize_add(v_i_2774_, v___x_2815_);
v___x_2817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2770_, v___x_2771_, v_edited_2768_, v___x_2769_, v_as_2772_, v_sz_2773_, v___x_2816_, v___x_2814_);
return v___x_2817_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v_edited_2826_, lean_object* v___x_2827_, lean_object* v_original_2828_, lean_object* v___x_2829_, lean_object* v_as_2830_, lean_object* v_sz_2831_, lean_object* v_i_2832_, lean_object* v_b_2833_){
_start:
{
size_t v_sz_boxed_2834_; size_t v_i_boxed_2835_; lean_object* v_res_2836_; 
v_sz_boxed_2834_ = lean_unbox_usize(v_sz_2831_);
lean_dec(v_sz_2831_);
v_i_boxed_2835_ = lean_unbox_usize(v_i_2832_);
lean_dec(v_i_2832_);
v_res_2836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_2826_, v___x_2827_, v_original_2828_, v___x_2829_, v_as_2830_, v_sz_boxed_2834_, v_i_boxed_2835_, v_b_2833_);
lean_dec_ref(v_as_2830_);
lean_dec(v___x_2829_);
lean_dec_ref(v_original_2828_);
lean_dec(v___x_2827_);
lean_dec_ref(v_edited_2826_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(lean_object* v_a_2837_, lean_object* v_x_2838_){
_start:
{
if (lean_obj_tag(v_x_2838_) == 0)
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_box(0);
return v___x_2839_;
}
else
{
lean_object* v_key_2840_; lean_object* v_value_2841_; lean_object* v_tail_2842_; uint8_t v___x_2843_; 
v_key_2840_ = lean_ctor_get(v_x_2838_, 0);
v_value_2841_ = lean_ctor_get(v_x_2838_, 1);
v_tail_2842_ = lean_ctor_get(v_x_2838_, 2);
v___x_2843_ = lean_string_dec_eq(v_key_2840_, v_a_2837_);
if (v___x_2843_ == 0)
{
v_x_2838_ = v_tail_2842_;
goto _start;
}
else
{
lean_object* v___x_2845_; 
lean_inc(v_value_2841_);
v___x_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2845_, 0, v_value_2841_);
return v___x_2845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg___boxed(lean_object* v_a_2846_, lean_object* v_x_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2846_, v_x_2847_);
lean_dec(v_x_2847_);
lean_dec_ref(v_a_2846_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(lean_object* v_m_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_buckets_2851_; lean_object* v___x_2852_; uint64_t v___x_2853_; uint64_t v___x_2854_; uint64_t v___x_2855_; uint64_t v_fold_2856_; uint64_t v___x_2857_; uint64_t v___x_2858_; uint64_t v___x_2859_; size_t v___x_2860_; size_t v___x_2861_; size_t v___x_2862_; size_t v___x_2863_; size_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_buckets_2851_ = lean_ctor_get(v_m_2849_, 1);
v___x_2852_ = lean_array_get_size(v_buckets_2851_);
v___x_2853_ = lean_string_hash(v_a_2850_);
v___x_2854_ = 32ULL;
v___x_2855_ = lean_uint64_shift_right(v___x_2853_, v___x_2854_);
v_fold_2856_ = lean_uint64_xor(v___x_2853_, v___x_2855_);
v___x_2857_ = 16ULL;
v___x_2858_ = lean_uint64_shift_right(v_fold_2856_, v___x_2857_);
v___x_2859_ = lean_uint64_xor(v_fold_2856_, v___x_2858_);
v___x_2860_ = lean_uint64_to_usize(v___x_2859_);
v___x_2861_ = lean_usize_of_nat(v___x_2852_);
v___x_2862_ = ((size_t)1ULL);
v___x_2863_ = lean_usize_sub(v___x_2861_, v___x_2862_);
v___x_2864_ = lean_usize_land(v___x_2860_, v___x_2863_);
v___x_2865_ = lean_array_uget_borrowed(v_buckets_2851_, v___x_2864_);
v___x_2866_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2850_, v___x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_m_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_2867_, v_a_2868_);
lean_dec_ref(v_a_2868_);
lean_dec_ref(v_m_2867_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(lean_object* v_a_2870_, lean_object* v_b_2871_, lean_object* v_x_2872_){
_start:
{
if (lean_obj_tag(v_x_2872_) == 0)
{
lean_dec(v_b_2871_);
lean_dec_ref(v_a_2870_);
return v_x_2872_;
}
else
{
lean_object* v_key_2873_; lean_object* v_value_2874_; lean_object* v_tail_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2887_; 
v_key_2873_ = lean_ctor_get(v_x_2872_, 0);
v_value_2874_ = lean_ctor_get(v_x_2872_, 1);
v_tail_2875_ = lean_ctor_get(v_x_2872_, 2);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_x_2872_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2877_ = v_x_2872_;
v_isShared_2878_ = v_isSharedCheck_2887_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_tail_2875_);
lean_inc(v_value_2874_);
lean_inc(v_key_2873_);
lean_dec(v_x_2872_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2887_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
uint8_t v___x_2879_; 
v___x_2879_ = lean_string_dec_eq(v_key_2873_, v_a_2870_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2880_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2870_, v_b_2871_, v_tail_2875_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 2, v___x_2880_);
v___x_2882_ = v___x_2877_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_key_2873_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_value_2874_);
lean_ctor_set(v_reuseFailAlloc_2883_, 2, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
else
{
lean_object* v___x_2885_; 
lean_dec(v_value_2874_);
lean_dec(v_key_2873_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 1, v_b_2871_);
lean_ctor_set(v___x_2877_, 0, v_a_2870_);
v___x_2885_ = v___x_2877_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2870_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_b_2871_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v_tail_2875_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(lean_object* v_a_2888_, lean_object* v_x_2889_){
_start:
{
if (lean_obj_tag(v_x_2889_) == 0)
{
uint8_t v___x_2890_; 
v___x_2890_ = 0;
return v___x_2890_;
}
else
{
lean_object* v_key_2891_; lean_object* v_tail_2892_; uint8_t v___x_2893_; 
v_key_2891_ = lean_ctor_get(v_x_2889_, 0);
v_tail_2892_ = lean_ctor_get(v_x_2889_, 2);
v___x_2893_ = lean_string_dec_eq(v_key_2891_, v_a_2888_);
if (v___x_2893_ == 0)
{
v_x_2889_ = v_tail_2892_;
goto _start;
}
else
{
return v___x_2893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg___boxed(lean_object* v_a_2895_, lean_object* v_x_2896_){
_start:
{
uint8_t v_res_2897_; lean_object* v_r_2898_; 
v_res_2897_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2895_, v_x_2896_);
lean_dec(v_x_2896_);
lean_dec_ref(v_a_2895_);
v_r_2898_ = lean_box(v_res_2897_);
return v_r_2898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2899_, lean_object* v_x_2900_){
_start:
{
if (lean_obj_tag(v_x_2900_) == 0)
{
return v_x_2899_;
}
else
{
lean_object* v_key_2901_; lean_object* v_value_2902_; lean_object* v_tail_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2926_; 
v_key_2901_ = lean_ctor_get(v_x_2900_, 0);
v_value_2902_ = lean_ctor_get(v_x_2900_, 1);
v_tail_2903_ = lean_ctor_get(v_x_2900_, 2);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_x_2900_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2905_ = v_x_2900_;
v_isShared_2906_ = v_isSharedCheck_2926_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_tail_2903_);
lean_inc(v_value_2902_);
lean_inc(v_key_2901_);
lean_dec(v_x_2900_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2926_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; uint64_t v___x_2908_; uint64_t v___x_2909_; uint64_t v___x_2910_; uint64_t v_fold_2911_; uint64_t v___x_2912_; uint64_t v___x_2913_; uint64_t v___x_2914_; size_t v___x_2915_; size_t v___x_2916_; size_t v___x_2917_; size_t v___x_2918_; size_t v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2907_ = lean_array_get_size(v_x_2899_);
v___x_2908_ = lean_string_hash(v_key_2901_);
v___x_2909_ = 32ULL;
v___x_2910_ = lean_uint64_shift_right(v___x_2908_, v___x_2909_);
v_fold_2911_ = lean_uint64_xor(v___x_2908_, v___x_2910_);
v___x_2912_ = 16ULL;
v___x_2913_ = lean_uint64_shift_right(v_fold_2911_, v___x_2912_);
v___x_2914_ = lean_uint64_xor(v_fold_2911_, v___x_2913_);
v___x_2915_ = lean_uint64_to_usize(v___x_2914_);
v___x_2916_ = lean_usize_of_nat(v___x_2907_);
v___x_2917_ = ((size_t)1ULL);
v___x_2918_ = lean_usize_sub(v___x_2916_, v___x_2917_);
v___x_2919_ = lean_usize_land(v___x_2915_, v___x_2918_);
v___x_2920_ = lean_array_uget_borrowed(v_x_2899_, v___x_2919_);
lean_inc(v___x_2920_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 2, v___x_2920_);
v___x_2922_ = v___x_2905_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_key_2901_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_value_2902_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_array_uset(v_x_2899_, v___x_2919_, v___x_2922_);
v_x_2899_ = v___x_2923_;
v_x_2900_ = v_tail_2903_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(lean_object* v_i_2927_, lean_object* v_source_2928_, lean_object* v_target_2929_){
_start:
{
lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2930_ = lean_array_get_size(v_source_2928_);
v___x_2931_ = lean_nat_dec_lt(v_i_2927_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_dec_ref(v_source_2928_);
lean_dec(v_i_2927_);
return v_target_2929_;
}
else
{
lean_object* v_es_2932_; lean_object* v___x_2933_; lean_object* v_source_2934_; lean_object* v_target_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_es_2932_ = lean_array_fget(v_source_2928_, v_i_2927_);
v___x_2933_ = lean_box(0);
v_source_2934_ = lean_array_fset(v_source_2928_, v_i_2927_, v___x_2933_);
v_target_2935_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_target_2929_, v_es_2932_);
v___x_2936_ = lean_unsigned_to_nat(1u);
v___x_2937_ = lean_nat_add(v_i_2927_, v___x_2936_);
lean_dec(v_i_2927_);
v_i_2927_ = v___x_2937_;
v_source_2928_ = v_source_2934_;
v_target_2929_ = v_target_2935_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(lean_object* v_data_2939_){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v_nbuckets_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2940_ = lean_array_get_size(v_data_2939_);
v___x_2941_ = lean_unsigned_to_nat(2u);
v_nbuckets_2942_ = lean_nat_mul(v___x_2940_, v___x_2941_);
v___x_2943_ = lean_unsigned_to_nat(0u);
v___x_2944_ = lean_box(0);
v___x_2945_ = lean_mk_array(v_nbuckets_2942_, v___x_2944_);
v___x_2946_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v___x_2943_, v_data_2939_, v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(lean_object* v_m_2947_, lean_object* v_a_2948_, lean_object* v_b_2949_){
_start:
{
lean_object* v_size_2950_; lean_object* v_buckets_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2994_; 
v_size_2950_ = lean_ctor_get(v_m_2947_, 0);
v_buckets_2951_ = lean_ctor_get(v_m_2947_, 1);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_m_2947_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2953_ = v_m_2947_;
v_isShared_2954_ = v_isSharedCheck_2994_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_buckets_2951_);
lean_inc(v_size_2950_);
lean_dec(v_m_2947_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2994_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; uint64_t v___x_2956_; uint64_t v___x_2957_; uint64_t v___x_2958_; uint64_t v_fold_2959_; uint64_t v___x_2960_; uint64_t v___x_2961_; uint64_t v___x_2962_; size_t v___x_2963_; size_t v___x_2964_; size_t v___x_2965_; size_t v___x_2966_; size_t v___x_2967_; lean_object* v_bkt_2968_; uint8_t v___x_2969_; 
v___x_2955_ = lean_array_get_size(v_buckets_2951_);
v___x_2956_ = lean_string_hash(v_a_2948_);
v___x_2957_ = 32ULL;
v___x_2958_ = lean_uint64_shift_right(v___x_2956_, v___x_2957_);
v_fold_2959_ = lean_uint64_xor(v___x_2956_, v___x_2958_);
v___x_2960_ = 16ULL;
v___x_2961_ = lean_uint64_shift_right(v_fold_2959_, v___x_2960_);
v___x_2962_ = lean_uint64_xor(v_fold_2959_, v___x_2961_);
v___x_2963_ = lean_uint64_to_usize(v___x_2962_);
v___x_2964_ = lean_usize_of_nat(v___x_2955_);
v___x_2965_ = ((size_t)1ULL);
v___x_2966_ = lean_usize_sub(v___x_2964_, v___x_2965_);
v___x_2967_ = lean_usize_land(v___x_2963_, v___x_2966_);
v_bkt_2968_ = lean_array_uget_borrowed(v_buckets_2951_, v___x_2967_);
v___x_2969_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2948_, v_bkt_2968_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; lean_object* v_size_x27_2971_; lean_object* v___x_2972_; lean_object* v_buckets_x27_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2970_ = lean_unsigned_to_nat(1u);
v_size_x27_2971_ = lean_nat_add(v_size_2950_, v___x_2970_);
lean_dec(v_size_2950_);
lean_inc(v_bkt_2968_);
v___x_2972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2972_, 0, v_a_2948_);
lean_ctor_set(v___x_2972_, 1, v_b_2949_);
lean_ctor_set(v___x_2972_, 2, v_bkt_2968_);
v_buckets_x27_2973_ = lean_array_uset(v_buckets_2951_, v___x_2967_, v___x_2972_);
v___x_2974_ = lean_unsigned_to_nat(4u);
v___x_2975_ = lean_nat_mul(v_size_x27_2971_, v___x_2974_);
v___x_2976_ = lean_unsigned_to_nat(3u);
v___x_2977_ = lean_nat_div(v___x_2975_, v___x_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_array_get_size(v_buckets_x27_2973_);
v___x_2979_ = lean_nat_dec_le(v___x_2977_, v___x_2978_);
lean_dec(v___x_2977_);
if (v___x_2979_ == 0)
{
lean_object* v_val_2980_; lean_object* v___x_2982_; 
v_val_2980_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_buckets_x27_2973_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v_val_2980_);
lean_ctor_set(v___x_2953_, 0, v_size_x27_2971_);
v___x_2982_ = v___x_2953_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_size_x27_2971_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_val_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
else
{
lean_object* v___x_2985_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v_buckets_x27_2973_);
lean_ctor_set(v___x_2953_, 0, v_size_x27_2971_);
v___x_2985_ = v___x_2953_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_size_x27_2971_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_buckets_x27_2973_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
else
{
lean_object* v___x_2987_; lean_object* v_buckets_x27_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2992_; 
lean_inc(v_bkt_2968_);
v___x_2987_ = lean_box(0);
v_buckets_x27_2988_ = lean_array_uset(v_buckets_2951_, v___x_2967_, v___x_2987_);
v___x_2989_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2948_, v_b_2949_, v_bkt_2968_);
v___x_2990_ = lean_array_uset(v_buckets_x27_2988_, v___x_2967_, v___x_2989_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v___x_2990_);
v___x_2992_ = v___x_2953_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_size_2950_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(lean_object* v_histogram_2995_, lean_object* v_index_2996_, lean_object* v_val_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_2995_, v_val_2997_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_2999_ = lean_unsigned_to_nat(1u);
v___x_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3000_, 0, v_index_2996_);
v___x_3001_ = lean_unsigned_to_nat(0u);
v___x_3002_ = lean_box(0);
v___x_3003_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3003_, 0, v___x_2999_);
lean_ctor_set(v___x_3003_, 1, v___x_3000_);
lean_ctor_set(v___x_3003_, 2, v___x_3001_);
lean_ctor_set(v___x_3003_, 3, v___x_3002_);
v___x_3004_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_2995_, v_val_2997_, v___x_3003_);
return v___x_3004_;
}
else
{
lean_object* v_val_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3026_; 
v_val_3005_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3007_ = v___x_2998_;
v_isShared_3008_ = v_isSharedCheck_3026_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_val_3005_);
lean_dec(v___x_2998_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3026_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v_leftCount_3009_; lean_object* v_rightCount_3010_; lean_object* v_rightIndex_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3024_; 
v_leftCount_3009_ = lean_ctor_get(v_val_3005_, 0);
v_rightCount_3010_ = lean_ctor_get(v_val_3005_, 2);
v_rightIndex_3011_ = lean_ctor_get(v_val_3005_, 3);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_val_3005_);
if (v_isSharedCheck_3024_ == 0)
{
lean_object* v_unused_3025_; 
v_unused_3025_ = lean_ctor_get(v_val_3005_, 1);
lean_dec(v_unused_3025_);
v___x_3013_ = v_val_3005_;
v_isShared_3014_ = v_isSharedCheck_3024_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_rightIndex_3011_);
lean_inc(v_rightCount_3010_);
lean_inc(v_leftCount_3009_);
lean_dec(v_val_3005_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3024_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3015_ = lean_unsigned_to_nat(1u);
v___x_3016_ = lean_nat_add(v_leftCount_3009_, v___x_3015_);
lean_dec(v_leftCount_3009_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v_index_2996_);
v___x_3018_ = v___x_3007_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_index_2996_);
v___x_3018_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3020_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 1, v___x_3018_);
lean_ctor_set(v___x_3013_, 0, v___x_3016_);
v___x_3020_ = v___x_3013_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3016_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v___x_3018_);
lean_ctor_set(v_reuseFailAlloc_3022_, 2, v_rightCount_3010_);
lean_ctor_set(v_reuseFailAlloc_3022_, 3, v_rightIndex_3011_);
v___x_3020_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_2995_, v_val_2997_, v___x_3020_);
return v___x_3021_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(lean_object* v_upperBound_3027_, lean_object* v_fst_3028_, lean_object* v___x_3029_, lean_object* v_fst_3030_, lean_object* v_a_3031_, lean_object* v_b_3032_){
_start:
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_nat_dec_lt(v_a_3031_, v_upperBound_3027_);
if (v___x_3033_ == 0)
{
lean_dec(v_a_3031_);
return v_b_3032_;
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3034_ = l_Subarray_get___redArg(v_fst_3030_, v_a_3031_);
lean_inc(v_a_3031_);
v___x_3035_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_b_3032_, v_a_3031_, v___x_3034_);
v___x_3036_ = lean_unsigned_to_nat(1u);
v___x_3037_ = lean_nat_add(v_a_3031_, v___x_3036_);
lean_dec(v_a_3031_);
v_a_3031_ = v___x_3037_;
v_b_3032_ = v___x_3035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg___boxed(lean_object* v_upperBound_3039_, lean_object* v_fst_3040_, lean_object* v___x_3041_, lean_object* v_fst_3042_, lean_object* v_a_3043_, lean_object* v_b_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3039_, v_fst_3040_, v___x_3041_, v_fst_3042_, v_a_3043_, v_b_3044_);
lean_dec_ref(v_fst_3042_);
lean_dec(v___x_3041_);
lean_dec_ref(v_fst_3040_);
lean_dec(v_upperBound_3039_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(lean_object* v_x_3046_, lean_object* v_x_3047_){
_start:
{
if (lean_obj_tag(v_x_3047_) == 0)
{
lean_inc(v_x_3046_);
return v_x_3046_;
}
else
{
lean_object* v_key_3048_; lean_object* v_value_3049_; lean_object* v_tail_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_key_3048_ = lean_ctor_get(v_x_3047_, 0);
v_value_3049_ = lean_ctor_get(v_x_3047_, 1);
v_tail_3050_ = lean_ctor_get(v_x_3047_, 2);
v___x_3051_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3046_, v_tail_3050_);
lean_inc(v_value_3049_);
lean_inc(v_key_3048_);
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v_key_3048_);
lean_ctor_set(v___x_3052_, 1, v_value_3049_);
v___x_3053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v___x_3051_);
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___boxed(lean_object* v_x_3054_, lean_object* v_x_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3054_, v_x_3055_);
lean_dec(v_x_3055_);
lean_dec(v_x_3054_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(lean_object* v_as_3057_, size_t v_i_3058_, size_t v_stop_3059_, lean_object* v_b_3060_){
_start:
{
uint8_t v___x_3061_; 
v___x_3061_ = lean_usize_dec_eq(v_i_3058_, v_stop_3059_);
if (v___x_3061_ == 0)
{
size_t v___x_3062_; size_t v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3062_ = ((size_t)1ULL);
v___x_3063_ = lean_usize_sub(v_i_3058_, v___x_3062_);
v___x_3064_ = lean_array_uget_borrowed(v_as_3057_, v___x_3063_);
v___x_3065_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_b_3060_, v___x_3064_);
lean_dec(v_b_3060_);
v_i_3058_ = v___x_3063_;
v_b_3060_ = v___x_3065_;
goto _start;
}
else
{
return v_b_3060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___boxed(lean_object* v_as_3067_, lean_object* v_i_3068_, lean_object* v_stop_3069_, lean_object* v_b_3070_){
_start:
{
size_t v_i_boxed_3071_; size_t v_stop_boxed_3072_; lean_object* v_res_3073_; 
v_i_boxed_3071_ = lean_unbox_usize(v_i_3068_);
lean_dec(v_i_3068_);
v_stop_boxed_3072_ = lean_unbox_usize(v_stop_3069_);
lean_dec(v_stop_3069_);
v_res_3073_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_as_3067_, v_i_boxed_3071_, v_stop_boxed_3072_, v_b_3070_);
lean_dec_ref(v_as_3067_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(lean_object* v_left_3074_, lean_object* v_right_3075_, lean_object* v_pref_3076_){
_start:
{
lean_object* v_start_3077_; lean_object* v_stop_3078_; lean_object* v_i_3079_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v_start_3077_ = lean_ctor_get(v_left_3074_, 1);
v_stop_3078_ = lean_ctor_get(v_left_3074_, 2);
v_i_3079_ = lean_array_get_size(v_pref_3076_);
v___x_3085_ = lean_nat_sub(v_stop_3078_, v_start_3077_);
v___x_3086_ = lean_nat_dec_lt(v_i_3079_, v___x_3085_);
lean_dec(v___x_3085_);
if (v___x_3086_ == 0)
{
goto v___jp_3080_;
}
else
{
lean_object* v_start_3087_; lean_object* v_stop_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; 
v_start_3087_ = lean_ctor_get(v_right_3075_, 1);
v_stop_3088_ = lean_ctor_get(v_right_3075_, 2);
v___x_3089_ = lean_nat_sub(v_stop_3088_, v_start_3087_);
v___x_3090_ = lean_nat_dec_lt(v_i_3079_, v___x_3089_);
lean_dec(v___x_3089_);
if (v___x_3090_ == 0)
{
goto v___jp_3080_;
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3091_ = l_Subarray_get___redArg(v_left_3074_, v_i_3079_);
v___x_3092_ = l_Subarray_get___redArg(v_right_3075_, v_i_3079_);
v___x_3093_ = lean_string_dec_eq(v___x_3091_, v___x_3092_);
lean_dec(v___x_3092_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
lean_dec(v___x_3091_);
v___x_3094_ = l_Subarray_drop___redArg(v_left_3074_, v_i_3079_);
v___x_3095_ = l_Subarray_drop___redArg(v_right_3075_, v_i_3079_);
v___x_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3094_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3097_, 0, v_pref_3076_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
return v___x_3097_;
}
else
{
lean_object* v___x_3098_; 
v___x_3098_ = lean_array_push(v_pref_3076_, v___x_3091_);
v_pref_3076_ = v___x_3098_;
goto _start;
}
}
}
v___jp_3080_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3081_ = l_Subarray_drop___redArg(v_left_3074_, v_i_3079_);
v___x_3082_ = l_Subarray_drop___redArg(v_right_3075_, v_i_3079_);
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3081_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3084_, 0, v_pref_3076_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
return v___x_3084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(lean_object* v_left_3102_, lean_object* v_right_3103_){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3105_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(v_left_3102_, v_right_3103_, v___x_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(lean_object* v_a_3106_, lean_object* v_b_3107_){
_start:
{
lean_object* v_array_3108_; lean_object* v_start_3109_; lean_object* v_stop_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3123_; 
v_array_3108_ = lean_ctor_get(v_a_3106_, 0);
v_start_3109_ = lean_ctor_get(v_a_3106_, 1);
v_stop_3110_ = lean_ctor_get(v_a_3106_, 2);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_a_3106_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3112_ = v_a_3106_;
v_isShared_3113_ = v_isSharedCheck_3123_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_stop_3110_);
lean_inc(v_start_3109_);
lean_inc(v_array_3108_);
lean_dec(v_a_3106_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3123_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
uint8_t v___x_3114_; 
v___x_3114_ = lean_nat_dec_lt(v_start_3109_, v_stop_3110_);
if (v___x_3114_ == 0)
{
lean_del_object(v___x_3112_);
lean_dec(v_stop_3110_);
lean_dec(v_start_3109_);
lean_dec_ref(v_array_3108_);
return v_b_3107_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3115_ = lean_unsigned_to_nat(1u);
v___x_3116_ = lean_nat_add(v_start_3109_, v___x_3115_);
lean_inc_ref(v_array_3108_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 1, v___x_3116_);
v___x_3118_ = v___x_3112_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_array_3108_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_stop_3110_);
v___x_3118_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_array_fget(v_array_3108_, v_start_3109_);
lean_dec(v_start_3109_);
lean_dec_ref(v_array_3108_);
v___x_3120_ = lean_array_push(v_b_3107_, v___x_3119_);
v_a_3106_ = v___x_3118_;
v_b_3107_ = v___x_3120_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(lean_object* v_left_3124_, lean_object* v_right_3125_, lean_object* v_i_3126_){
_start:
{
lean_object* v_start_3127_; lean_object* v_stop_3128_; lean_object* v___x_3129_; uint8_t v___x_3143_; 
v_start_3127_ = lean_ctor_get(v_left_3124_, 1);
v_stop_3128_ = lean_ctor_get(v_left_3124_, 2);
v___x_3129_ = lean_nat_sub(v_stop_3128_, v_start_3127_);
v___x_3143_ = lean_nat_dec_lt(v_i_3126_, v___x_3129_);
if (v___x_3143_ == 0)
{
goto v___jp_3130_;
}
else
{
lean_object* v_start_3144_; lean_object* v_stop_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v_start_3144_ = lean_ctor_get(v_right_3125_, 1);
v_stop_3145_ = lean_ctor_get(v_right_3125_, 2);
v___x_3146_ = lean_nat_sub(v_stop_3145_, v_start_3144_);
v___x_3147_ = lean_nat_dec_lt(v_i_3126_, v___x_3146_);
if (v___x_3147_ == 0)
{
lean_dec(v___x_3146_);
goto v___jp_3130_;
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; 
v___x_3148_ = lean_nat_sub(v___x_3129_, v_i_3126_);
lean_dec(v___x_3129_);
v___x_3149_ = lean_unsigned_to_nat(1u);
v___x_3150_ = lean_nat_sub(v___x_3148_, v___x_3149_);
v___x_3151_ = l_Subarray_get___redArg(v_left_3124_, v___x_3150_);
lean_dec(v___x_3150_);
v___x_3152_ = lean_nat_sub(v___x_3146_, v_i_3126_);
lean_dec(v___x_3146_);
v___x_3153_ = lean_nat_sub(v___x_3152_, v___x_3149_);
v___x_3154_ = l_Subarray_get___redArg(v_right_3125_, v___x_3153_);
lean_dec(v___x_3153_);
v___x_3155_ = lean_string_dec_eq(v___x_3151_, v___x_3154_);
lean_dec(v___x_3154_);
lean_dec(v___x_3151_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_dec(v_i_3126_);
lean_inc_ref(v_left_3124_);
v___x_3156_ = l_Subarray_take___redArg(v_left_3124_, v___x_3148_);
v___x_3157_ = l_Subarray_take___redArg(v_right_3125_, v___x_3152_);
lean_dec(v___x_3152_);
v___x_3158_ = l_Subarray_drop___redArg(v_left_3124_, v___x_3148_);
lean_dec(v___x_3148_);
v___x_3159_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3160_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3158_, v___x_3159_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3157_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3156_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
return v___x_3162_;
}
else
{
lean_object* v___x_3163_; 
lean_dec(v___x_3152_);
lean_dec(v___x_3148_);
v___x_3163_ = lean_nat_add(v_i_3126_, v___x_3149_);
lean_dec(v_i_3126_);
v_i_3126_ = v___x_3163_;
goto _start;
}
}
}
v___jp_3130_:
{
lean_object* v_start_3131_; lean_object* v_stop_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v_start_3131_ = lean_ctor_get(v_right_3125_, 1);
v_stop_3132_ = lean_ctor_get(v_right_3125_, 2);
v___x_3133_ = lean_nat_sub(v___x_3129_, v_i_3126_);
lean_dec(v___x_3129_);
lean_inc_ref(v_left_3124_);
v___x_3134_ = l_Subarray_take___redArg(v_left_3124_, v___x_3133_);
v___x_3135_ = lean_nat_sub(v_stop_3132_, v_start_3131_);
v___x_3136_ = lean_nat_sub(v___x_3135_, v_i_3126_);
lean_dec(v_i_3126_);
lean_dec(v___x_3135_);
v___x_3137_ = l_Subarray_take___redArg(v_right_3125_, v___x_3136_);
lean_dec(v___x_3136_);
v___x_3138_ = l_Subarray_drop___redArg(v_left_3124_, v___x_3133_);
lean_dec(v___x_3133_);
v___x_3139_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3140_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3138_, v___x_3139_);
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3137_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3134_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
return v___x_3142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(lean_object* v_left_3165_, lean_object* v_right_3166_){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = lean_unsigned_to_nat(0u);
v___x_3168_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(v_left_3165_, v_right_3166_, v___x_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(lean_object* v_as_x27_3169_, lean_object* v_b_3170_){
_start:
{
if (lean_obj_tag(v_as_x27_3169_) == 0)
{
return v_b_3170_;
}
else
{
lean_object* v_head_3171_; lean_object* v_snd_3172_; lean_object* v_leftIndex_3173_; 
v_head_3171_ = lean_ctor_get(v_as_x27_3169_, 0);
v_snd_3172_ = lean_ctor_get(v_head_3171_, 1);
v_leftIndex_3173_ = lean_ctor_get(v_snd_3172_, 1);
if (lean_obj_tag(v_leftIndex_3173_) == 1)
{
lean_object* v_rightIndex_3174_; 
v_rightIndex_3174_ = lean_ctor_get(v_snd_3172_, 3);
if (lean_obj_tag(v_rightIndex_3174_) == 1)
{
if (lean_obj_tag(v_b_3170_) == 0)
{
lean_object* v_tail_3175_; lean_object* v_fst_3176_; lean_object* v_leftCount_3177_; lean_object* v_rightCount_3178_; lean_object* v_val_3179_; lean_object* v_val_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v_tail_3175_ = lean_ctor_get(v_as_x27_3169_, 1);
v_fst_3176_ = lean_ctor_get(v_head_3171_, 0);
v_leftCount_3177_ = lean_ctor_get(v_snd_3172_, 0);
v_rightCount_3178_ = lean_ctor_get(v_snd_3172_, 2);
v_val_3179_ = lean_ctor_get(v_leftIndex_3173_, 0);
v_val_3180_ = lean_ctor_get(v_rightIndex_3174_, 0);
v___x_3181_ = lean_nat_add(v_leftCount_3177_, v_rightCount_3178_);
lean_inc(v_val_3180_);
lean_inc(v_val_3179_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v_val_3179_);
lean_ctor_set(v___x_3182_, 1, v_val_3180_);
lean_inc(v_fst_3176_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v_fst_3176_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3181_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
v_as_x27_3169_ = v_tail_3175_;
v_b_3170_ = v___x_3185_;
goto _start;
}
else
{
lean_object* v_val_3187_; lean_object* v_tail_3188_; lean_object* v_fst_3189_; lean_object* v_leftCount_3190_; lean_object* v_rightCount_3191_; lean_object* v_val_3192_; lean_object* v_val_3193_; lean_object* v_fst_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3215_; 
v_val_3187_ = lean_ctor_get(v_b_3170_, 0);
lean_inc(v_val_3187_);
v_tail_3188_ = lean_ctor_get(v_as_x27_3169_, 1);
v_fst_3189_ = lean_ctor_get(v_head_3171_, 0);
v_leftCount_3190_ = lean_ctor_get(v_snd_3172_, 0);
v_rightCount_3191_ = lean_ctor_get(v_snd_3172_, 2);
v_val_3192_ = lean_ctor_get(v_leftIndex_3173_, 0);
v_val_3193_ = lean_ctor_get(v_rightIndex_3174_, 0);
v_fst_3194_ = lean_ctor_get(v_val_3187_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_val_3187_);
if (v_isSharedCheck_3215_ == 0)
{
lean_object* v_unused_3216_; 
v_unused_3216_ = lean_ctor_get(v_val_3187_, 1);
lean_dec(v_unused_3216_);
v___x_3196_ = v_val_3187_;
v_isShared_3197_ = v_isSharedCheck_3215_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_fst_3194_);
lean_dec(v_val_3187_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3215_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; uint8_t v___x_3199_; 
v___x_3198_ = lean_nat_add(v_leftCount_3190_, v_rightCount_3191_);
v___x_3199_ = lean_nat_dec_lt(v___x_3198_, v_fst_3194_);
lean_dec(v_fst_3194_);
if (v___x_3199_ == 0)
{
lean_dec(v___x_3198_);
lean_del_object(v___x_3196_);
v_as_x27_3169_ = v_tail_3188_;
goto _start;
}
else
{
lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3213_; 
v_isSharedCheck_3213_ = !lean_is_exclusive(v_b_3170_);
if (v_isSharedCheck_3213_ == 0)
{
lean_object* v_unused_3214_; 
v_unused_3214_ = lean_ctor_get(v_b_3170_, 0);
lean_dec(v_unused_3214_);
v___x_3202_ = v_b_3170_;
v_isShared_3203_ = v_isSharedCheck_3213_;
goto v_resetjp_3201_;
}
else
{
lean_dec(v_b_3170_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3213_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
lean_inc(v_val_3193_);
lean_inc(v_val_3192_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 1, v_val_3193_);
lean_ctor_set(v___x_3196_, 0, v_val_3192_);
v___x_3205_ = v___x_3196_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_val_3192_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v_val_3193_);
v___x_3205_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
lean_inc(v_fst_3189_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_fst_3189_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3198_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v___x_3207_);
v___x_3209_ = v___x_3202_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
v_as_x27_3169_ = v_tail_3188_;
v_b_3170_ = v___x_3209_;
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
lean_object* v_tail_3217_; 
v_tail_3217_ = lean_ctor_get(v_as_x27_3169_, 1);
v_as_x27_3169_ = v_tail_3217_;
goto _start;
}
}
else
{
lean_object* v_tail_3219_; 
v_tail_3219_ = lean_ctor_get(v_as_x27_3169_, 1);
v_as_x27_3169_ = v_tail_3219_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg___boxed(lean_object* v_as_x27_3221_, lean_object* v_b_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3221_, v_b_3222_);
lean_dec(v_as_x27_3221_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(lean_object* v_histogram_3224_, lean_object* v_index_3225_, lean_object* v_val_3226_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3224_, v_val_3226_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3228_ = lean_unsigned_to_nat(0u);
v___x_3229_ = lean_box(0);
v___x_3230_ = lean_unsigned_to_nat(1u);
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_index_3225_);
v___x_3232_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3228_);
lean_ctor_set(v___x_3232_, 1, v___x_3229_);
lean_ctor_set(v___x_3232_, 2, v___x_3230_);
lean_ctor_set(v___x_3232_, 3, v___x_3231_);
v___x_3233_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3224_, v_val_3226_, v___x_3232_);
return v___x_3233_;
}
else
{
lean_object* v_val_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3255_; 
v_val_3234_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3236_ = v___x_3227_;
v_isShared_3237_ = v_isSharedCheck_3255_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_val_3234_);
lean_dec(v___x_3227_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3255_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v_leftCount_3238_; lean_object* v_leftIndex_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3252_; 
v_leftCount_3238_ = lean_ctor_get(v_val_3234_, 0);
v_leftIndex_3239_ = lean_ctor_get(v_val_3234_, 1);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_val_3234_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; lean_object* v_unused_3254_; 
v_unused_3253_ = lean_ctor_get(v_val_3234_, 3);
lean_dec(v_unused_3253_);
v_unused_3254_ = lean_ctor_get(v_val_3234_, 2);
lean_dec(v_unused_3254_);
v___x_3241_ = v_val_3234_;
v_isShared_3242_ = v_isSharedCheck_3252_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_leftIndex_3239_);
lean_inc(v_leftCount_3238_);
lean_dec(v_val_3234_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3252_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3243_ = lean_unsigned_to_nat(1u);
v___x_3244_ = lean_nat_add(v_leftCount_3238_, v___x_3243_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v_index_3225_);
v___x_3246_ = v___x_3236_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_index_3225_);
v___x_3246_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3248_; 
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 3, v___x_3246_);
lean_ctor_set(v___x_3241_, 2, v___x_3244_);
v___x_3248_ = v___x_3241_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_leftCount_3238_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v_leftIndex_3239_);
lean_ctor_set(v_reuseFailAlloc_3250_, 2, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3250_, 3, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3224_, v_val_3226_, v___x_3248_);
return v___x_3249_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(lean_object* v_upperBound_3256_, lean_object* v___x_3257_, lean_object* v_fst_3258_, lean_object* v___x_3259_, lean_object* v_a_3260_, lean_object* v_b_3261_){
_start:
{
uint8_t v___x_3262_; 
v___x_3262_ = lean_nat_dec_lt(v_a_3260_, v_upperBound_3256_);
if (v___x_3262_ == 0)
{
lean_dec(v_a_3260_);
return v_b_3261_;
}
else
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3263_ = l_Subarray_get___redArg(v_fst_3258_, v_a_3260_);
lean_inc(v_a_3260_);
v___x_3264_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_b_3261_, v_a_3260_, v___x_3263_);
v___x_3265_ = lean_unsigned_to_nat(1u);
v___x_3266_ = lean_nat_add(v_a_3260_, v___x_3265_);
lean_dec(v_a_3260_);
v_a_3260_ = v___x_3266_;
v_b_3261_ = v___x_3264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg___boxed(lean_object* v_upperBound_3268_, lean_object* v___x_3269_, lean_object* v_fst_3270_, lean_object* v___x_3271_, lean_object* v_a_3272_, lean_object* v_b_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3268_, v___x_3269_, v_fst_3270_, v___x_3271_, v_a_3272_, v_b_3273_);
lean_dec(v___x_3271_);
lean_dec_ref(v_fst_3270_);
lean_dec(v___x_3269_);
lean_dec(v_upperBound_3268_);
return v_res_3274_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3275_ = lean_box(0);
v___x_3276_ = lean_unsigned_to_nat(16u);
v___x_3277_ = lean_mk_array(v___x_3276_, v___x_3275_);
return v___x_3277_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v_hist_3280_; 
v___x_3278_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0);
v___x_3279_ = lean_unsigned_to_nat(0u);
v_hist_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3280_, 0, v___x_3279_);
lean_ctor_set(v_hist_3280_, 1, v___x_3278_);
return v_hist_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v_left_3281_, lean_object* v_right_3282_){
_start:
{
lean_object* v___x_3283_; lean_object* v_snd_3284_; lean_object* v_fst_3285_; lean_object* v_fst_3286_; lean_object* v_snd_3287_; lean_object* v___x_3288_; lean_object* v_snd_3289_; lean_object* v_fst_3290_; lean_object* v_fst_3291_; lean_object* v_snd_3292_; lean_object* v_start_3293_; lean_object* v_stop_3294_; lean_object* v___x_3295_; lean_object* v_hist_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v_start_3299_; lean_object* v_stop_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v_buckets_3303_; lean_object* v___x_3304_; lean_object* v___y_3306_; lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3283_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(v_left_3281_, v_right_3282_);
v_snd_3284_ = lean_ctor_get(v___x_3283_, 1);
lean_inc(v_snd_3284_);
v_fst_3285_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_fst_3285_);
lean_dec_ref(v___x_3283_);
v_fst_3286_ = lean_ctor_get(v_snd_3284_, 0);
lean_inc(v_fst_3286_);
v_snd_3287_ = lean_ctor_get(v_snd_3284_, 1);
lean_inc(v_snd_3287_);
lean_dec(v_snd_3284_);
v___x_3288_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(v_fst_3286_, v_snd_3287_);
v_snd_3289_ = lean_ctor_get(v___x_3288_, 1);
lean_inc(v_snd_3289_);
v_fst_3290_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_fst_3290_);
lean_dec_ref(v___x_3288_);
v_fst_3291_ = lean_ctor_get(v_snd_3289_, 0);
lean_inc(v_fst_3291_);
v_snd_3292_ = lean_ctor_get(v_snd_3289_, 1);
lean_inc(v_snd_3292_);
lean_dec(v_snd_3289_);
v_start_3293_ = lean_ctor_get(v_fst_3290_, 1);
v_stop_3294_ = lean_ctor_get(v_fst_3290_, 2);
v___x_3295_ = lean_unsigned_to_nat(0u);
v_hist_3296_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1);
v___x_3297_ = lean_nat_sub(v_stop_3294_, v_start_3293_);
v___x_3298_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v___x_3297_, v_fst_3291_, v___x_3297_, v_fst_3290_, v___x_3295_, v_hist_3296_);
v_start_3299_ = lean_ctor_get(v_fst_3291_, 1);
v_stop_3300_ = lean_ctor_get(v_fst_3291_, 2);
v___x_3301_ = lean_nat_sub(v_stop_3300_, v_start_3299_);
v___x_3302_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v___x_3301_, v___x_3301_, v_fst_3291_, v___x_3297_, v___x_3295_, v___x_3298_);
lean_dec(v___x_3297_);
lean_dec(v___x_3301_);
v_buckets_3303_ = lean_ctor_get(v___x_3302_, 1);
lean_inc_ref(v_buckets_3303_);
lean_dec_ref(v___x_3302_);
v___x_3304_ = lean_box(0);
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_array_get_size(v_buckets_3303_);
v___x_3334_ = lean_nat_dec_lt(v___x_3295_, v___x_3333_);
if (v___x_3334_ == 0)
{
lean_dec_ref(v_buckets_3303_);
v___y_3306_ = v___x_3332_;
goto v___jp_3305_;
}
else
{
size_t v___x_3335_; size_t v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = lean_usize_of_nat(v___x_3333_);
v___x_3336_ = ((size_t)0ULL);
v___x_3337_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_buckets_3303_, v___x_3335_, v___x_3336_, v___x_3332_);
lean_dec_ref(v_buckets_3303_);
v___y_3306_ = v___x_3337_;
goto v___jp_3305_;
}
v___jp_3305_:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v___y_3306_, v___x_3304_);
lean_dec(v___y_3306_);
if (lean_obj_tag(v___x_3307_) == 1)
{
lean_object* v_val_3308_; lean_object* v_snd_3309_; lean_object* v_snd_3310_; lean_object* v_fst_3311_; lean_object* v_fst_3312_; lean_object* v_snd_3313_; lean_object* v___x_3314_; lean_object* v_fst_3315_; lean_object* v_snd_3316_; lean_object* v___x_3317_; lean_object* v_fst_3318_; lean_object* v_snd_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_val_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_val_3308_);
lean_dec_ref_known(v___x_3307_, 1);
v_snd_3309_ = lean_ctor_get(v_val_3308_, 1);
lean_inc(v_snd_3309_);
lean_dec(v_val_3308_);
v_snd_3310_ = lean_ctor_get(v_snd_3309_, 1);
lean_inc(v_snd_3310_);
v_fst_3311_ = lean_ctor_get(v_snd_3309_, 0);
lean_inc(v_fst_3311_);
lean_dec(v_snd_3309_);
v_fst_3312_ = lean_ctor_get(v_snd_3310_, 0);
lean_inc(v_fst_3312_);
v_snd_3313_ = lean_ctor_get(v_snd_3310_, 1);
lean_inc(v_snd_3313_);
lean_dec(v_snd_3310_);
v___x_3314_ = l_Subarray_split___redArg(v_fst_3290_, v_fst_3312_);
lean_dec(v_fst_3312_);
v_fst_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_fst_3315_);
v_snd_3316_ = lean_ctor_get(v___x_3314_, 1);
lean_inc(v_snd_3316_);
lean_dec_ref(v___x_3314_);
v___x_3317_ = l_Subarray_split___redArg(v_fst_3291_, v_snd_3313_);
lean_dec(v_snd_3313_);
v_fst_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_fst_3318_);
v_snd_3319_ = lean_ctor_get(v___x_3317_, 1);
lean_inc(v_snd_3319_);
lean_dec_ref(v___x_3317_);
v___x_3320_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v_fst_3315_, v_fst_3318_);
v___x_3321_ = l_Array_append___redArg(v_fst_3285_, v___x_3320_);
lean_dec_ref(v___x_3320_);
v___x_3322_ = lean_unsigned_to_nat(1u);
v___x_3323_ = lean_mk_empty_array_with_capacity(v___x_3322_);
v___x_3324_ = lean_array_push(v___x_3323_, v_fst_3311_);
v___x_3325_ = l_Array_append___redArg(v___x_3321_, v___x_3324_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = l_Subarray_drop___redArg(v_snd_3316_, v___x_3322_);
v___x_3327_ = l_Subarray_drop___redArg(v_snd_3319_, v___x_3322_);
v___x_3328_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3326_, v___x_3327_);
v___x_3329_ = l_Array_append___redArg(v___x_3325_, v___x_3328_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = l_Array_append___redArg(v___x_3329_, v_snd_3292_);
lean_dec(v_snd_3292_);
return v___x_3330_;
}
else
{
lean_object* v___x_3331_; 
lean_dec(v___x_3307_);
lean_dec(v_fst_3291_);
lean_dec(v_fst_3290_);
v___x_3331_ = l_Array_append___redArg(v_fst_3285_, v_snd_3292_);
lean_dec(v_snd_3292_);
return v___x_3331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_3338_, lean_object* v_original_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v_fst_3341_; lean_object* v_snd_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3361_; 
v_fst_3341_ = lean_ctor_get(v_a_3340_, 0);
v_snd_3342_ = lean_ctor_get(v_a_3340_, 1);
v_isSharedCheck_3361_ = !lean_is_exclusive(v_a_3340_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3344_ = v_a_3340_;
v_isShared_3345_ = v_isSharedCheck_3361_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_snd_3342_);
lean_inc(v_fst_3341_);
lean_dec(v_a_3340_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3361_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
uint8_t v___x_3346_; 
v___x_3346_ = lean_nat_dec_lt(v_snd_3342_, v___x_3338_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3348_; 
if (v_isShared_3345_ == 0)
{
v___x_3348_ = v___x_3344_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_fst_3341_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_snd_3342_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
else
{
uint8_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3350_ = 1;
v___x_3351_ = lean_array_fget_borrowed(v_original_3339_, v_snd_3342_);
v___x_3352_ = lean_box(v___x_3350_);
lean_inc(v___x_3351_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 1, v___x_3351_);
lean_ctor_set(v___x_3344_, 0, v___x_3352_);
v___x_3354_ = v___x_3344_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3352_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___x_3351_);
v___x_3354_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3355_ = lean_array_push(v_fst_3341_, v___x_3354_);
v___x_3356_ = lean_unsigned_to_nat(1u);
v___x_3357_ = lean_nat_add(v_snd_3342_, v___x_3356_);
lean_dec(v_snd_3342_);
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3355_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v_a_3340_ = v___x_3358_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_3362_, lean_object* v_original_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3362_, v_original_3363_, v_a_3364_);
lean_dec_ref(v_original_3363_);
lean_dec(v___x_3362_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_3366_, size_t v_i_3367_, lean_object* v_bs_3368_){
_start:
{
uint8_t v___x_3369_; 
v___x_3369_ = lean_usize_dec_lt(v_i_3367_, v_sz_3366_);
if (v___x_3369_ == 0)
{
return v_bs_3368_;
}
else
{
lean_object* v_v_3370_; lean_object* v___x_3371_; lean_object* v_bs_x27_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; size_t v___x_3376_; size_t v___x_3377_; lean_object* v___x_3378_; 
v_v_3370_ = lean_array_uget(v_bs_3368_, v_i_3367_);
v___x_3371_ = lean_unsigned_to_nat(0u);
v_bs_x27_3372_ = lean_array_uset(v_bs_3368_, v_i_3367_, v___x_3371_);
v___x_3373_ = 0;
v___x_3374_ = lean_box(v___x_3373_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
lean_ctor_set(v___x_3375_, 1, v_v_3370_);
v___x_3376_ = ((size_t)1ULL);
v___x_3377_ = lean_usize_add(v_i_3367_, v___x_3376_);
v___x_3378_ = lean_array_uset(v_bs_x27_3372_, v_i_3367_, v___x_3375_);
v_i_3367_ = v___x_3377_;
v_bs_3368_ = v___x_3378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_3380_, lean_object* v_i_3381_, lean_object* v_bs_3382_){
_start:
{
size_t v_sz_boxed_3383_; size_t v_i_boxed_3384_; lean_object* v_res_3385_; 
v_sz_boxed_3383_ = lean_unbox_usize(v_sz_3380_);
lean_dec(v_sz_3380_);
v_i_boxed_3384_ = lean_unbox_usize(v_i_3381_);
lean_dec(v_i_3381_);
v_res_3385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_3383_, v_i_boxed_3384_, v_bs_3382_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_3386_, lean_object* v_edited_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v_fst_3389_; lean_object* v_snd_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3409_; 
v_fst_3389_ = lean_ctor_get(v_a_3388_, 0);
v_snd_3390_ = lean_ctor_get(v_a_3388_, 1);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_a_3388_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3392_ = v_a_3388_;
v_isShared_3393_ = v_isSharedCheck_3409_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_snd_3390_);
lean_inc(v_fst_3389_);
lean_dec(v_a_3388_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3409_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
uint8_t v___x_3394_; 
v___x_3394_ = lean_nat_dec_lt(v_snd_3390_, v___x_3386_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3396_; 
if (v_isShared_3393_ == 0)
{
v___x_3396_ = v___x_3392_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_fst_3389_);
lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_snd_3390_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
else
{
uint8_t v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3398_ = 0;
v___x_3399_ = lean_array_fget_borrowed(v_edited_3387_, v_snd_3390_);
v___x_3400_ = lean_box(v___x_3398_);
lean_inc(v___x_3399_);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 1, v___x_3399_);
lean_ctor_set(v___x_3392_, 0, v___x_3400_);
v___x_3402_ = v___x_3392_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3400_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v___x_3399_);
v___x_3402_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3403_ = lean_array_push(v_fst_3389_, v___x_3402_);
v___x_3404_ = lean_unsigned_to_nat(1u);
v___x_3405_ = lean_nat_add(v_snd_3390_, v___x_3404_);
lean_dec(v_snd_3390_);
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3403_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v_a_3388_ = v___x_3406_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_3410_, lean_object* v_edited_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3410_, v_edited_3411_, v_a_3412_);
lean_dec_ref(v_edited_3411_);
lean_dec(v___x_3410_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3414_, size_t v_i_3415_, lean_object* v_bs_3416_){
_start:
{
uint8_t v___x_3417_; 
v___x_3417_ = lean_usize_dec_lt(v_i_3415_, v_sz_3414_);
if (v___x_3417_ == 0)
{
return v_bs_3416_;
}
else
{
lean_object* v_v_3418_; lean_object* v___x_3419_; lean_object* v_bs_x27_3420_; uint8_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; size_t v___x_3424_; size_t v___x_3425_; lean_object* v___x_3426_; 
v_v_3418_ = lean_array_uget(v_bs_3416_, v_i_3415_);
v___x_3419_ = lean_unsigned_to_nat(0u);
v_bs_x27_3420_ = lean_array_uset(v_bs_3416_, v_i_3415_, v___x_3419_);
v___x_3421_ = 1;
v___x_3422_ = lean_box(v___x_3421_);
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
lean_ctor_set(v___x_3423_, 1, v_v_3418_);
v___x_3424_ = ((size_t)1ULL);
v___x_3425_ = lean_usize_add(v_i_3415_, v___x_3424_);
v___x_3426_ = lean_array_uset(v_bs_x27_3420_, v_i_3415_, v___x_3423_);
v_i_3415_ = v___x_3425_;
v_bs_3416_ = v___x_3426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3428_, lean_object* v_i_3429_, lean_object* v_bs_3430_){
_start:
{
size_t v_sz_boxed_3431_; size_t v_i_boxed_3432_; lean_object* v_res_3433_; 
v_sz_boxed_3431_ = lean_unbox_usize(v_sz_3428_);
lean_dec(v_sz_3428_);
v_i_boxed_3432_ = lean_unbox_usize(v_i_3429_);
lean_dec(v_i_3429_);
v_res_3433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3431_, v_i_boxed_3432_, v_bs_3430_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3441_, lean_object* v_edited_3442_){
_start:
{
lean_object* v_i_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v_i_3443_ = lean_unsigned_to_nat(0u);
v___x_3444_ = lean_array_get_size(v_original_3441_);
v___x_3445_ = lean_nat_dec_lt(v_i_3443_, v___x_3444_);
if (v___x_3445_ == 0)
{
size_t v_sz_3446_; size_t v___x_3447_; lean_object* v___x_3448_; 
lean_dec_ref(v_original_3441_);
v_sz_3446_ = lean_array_size(v_edited_3442_);
v___x_3447_ = ((size_t)0ULL);
v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3446_, v___x_3447_, v_edited_3442_);
return v___x_3448_;
}
else
{
lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3449_ = lean_array_get_size(v_edited_3442_);
v___x_3450_ = lean_nat_dec_lt(v_i_3443_, v___x_3449_);
if (v___x_3450_ == 0)
{
size_t v_sz_3451_; size_t v___x_3452_; lean_object* v___x_3453_; 
lean_dec_ref(v_edited_3442_);
v_sz_3451_ = lean_array_size(v_original_3441_);
v___x_3452_ = ((size_t)0ULL);
v___x_3453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3451_, v___x_3452_, v_original_3441_);
return v___x_3453_;
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v_ds_3456_; lean_object* v___x_3457_; size_t v_sz_3458_; size_t v___x_3459_; lean_object* v___x_3460_; lean_object* v_snd_3461_; lean_object* v_fst_3462_; lean_object* v_fst_3463_; lean_object* v_snd_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3483_; 
lean_inc_ref(v_original_3441_);
v___x_3454_ = l_Array_toSubarray___redArg(v_original_3441_, v_i_3443_, v___x_3444_);
lean_inc_ref(v_edited_3442_);
v___x_3455_ = l_Array_toSubarray___redArg(v_edited_3442_, v_i_3443_, v___x_3449_);
v_ds_3456_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3454_, v___x_3455_);
v___x_3457_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3458_ = lean_array_size(v_ds_3456_);
v___x_3459_ = ((size_t)0ULL);
v___x_3460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_3442_, v___x_3449_, v_original_3441_, v___x_3444_, v_ds_3456_, v_sz_3458_, v___x_3459_, v___x_3457_);
lean_dec_ref(v_ds_3456_);
v_snd_3461_ = lean_ctor_get(v___x_3460_, 1);
lean_inc(v_snd_3461_);
v_fst_3462_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_fst_3462_);
lean_dec_ref(v___x_3460_);
v_fst_3463_ = lean_ctor_get(v_snd_3461_, 0);
v_snd_3464_ = lean_ctor_get(v_snd_3461_, 1);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_snd_3461_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3466_ = v_snd_3461_;
v_isShared_3467_ = v_isSharedCheck_3483_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_snd_3464_);
lean_inc(v_fst_3463_);
lean_dec(v_snd_3461_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3483_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 1, v_fst_3463_);
lean_ctor_set(v___x_3466_, 0, v_fst_3462_);
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_fst_3462_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_fst_3463_);
v___x_3469_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3470_; lean_object* v_fst_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3480_; 
v___x_3470_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3444_, v_original_3441_, v___x_3469_);
lean_dec_ref(v_original_3441_);
v_fst_3471_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3480_ == 0)
{
lean_object* v_unused_3481_; 
v_unused_3481_ = lean_ctor_get(v___x_3470_, 1);
lean_dec(v_unused_3481_);
v___x_3473_ = v___x_3470_;
v_isShared_3474_ = v_isSharedCheck_3480_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_fst_3471_);
lean_dec(v___x_3470_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3480_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 1, v_snd_3464_);
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_fst_3471_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_snd_3464_);
v___x_3476_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3477_; lean_object* v_fst_3478_; 
v___x_3477_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3449_, v_edited_3442_, v___x_3476_);
lean_dec_ref(v_edited_3442_);
v_fst_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_fst_3478_);
lean_dec_ref(v___x_3477_);
return v_fst_3478_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3484_, lean_object* v_x_3485_, lean_object* v_x_3486_){
_start:
{
if (lean_obj_tag(v_x_3485_) == 0)
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = l_List_reverse___redArg(v_x_3486_);
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
else
{
lean_object* v_head_3490_; lean_object* v_tail_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3500_; 
v_head_3490_ = lean_ctor_get(v_x_3485_, 0);
v_tail_3491_ = lean_ctor_get(v_x_3485_, 1);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_x_3485_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3493_ = v_x_3485_;
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_tail_3491_);
lean_inc(v_head_3490_);
lean_dec(v_x_3485_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3495_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3490_, v___y_3484_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 1, v_x_3486_);
lean_ctor_set(v___x_3493_, 0, v___x_3495_);
v___x_3497_ = v___x_3493_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_x_3486_);
v___x_3497_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
v_x_3485_ = v_tail_3491_;
v_x_3486_ = v___x_3497_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3501_, lean_object* v_x_3502_, lean_object* v_x_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3501_, v_x_3502_, v_x_3503_);
lean_dec(v___y_3501_);
return v_res_3505_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0));
v___x_3508_ = l_Lean_stringToMessageData(v___x_3507_);
return v___x_3508_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = l_Lean_MessageLog_empty;
v___x_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; uint8_t v___y_3567_; lean_object* v___y_3631_; uint8_t v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; uint8_t v___y_3636_; lean_object* v___y_3637_; uint8_t v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v_dc_x3f_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___x_3772_; uint8_t v___x_3773_; 
v___x_3772_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
lean_inc(v_x_3522_);
v___x_3773_ = l_Lean_Syntax_isOfKind(v_x_3522_, v___x_3772_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; 
lean_dec(v_x_3522_);
v___x_3774_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3774_;
}
else
{
lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3775_ = lean_unsigned_to_nat(0u);
v___x_3776_ = l_Lean_Syntax_getArg(v_x_3522_, v___x_3775_);
v___x_3777_ = l_Lean_Syntax_isNone(v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; uint8_t v___x_3779_; 
v___x_3778_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3776_);
v___x_3779_ = l_Lean_Syntax_matchesNull(v___x_3776_, v___x_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; 
lean_dec(v___x_3776_);
lean_dec(v_x_3522_);
v___x_3780_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3780_;
}
else
{
lean_object* v_dc_x3f_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v_dc_x3f_3781_ = l_Lean_Syntax_getArg(v___x_3776_, v___x_3775_);
lean_dec(v___x_3776_);
v___x_3782_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3781_);
v___x_3783_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3781_, v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; 
lean_dec(v_dc_x3f_3781_);
lean_dec(v_x_3522_);
v___x_3784_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3784_;
}
else
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3785_, 0, v_dc_x3f_3781_);
v_dc_x3f_3753_ = v___x_3785_;
v___y_3754_ = v_a_3523_;
v___y_3755_ = v_a_3524_;
goto v___jp_3752_;
}
}
}
else
{
lean_object* v___x_3786_; 
lean_dec(v___x_3776_);
v___x_3786_ = lean_box(0);
v_dc_x3f_3753_ = v___x_3786_;
v___y_3754_ = v_a_3523_;
v___y_3755_ = v_a_3524_;
goto v___jp_3752_;
}
}
v___jp_3526_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3532_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1);
v___x_3533_ = l_Lean_stringToMessageData(v___y_3531_);
v___x_3534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3532_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3530_, v___x_3534_, v___y_3528_, v___y_3529_);
lean_dec(v___y_3530_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3556_; 
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; 
v_unused_3557_ = lean_ctor_get(v___x_3535_, 0);
lean_dec(v_unused_3557_);
v___x_3537_ = v___x_3535_;
v_isShared_3538_ = v_isSharedCheck_3556_;
goto v_resetjp_3536_;
}
else
{
lean_dec(v___x_3535_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3556_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_Elab_Command_getRef___redArg(v___y_3528_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3545_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3539_, 1);
v___x_3541_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
lean_ctor_set(v___x_3542_, 1, v___y_3527_);
v___x_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3543_, 0, v_a_3540_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 10);
lean_ctor_set(v___x_3537_, 0, v___x_3543_);
v___x_3545_ = v___x_3537_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3545_, v___y_3528_, v___y_3529_);
return v___x_3546_;
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_del_object(v___x_3537_);
lean_dec_ref(v___y_3527_);
v_a_3548_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3539_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3539_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3527_);
return v___x_3535_;
}
}
v___jp_3558_:
{
if (v___y_3567_ == 0)
{
lean_object* v___x_3568_; lean_object* v_env_3569_; lean_object* v_scopes_3570_; lean_object* v_usedQuotCtxts_3571_; lean_object* v_nextMacroScope_3572_; lean_object* v_maxRecDepth_3573_; lean_object* v_ngen_3574_; lean_object* v_auxDeclNGen_3575_; lean_object* v_infoState_3576_; lean_object* v_traceState_3577_; lean_object* v_snapshotTasks_3578_; lean_object* v_prevLinterStates_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3605_; 
lean_dec(v___y_3565_);
v___x_3568_ = lean_st_ref_take(v___y_3564_);
v_env_3569_ = lean_ctor_get(v___x_3568_, 0);
v_scopes_3570_ = lean_ctor_get(v___x_3568_, 2);
v_usedQuotCtxts_3571_ = lean_ctor_get(v___x_3568_, 3);
v_nextMacroScope_3572_ = lean_ctor_get(v___x_3568_, 4);
v_maxRecDepth_3573_ = lean_ctor_get(v___x_3568_, 5);
v_ngen_3574_ = lean_ctor_get(v___x_3568_, 6);
v_auxDeclNGen_3575_ = lean_ctor_get(v___x_3568_, 7);
v_infoState_3576_ = lean_ctor_get(v___x_3568_, 8);
v_traceState_3577_ = lean_ctor_get(v___x_3568_, 9);
v_snapshotTasks_3578_ = lean_ctor_get(v___x_3568_, 10);
v_prevLinterStates_3579_ = lean_ctor_get(v___x_3568_, 11);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3605_ == 0)
{
lean_object* v_unused_3606_; 
v_unused_3606_ = lean_ctor_get(v___x_3568_, 1);
lean_dec(v_unused_3606_);
v___x_3581_ = v___x_3568_;
v_isShared_3582_ = v_isSharedCheck_3605_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_prevLinterStates_3579_);
lean_inc(v_snapshotTasks_3578_);
lean_inc(v_traceState_3577_);
lean_inc(v_infoState_3576_);
lean_inc(v_auxDeclNGen_3575_);
lean_inc(v_ngen_3574_);
lean_inc(v_maxRecDepth_3573_);
lean_inc(v_nextMacroScope_3572_);
lean_inc(v_usedQuotCtxts_3571_);
lean_inc(v_scopes_3570_);
lean_inc(v_env_3569_);
lean_dec(v___x_3568_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3605_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___y_3562_);
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_env_3569_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v___y_3562_);
lean_ctor_set(v_reuseFailAlloc_3604_, 2, v_scopes_3570_);
lean_ctor_set(v_reuseFailAlloc_3604_, 3, v_usedQuotCtxts_3571_);
lean_ctor_set(v_reuseFailAlloc_3604_, 4, v_nextMacroScope_3572_);
lean_ctor_set(v_reuseFailAlloc_3604_, 5, v_maxRecDepth_3573_);
lean_ctor_set(v_reuseFailAlloc_3604_, 6, v_ngen_3574_);
lean_ctor_set(v_reuseFailAlloc_3604_, 7, v_auxDeclNGen_3575_);
lean_ctor_set(v_reuseFailAlloc_3604_, 8, v_infoState_3576_);
lean_ctor_set(v_reuseFailAlloc_3604_, 9, v_traceState_3577_);
lean_ctor_set(v_reuseFailAlloc_3604_, 10, v_snapshotTasks_3578_);
lean_ctor_set(v_reuseFailAlloc_3604_, 11, v_prevLinterStates_3579_);
v___x_3584_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v_scopes_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v_opts_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3585_ = lean_st_ref_set(v___y_3564_, v___x_3584_);
v___x_3586_ = lean_st_ref_get(v___y_3564_);
v_scopes_3587_ = lean_ctor_get(v___x_3586_, 2);
lean_inc(v_scopes_3587_);
lean_dec(v___x_3586_);
v___x_3588_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3589_ = l_List_head_x21___redArg(v___x_3588_, v_scopes_3587_);
lean_dec(v_scopes_3587_);
v_opts_3590_ = lean_ctor_get(v___x_3589_, 1);
lean_inc_ref(v_opts_3590_);
lean_dec(v___x_3589_);
v___x_3591_ = l_Lean_guard__msgs_diff;
v___x_3592_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3590_, v___x_3591_);
lean_dec_ref(v_opts_3590_);
if (v___x_3592_ == 0)
{
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3561_);
lean_inc_ref(v___y_3560_);
v___y_3527_ = v___y_3560_;
v___y_3528_ = v___y_3559_;
v___y_3529_ = v___y_3564_;
v___y_3530_ = v___y_3566_;
v___y_3531_ = v___y_3560_;
goto v___jp_3526_;
}
else
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3593_ = lean_string_utf8_byte_size(v___y_3561_);
lean_inc(v___y_3563_);
lean_inc_ref(v___y_3561_);
v___x_3594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3594_, 0, v___y_3561_);
lean_ctor_set(v___x_3594_, 1, v___y_3563_);
lean_ctor_set(v___x_3594_, 2, v___x_3593_);
v___x_3595_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3594_);
v___x_3596_ = lean_mk_empty_array_with_capacity(v___y_3563_);
lean_inc_ref(v___x_3596_);
v___x_3597_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3561_, v___x_3594_, v___x_3593_, v___x_3595_, v___x_3596_);
lean_dec_ref_known(v___x_3594_, 3);
v___x_3598_ = lean_string_utf8_byte_size(v___y_3560_);
lean_inc_ref_n(v___y_3560_, 2);
v___x_3599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3599_, 0, v___y_3560_);
lean_ctor_set(v___x_3599_, 1, v___y_3563_);
lean_ctor_set(v___x_3599_, 2, v___x_3598_);
v___x_3600_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3599_);
v___x_3601_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3560_, v___x_3599_, v___x_3598_, v___x_3600_, v___x_3596_);
lean_dec_ref_known(v___x_3599_, 3);
v___x_3602_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3597_, v___x_3601_);
v___x_3603_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3602_);
lean_dec_ref(v___x_3602_);
v___y_3527_ = v___y_3560_;
v___y_3528_ = v___y_3559_;
v___y_3529_ = v___y_3564_;
v___y_3530_ = v___y_3566_;
v___y_3531_ = v___x_3603_;
goto v___jp_3526_;
}
}
}
}
else
{
lean_object* v___x_3607_; lean_object* v_env_3608_; lean_object* v_scopes_3609_; lean_object* v_usedQuotCtxts_3610_; lean_object* v_nextMacroScope_3611_; lean_object* v_maxRecDepth_3612_; lean_object* v_ngen_3613_; lean_object* v_auxDeclNGen_3614_; lean_object* v_infoState_3615_; lean_object* v_traceState_3616_; lean_object* v_snapshotTasks_3617_; lean_object* v_prevLinterStates_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v___y_3566_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec_ref(v___y_3560_);
v___x_3607_ = lean_st_ref_take(v___y_3564_);
v_env_3608_ = lean_ctor_get(v___x_3607_, 0);
v_scopes_3609_ = lean_ctor_get(v___x_3607_, 2);
v_usedQuotCtxts_3610_ = lean_ctor_get(v___x_3607_, 3);
v_nextMacroScope_3611_ = lean_ctor_get(v___x_3607_, 4);
v_maxRecDepth_3612_ = lean_ctor_get(v___x_3607_, 5);
v_ngen_3613_ = lean_ctor_get(v___x_3607_, 6);
v_auxDeclNGen_3614_ = lean_ctor_get(v___x_3607_, 7);
v_infoState_3615_ = lean_ctor_get(v___x_3607_, 8);
v_traceState_3616_ = lean_ctor_get(v___x_3607_, 9);
v_snapshotTasks_3617_ = lean_ctor_get(v___x_3607_, 10);
v_prevLinterStates_3618_ = lean_ctor_get(v___x_3607_, 11);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; 
v_unused_3629_ = lean_ctor_get(v___x_3607_, 1);
lean_dec(v_unused_3629_);
v___x_3620_ = v___x_3607_;
v_isShared_3621_ = v_isSharedCheck_3628_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_prevLinterStates_3618_);
lean_inc(v_snapshotTasks_3617_);
lean_inc(v_traceState_3616_);
lean_inc(v_infoState_3615_);
lean_inc(v_auxDeclNGen_3614_);
lean_inc(v_ngen_3613_);
lean_inc(v_maxRecDepth_3612_);
lean_inc(v_nextMacroScope_3611_);
lean_inc(v_usedQuotCtxts_3610_);
lean_inc(v_scopes_3609_);
lean_inc(v_env_3608_);
lean_dec(v___x_3607_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3628_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 1, v___y_3565_);
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_env_3608_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v___y_3565_);
lean_ctor_set(v_reuseFailAlloc_3627_, 2, v_scopes_3609_);
lean_ctor_set(v_reuseFailAlloc_3627_, 3, v_usedQuotCtxts_3610_);
lean_ctor_set(v_reuseFailAlloc_3627_, 4, v_nextMacroScope_3611_);
lean_ctor_set(v_reuseFailAlloc_3627_, 5, v_maxRecDepth_3612_);
lean_ctor_set(v_reuseFailAlloc_3627_, 6, v_ngen_3613_);
lean_ctor_set(v_reuseFailAlloc_3627_, 7, v_auxDeclNGen_3614_);
lean_ctor_set(v_reuseFailAlloc_3627_, 8, v_infoState_3615_);
lean_ctor_set(v_reuseFailAlloc_3627_, 9, v_traceState_3616_);
lean_ctor_set(v_reuseFailAlloc_3627_, 10, v_snapshotTasks_3617_);
lean_ctor_set(v_reuseFailAlloc_3627_, 11, v_prevLinterStates_3618_);
v___x_3623_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3624_ = lean_st_ref_set(v___y_3564_, v___x_3623_);
v___x_3625_ = lean_box(0);
v___x_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
return v___x_3626_;
}
}
}
}
v___jp_3630_:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v_a_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v_str_3653_; lean_object* v_startInclusive_3654_; lean_object* v_endExclusive_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3670_; 
v___x_3643_ = l_Lean_MessageLog_toList(v___y_3641_);
lean_dec(v___y_3641_);
v___x_3644_ = lean_box(0);
v___x_3645_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3642_, v___x_3643_, v___x_3644_);
lean_dec(v___y_3642_);
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref(v___x_3645_);
v___x_3647_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3636_, v_a_3646_);
v___x_3648_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3649_ = l_String_intercalate(v___x_3648_, v___x_3647_);
v___x_3650_ = lean_string_utf8_byte_size(v___x_3649_);
lean_inc(v___y_3635_);
v___x_3651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v___y_3635_);
lean_ctor_set(v___x_3651_, 2, v___x_3650_);
v___x_3652_ = l_String_Slice_trimAscii(v___x_3651_);
v_str_3653_ = lean_ctor_get(v___x_3652_, 0);
v_startInclusive_3654_ = lean_ctor_get(v___x_3652_, 1);
v_endExclusive_3655_ = lean_ctor_get(v___x_3652_, 2);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3657_ = v___x_3652_;
v_isShared_3658_ = v_isSharedCheck_3670_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_endExclusive_3655_);
lean_inc(v_startInclusive_3654_);
lean_inc(v_str_3653_);
lean_dec(v___x_3652_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3670_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_string_utf8_extract_fast(v_str_3653_, v_startInclusive_3654_, v_endExclusive_3655_);
lean_dec(v_endExclusive_3655_);
lean_dec(v_startInclusive_3654_);
lean_dec_ref(v_str_3653_);
if (v___y_3632_ == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
lean_del_object(v___x_3657_);
lean_inc_ref(v___y_3633_);
v___x_3660_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3638_, v___y_3633_);
lean_inc_ref(v___x_3659_);
v___x_3661_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3638_, v___x_3659_);
v___x_3662_ = lean_string_dec_eq(v___x_3660_, v___x_3661_);
lean_dec_ref(v___x_3661_);
lean_dec_ref(v___x_3660_);
v___y_3559_ = v___y_3631_;
v___y_3560_ = v___x_3659_;
v___y_3561_ = v___y_3633_;
v___y_3562_ = v___y_3634_;
v___y_3563_ = v___y_3635_;
v___y_3564_ = v___y_3637_;
v___y_3565_ = v___y_3639_;
v___y_3566_ = v___y_3640_;
v___y_3567_ = v___x_3662_;
goto v___jp_3558_;
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3667_; 
lean_inc_ref(v___x_3659_);
v___x_3663_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3638_, v___x_3659_);
lean_inc_ref(v___y_3633_);
v___x_3664_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3638_, v___y_3633_);
v___x_3665_ = lean_string_utf8_byte_size(v___x_3663_);
lean_inc(v___y_3635_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 2, v___x_3665_);
lean_ctor_set(v___x_3657_, 1, v___y_3635_);
lean_ctor_set(v___x_3657_, 0, v___x_3663_);
v___x_3667_ = v___x_3657_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v___y_3635_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
uint8_t v___x_3668_; 
v___x_3668_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3664_, v___x_3667_);
lean_dec_ref(v___x_3667_);
v___y_3559_ = v___y_3631_;
v___y_3560_ = v___x_3659_;
v___y_3561_ = v___y_3633_;
v___y_3562_ = v___y_3634_;
v___y_3563_ = v___y_3635_;
v___y_3564_ = v___y_3637_;
v___y_3565_ = v___y_3639_;
v___y_3566_ = v___y_3640_;
v___y_3567_ = v___x_3668_;
goto v___jp_3558_;
}
}
}
}
v___jp_3671_:
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3676_, v___y_3673_, v___y_3674_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v_filterFn_3680_; uint8_t v_whitespace_3681_; uint8_t v_ordering_3682_; uint8_t v_reportPositions_3683_; uint8_t v_substring_3684_; lean_object* v___x_3685_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3678_, 1);
v_filterFn_3680_ = lean_ctor_get(v_a_3679_, 0);
lean_inc_ref(v_filterFn_3680_);
v_whitespace_3681_ = lean_ctor_get_uint8(v_a_3679_, sizeof(void*)*1);
v_ordering_3682_ = lean_ctor_get_uint8(v_a_3679_, sizeof(void*)*1 + 1);
v_reportPositions_3683_ = lean_ctor_get_uint8(v_a_3679_, sizeof(void*)*1 + 2);
v_substring_3684_ = lean_ctor_get_uint8(v_a_3679_, sizeof(void*)*1 + 3);
lean_dec(v_a_3679_);
v___x_3685_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3672_, v___y_3673_, v___y_3674_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v_a_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v_str_3695_; lean_object* v_startInclusive_3696_; lean_object* v_endExclusive_3697_; lean_object* v_fst_3698_; lean_object* v_snd_3699_; lean_object* v_fileMap_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3685_, 1);
v___x_3687_ = l_Lean_MessageLog_toList(v_a_3686_);
v___x_3688_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3689_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3680_, v___x_3687_, v___x_3688_);
lean_dec(v___x_3687_);
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_a_3690_);
lean_dec_ref(v___x_3689_);
v___x_3691_ = lean_unsigned_to_nat(0u);
v___x_3692_ = lean_string_utf8_byte_size(v___y_3677_);
v___x_3693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3693_, 0, v___y_3677_);
lean_ctor_set(v___x_3693_, 1, v___x_3691_);
lean_ctor_set(v___x_3693_, 2, v___x_3692_);
v___x_3694_ = l_String_Slice_trimAscii(v___x_3693_);
v_str_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc_ref(v_str_3695_);
v_startInclusive_3696_ = lean_ctor_get(v___x_3694_, 1);
lean_inc(v_startInclusive_3696_);
v_endExclusive_3697_ = lean_ctor_get(v___x_3694_, 2);
lean_inc(v_endExclusive_3697_);
lean_dec_ref(v___x_3694_);
v_fst_3698_ = lean_ctor_get(v_a_3690_, 0);
lean_inc(v_fst_3698_);
v_snd_3699_ = lean_ctor_get(v_a_3690_, 1);
lean_inc(v_snd_3699_);
lean_dec(v_a_3690_);
v_fileMap_3700_ = lean_ctor_get(v___y_3673_, 1);
v___x_3701_ = lean_string_utf8_extract_fast(v_str_3695_, v_startInclusive_3696_, v_endExclusive_3697_);
lean_dec(v_endExclusive_3697_);
lean_dec(v_startInclusive_3696_);
lean_dec_ref(v_str_3695_);
v___x_3702_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3701_);
if (v_reportPositions_3683_ == 0)
{
lean_object* v___x_3703_; 
v___x_3703_ = lean_box(0);
v___y_3631_ = v___y_3673_;
v___y_3632_ = v_substring_3684_;
v___y_3633_ = v___x_3702_;
v___y_3634_ = v_a_3686_;
v___y_3635_ = v___x_3691_;
v___y_3636_ = v_ordering_3682_;
v___y_3637_ = v___y_3674_;
v___y_3638_ = v_whitespace_3681_;
v___y_3639_ = v_snd_3699_;
v___y_3640_ = v___y_3675_;
v___y_3641_ = v_fst_3698_;
v___y_3642_ = v___x_3703_;
goto v___jp_3630_;
}
else
{
uint8_t v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = 0;
v___x_3705_ = l_Lean_Syntax_getPos_x3f(v___y_3675_, v___x_3704_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_box(0);
v___y_3631_ = v___y_3673_;
v___y_3632_ = v_substring_3684_;
v___y_3633_ = v___x_3702_;
v___y_3634_ = v_a_3686_;
v___y_3635_ = v___x_3691_;
v___y_3636_ = v_ordering_3682_;
v___y_3637_ = v___y_3674_;
v___y_3638_ = v_whitespace_3681_;
v___y_3639_ = v_snd_3699_;
v___y_3640_ = v___y_3675_;
v___y_3641_ = v_fst_3698_;
v___y_3642_ = v___x_3706_;
goto v___jp_3630_;
}
else
{
lean_object* v_val_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3716_; 
v_val_3707_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3709_ = v___x_3705_;
v_isShared_3710_ = v_isSharedCheck_3716_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_val_3707_);
lean_dec(v___x_3705_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3716_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3711_; lean_object* v_line_3712_; lean_object* v___x_3714_; 
lean_inc_ref(v_fileMap_3700_);
v___x_3711_ = l_Lean_FileMap_toPosition(v_fileMap_3700_, v_val_3707_);
lean_dec(v_val_3707_);
v_line_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_line_3712_);
lean_dec_ref(v___x_3711_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v_line_3712_);
v___x_3714_ = v___x_3709_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_line_3712_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
v___y_3631_ = v___y_3673_;
v___y_3632_ = v_substring_3684_;
v___y_3633_ = v___x_3702_;
v___y_3634_ = v_a_3686_;
v___y_3635_ = v___x_3691_;
v___y_3636_ = v_ordering_3682_;
v___y_3637_ = v___y_3674_;
v___y_3638_ = v_whitespace_3681_;
v___y_3639_ = v_snd_3699_;
v___y_3640_ = v___y_3675_;
v___y_3641_ = v_fst_3698_;
v___y_3642_ = v___x_3714_;
goto v___jp_3630_;
}
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec_ref(v_filterFn_3680_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3675_);
v_a_3717_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3685_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3685_);
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
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3675_);
lean_dec(v___y_3672_);
v_a_3725_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3678_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3678_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
v___jp_3733_:
{
if (lean_obj_tag(v___y_3737_) == 0)
{
lean_object* v___x_3740_; 
v___x_3740_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_3672_ = v___y_3734_;
v___y_3673_ = v___y_3735_;
v___y_3674_ = v___y_3736_;
v___y_3675_ = v___y_3738_;
v___y_3676_ = v___y_3739_;
v___y_3677_ = v___x_3740_;
goto v___jp_3671_;
}
else
{
lean_object* v_val_3741_; lean_object* v___x_3742_; 
v_val_3741_ = lean_ctor_get(v___y_3737_, 0);
lean_inc(v_val_3741_);
lean_dec_ref_known(v___y_3737_, 1);
v___x_3742_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3741_, v___y_3735_, v___y_3736_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___y_3672_ = v___y_3734_;
v___y_3673_ = v___y_3735_;
v___y_3674_ = v___y_3736_;
v___y_3675_ = v___y_3738_;
v___y_3676_ = v___y_3739_;
v___y_3677_ = v_a_3743_;
goto v___jp_3671_;
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_dec(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec(v___y_3734_);
v_a_3744_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3742_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3742_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
v___jp_3752_:
{
lean_object* v___x_3756_; lean_object* v_tk_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3756_ = lean_unsigned_to_nat(1u);
v_tk_3757_ = l_Lean_Syntax_getArg(v_x_3522_, v___x_3756_);
v___x_3758_ = lean_unsigned_to_nat(2u);
v___x_3759_ = l_Lean_Syntax_getArg(v_x_3522_, v___x_3758_);
v___x_3760_ = lean_unsigned_to_nat(4u);
v___x_3761_ = l_Lean_Syntax_getArg(v_x_3522_, v___x_3760_);
lean_dec(v_x_3522_);
v___x_3762_ = l_Lean_Syntax_getOptional_x3f(v___x_3759_);
lean_dec(v___x_3759_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_box(0);
v___y_3734_ = v___x_3761_;
v___y_3735_ = v___y_3754_;
v___y_3736_ = v___y_3755_;
v___y_3737_ = v_dc_x3f_3753_;
v___y_3738_ = v_tk_3757_;
v___y_3739_ = v___x_3763_;
goto v___jp_3733_;
}
else
{
lean_object* v_val_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
v_val_3764_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3762_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_val_3764_);
lean_dec(v___x_3762_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_val_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
v___y_3734_ = v___x_3761_;
v___y_3735_ = v___y_3754_;
v___y_3736_ = v___y_3755_;
v___y_3737_ = v_dc_x3f_3753_;
v___y_3738_ = v_tk_3757_;
v___y_3739_ = v___x_3769_;
goto v___jp_3733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3787_, v_a_3788_, v_a_3789_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3792_, lean_object* v_as_3793_, lean_object* v_as_x27_3794_, lean_object* v_b_3795_, lean_object* v_a_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3792_, v_as_x27_3794_, v_b_3795_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3801_, lean_object* v_as_3802_, lean_object* v_as_x27_3803_, lean_object* v_b_3804_, lean_object* v_a_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3801_, v_as_3802_, v_as_x27_3803_, v_b_3804_, v_a_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v_as_x27_3803_);
lean_dec(v_as_3802_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3810_, lean_object* v_x_3811_, lean_object* v_x_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3810_, v_x_3811_, v_x_3812_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3817_, lean_object* v_x_3818_, lean_object* v_x_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3817_, v_x_3818_, v_x_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3817_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3824_, v___y_3826_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3834_, lean_object* v___x_3835_, lean_object* v___x_3836_, lean_object* v_inst_3837_, lean_object* v_R_3838_, lean_object* v_a_3839_, lean_object* v_b_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3834_, v___x_3835_, v___x_3836_, v_a_3839_, v_b_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3842_, lean_object* v___x_3843_, lean_object* v___x_3844_, lean_object* v_inst_3845_, lean_object* v_R_3846_, lean_object* v_a_3847_, lean_object* v_b_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3842_, v___x_3843_, v___x_3844_, v_inst_3845_, v_R_3846_, v_a_3847_, v_b_3848_);
lean_dec_ref(v___x_3843_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3850_, v___y_3852_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3855_, v___y_3856_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3860_, lean_object* v___x_3861_, lean_object* v___x_3862_, lean_object* v_inst_3863_, lean_object* v_R_3864_, lean_object* v_a_3865_, lean_object* v_b_3866_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3860_, v___x_3861_, v___x_3862_, v_a_3865_, v_b_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3868_, lean_object* v___x_3869_, lean_object* v___x_3870_, lean_object* v_inst_3871_, lean_object* v_R_3872_, lean_object* v_a_3873_, lean_object* v_b_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3868_, v___x_3869_, v___x_3870_, v_inst_3871_, v_R_3872_, v_a_3873_, v_b_3874_);
lean_dec_ref(v___x_3869_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v_original_3876_, lean_object* v___x_3877_, lean_object* v_a_3878_, lean_object* v_inst_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_3876_, v___x_3877_, v_a_3878_, v_a_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v_original_3882_, lean_object* v___x_3883_, lean_object* v_a_3884_, lean_object* v_inst_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_original_3882_, v___x_3883_, v_a_3884_, v_inst_3885_, v_a_3886_);
lean_dec_ref(v_a_3884_);
lean_dec(v___x_3883_);
lean_dec_ref(v_original_3882_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_edited_3888_, lean_object* v___x_3889_, lean_object* v_a_3890_, lean_object* v_inst_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_3888_, v___x_3889_, v_a_3890_, v_a_3892_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object* v_edited_3894_, lean_object* v___x_3895_, lean_object* v_a_3896_, lean_object* v_inst_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_edited_3894_, v___x_3895_, v_a_3896_, v_inst_3897_, v_a_3898_);
lean_dec_ref(v_a_3896_);
lean_dec(v___x_3895_);
lean_dec_ref(v_edited_3894_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3900_, lean_object* v_original_3901_, lean_object* v_inst_3902_, lean_object* v_a_3903_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3900_, v_original_3901_, v_a_3903_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3905_, lean_object* v_original_3906_, lean_object* v_inst_3907_, lean_object* v_a_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3905_, v_original_3906_, v_inst_3907_, v_a_3908_);
lean_dec_ref(v_original_3906_);
lean_dec(v___x_3905_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3910_, lean_object* v_edited_3911_, lean_object* v_inst_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3910_, v_edited_3911_, v_a_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3915_, lean_object* v_edited_3916_, lean_object* v_inst_3917_, lean_object* v_a_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3915_, v_edited_3916_, v_inst_3917_, v_a_3918_);
lean_dec_ref(v_edited_3916_);
lean_dec(v___x_3915_);
return v_res_3919_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3920_, lean_object* v_inst_3921_, lean_object* v_R_3922_, lean_object* v_a_3923_, uint8_t v_b_3924_, lean_object* v_c_3925_){
_start:
{
uint8_t v___x_3926_; 
v___x_3926_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3920_, v_a_3923_, v_b_3924_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3927_, lean_object* v_inst_3928_, lean_object* v_R_3929_, lean_object* v_a_3930_, lean_object* v_b_3931_, lean_object* v_c_3932_){
_start:
{
uint8_t v_b_boxed_3933_; uint8_t v_res_3934_; lean_object* v_r_3935_; 
v_b_boxed_3933_ = lean_unbox(v_b_3931_);
v_res_3934_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3927_, v_inst_3928_, v_R_3929_, v_a_3930_, v_b_boxed_3933_, v_c_3932_);
lean_dec_ref(v_s_3927_);
v_r_3935_ = lean_box(v_res_3934_);
return v_r_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3936_, lean_object* v_ref_3937_, lean_object* v_msg_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3937_, v_msg_3938_, v___y_3939_, v___y_3940_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3943_, lean_object* v_ref_3944_, lean_object* v_msg_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3943_, v_ref_3944_, v_msg_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v_ref_3944_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(lean_object* v_as_3950_, lean_object* v_as_x27_3951_, lean_object* v_b_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3951_, v_b_3952_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___boxed(lean_object* v_as_3955_, lean_object* v_as_x27_3956_, lean_object* v_b_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(v_as_3955_, v_as_x27_3956_, v_b_3957_, v_a_3958_);
lean_dec(v_as_x27_3956_);
lean_dec(v_as_3955_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(lean_object* v_lsize_3960_, lean_object* v_rsize_3961_, lean_object* v_histogram_3962_, lean_object* v_index_3963_, lean_object* v_val_3964_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_histogram_3962_, v_index_3963_, v_val_3964_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___boxed(lean_object* v_lsize_3966_, lean_object* v_rsize_3967_, lean_object* v_histogram_3968_, lean_object* v_index_3969_, lean_object* v_val_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(v_lsize_3966_, v_rsize_3967_, v_histogram_3968_, v_index_3969_, v_val_3970_);
lean_dec(v_rsize_3967_);
lean_dec(v_lsize_3966_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(lean_object* v_upperBound_3972_, lean_object* v___x_3973_, lean_object* v_fst_3974_, lean_object* v___x_3975_, lean_object* v_inst_3976_, lean_object* v_R_3977_, lean_object* v_a_3978_, lean_object* v_b_3979_, lean_object* v_c_3980_){
_start:
{
lean_object* v___x_3981_; 
v___x_3981_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3972_, v___x_3973_, v_fst_3974_, v___x_3975_, v_a_3978_, v_b_3979_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___boxed(lean_object* v_upperBound_3982_, lean_object* v___x_3983_, lean_object* v_fst_3984_, lean_object* v___x_3985_, lean_object* v_inst_3986_, lean_object* v_R_3987_, lean_object* v_a_3988_, lean_object* v_b_3989_, lean_object* v_c_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(v_upperBound_3982_, v___x_3983_, v_fst_3984_, v___x_3985_, v_inst_3986_, v_R_3987_, v_a_3988_, v_b_3989_, v_c_3990_);
lean_dec(v___x_3985_);
lean_dec_ref(v_fst_3984_);
lean_dec(v___x_3983_);
lean_dec(v_upperBound_3982_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(lean_object* v_lsize_3992_, lean_object* v_rsize_3993_, lean_object* v_histogram_3994_, lean_object* v_index_3995_, lean_object* v_val_3996_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_histogram_3994_, v_index_3995_, v_val_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___boxed(lean_object* v_lsize_3998_, lean_object* v_rsize_3999_, lean_object* v_histogram_4000_, lean_object* v_index_4001_, lean_object* v_val_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(v_lsize_3998_, v_rsize_3999_, v_histogram_4000_, v_index_4001_, v_val_4002_);
lean_dec(v_rsize_3999_);
lean_dec(v_lsize_3998_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(lean_object* v_upperBound_4004_, lean_object* v_fst_4005_, lean_object* v___x_4006_, lean_object* v_fst_4007_, lean_object* v_inst_4008_, lean_object* v_R_4009_, lean_object* v_a_4010_, lean_object* v_b_4011_, lean_object* v_c_4012_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_4004_, v_fst_4005_, v___x_4006_, v_fst_4007_, v_a_4010_, v_b_4011_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___boxed(lean_object* v_upperBound_4014_, lean_object* v_fst_4015_, lean_object* v___x_4016_, lean_object* v_fst_4017_, lean_object* v_inst_4018_, lean_object* v_R_4019_, lean_object* v_a_4020_, lean_object* v_b_4021_, lean_object* v_c_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(v_upperBound_4014_, v_fst_4015_, v___x_4016_, v_fst_4017_, v_inst_4018_, v_R_4019_, v_a_4020_, v_b_4021_, v_c_4022_);
lean_dec_ref(v_fst_4017_);
lean_dec(v___x_4016_);
lean_dec_ref(v_fst_4015_);
lean_dec(v_upperBound_4014_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_4024_, lean_object* v_msg_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_4025_, v___y_4026_, v___y_4027_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_4030_, lean_object* v_msg_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_4030_, v_msg_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(lean_object* v_00_u03b2_4036_, lean_object* v_m_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_4037_, v_a_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b2_4040_, lean_object* v_m_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(v_00_u03b2_4040_, v_m_4041_, v_a_4042_);
lean_dec_ref(v_a_4042_);
lean_dec_ref(v_m_4041_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24(lean_object* v_00_u03b2_4044_, lean_object* v_m_4045_, lean_object* v_a_4046_, lean_object* v_b_4047_){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_m_4045_, v_a_4046_, v_b_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_4049_, lean_object* v_macroStack_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_4049_, v_macroStack_4050_, v___y_4052_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4055_, lean_object* v_macroStack_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4055_, v_macroStack_4056_, v___y_4057_, v___y_4058_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29(lean_object* v_inst_4061_, lean_object* v_R_4062_, lean_object* v_a_4063_, lean_object* v_b_4064_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v_a_4063_, v_b_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(lean_object* v_00_u03b2_4066_, lean_object* v_a_4067_, lean_object* v_x_4068_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_4067_, v_x_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___boxed(lean_object* v_00_u03b2_4070_, lean_object* v_a_4071_, lean_object* v_x_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(v_00_u03b2_4070_, v_a_4071_, v_x_4072_);
lean_dec(v_x_4072_);
lean_dec_ref(v_a_4071_);
return v_res_4073_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(lean_object* v_00_u03b2_4074_, lean_object* v_a_4075_, lean_object* v_x_4076_){
_start:
{
uint8_t v___x_4077_; 
v___x_4077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_4075_, v_x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___boxed(lean_object* v_00_u03b2_4078_, lean_object* v_a_4079_, lean_object* v_x_4080_){
_start:
{
uint8_t v_res_4081_; lean_object* v_r_4082_; 
v_res_4081_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(v_00_u03b2_4078_, v_a_4079_, v_x_4080_);
lean_dec(v_x_4080_);
lean_dec_ref(v_a_4079_);
v_r_4082_ = lean_box(v_res_4081_);
return v_r_4082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38(lean_object* v_00_u03b2_4083_, lean_object* v_data_4084_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_data_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39(lean_object* v_00_u03b2_4086_, lean_object* v_a_4087_, lean_object* v_b_4088_, lean_object* v_x_4089_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_4087_, v_b_4088_, v_x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44(lean_object* v_00_u03b2_4091_, lean_object* v_i_4092_, lean_object* v_source_4093_, lean_object* v_target_4094_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v_i_4092_, v_source_4093_, v_target_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4096_, lean_object* v_x_4097_, lean_object* v_x_4098_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_x_4097_, v_x_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4108_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4109_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
v___x_4110_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4111_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4112_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4108_, v___x_4109_, v___x_4110_, v___x_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4141_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4142_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4143_ = l_Lean_addBuiltinDeclarationRanges(v___x_4141_, v___x_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4146_){
_start:
{
lean_object* v_doc_4148_; lean_object* v___x_4149_; 
v_doc_4148_ = lean_ctor_get(v___y_4146_, 1);
lean_inc_ref(v_doc_4148_);
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v_doc_4148_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4150_);
lean_dec_ref(v___y_4150_);
return v_res_4152_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4153_, lean_object* v_a_4154_, uint8_t v_b_4155_){
_start:
{
lean_object* v_str_4156_; lean_object* v_startInclusive_4157_; lean_object* v_endExclusive_4158_; lean_object* v___x_4159_; uint8_t v___x_4160_; 
v_str_4156_ = lean_ctor_get(v_s_4153_, 0);
v_startInclusive_4157_ = lean_ctor_get(v_s_4153_, 1);
v_endExclusive_4158_ = lean_ctor_get(v_s_4153_, 2);
v___x_4159_ = lean_nat_sub(v_endExclusive_4158_, v_startInclusive_4157_);
v___x_4160_ = lean_nat_dec_eq(v_a_4154_, v___x_4159_);
lean_dec(v___x_4159_);
if (v___x_4160_ == 0)
{
lean_object* v___x_4161_; uint32_t v___x_4162_; uint32_t v___x_4163_; uint8_t v___x_4164_; 
v___x_4161_ = lean_nat_add(v_startInclusive_4157_, v_a_4154_);
lean_dec(v_a_4154_);
v___x_4162_ = lean_string_utf8_get_fast(v_str_4156_, v___x_4161_);
v___x_4163_ = 10;
v___x_4164_ = lean_uint32_dec_eq(v___x_4162_, v___x_4163_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; lean_object* v___x_4166_; 
v___x_4165_ = lean_string_utf8_next_fast(v_str_4156_, v___x_4161_);
lean_dec(v___x_4161_);
v___x_4166_ = lean_nat_sub(v___x_4165_, v_startInclusive_4157_);
v_a_4154_ = v___x_4166_;
v_b_4155_ = v___x_4164_;
goto _start;
}
else
{
lean_dec(v___x_4161_);
return v___x_4164_;
}
}
else
{
lean_dec(v_a_4154_);
return v_b_4155_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4168_, lean_object* v_a_4169_, lean_object* v_b_4170_){
_start:
{
uint8_t v_b_boxed_4171_; uint8_t v_res_4172_; lean_object* v_r_4173_; 
v_b_boxed_4171_ = lean_unbox(v_b_4170_);
v_res_4172_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4168_, v_a_4169_, v_b_boxed_4171_);
lean_dec_ref(v_s_4168_);
v_r_4173_ = lean_box(v_res_4172_);
return v_r_4173_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4174_){
_start:
{
lean_object* v_searcher_4175_; uint8_t v___x_4176_; uint8_t v___x_4177_; 
v_searcher_4175_ = lean_unsigned_to_nat(0u);
v___x_4176_ = 0;
v___x_4177_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4174_, v_searcher_4175_, v___x_4176_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4178_){
_start:
{
uint8_t v_res_4179_; lean_object* v_r_4180_; 
v_res_4179_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4178_);
lean_dec_ref(v_s_4178_);
v_r_4180_ = lean_box(v_res_4179_);
return v_r_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4192_, lean_object* v_fst_4193_, uint8_t v___x_4194_, lean_object* v_a_4195_, lean_object* v___x_4196_, lean_object* v___x_4197_, lean_object* v___x_4198_, lean_object* v___x_4199_, lean_object* v___x_4200_, lean_object* v___x_4201_, lean_object* v___x_4202_, lean_object* v___x_4203_, lean_object* v_snd_4204_, lean_object* v___x_4205_){
_start:
{
if (lean_obj_tag(v___x_4192_) == 1)
{
lean_object* v_val_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4270_; 
v_val_4207_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4209_ = v___x_4192_;
v_isShared_4210_ = v_isSharedCheck_4270_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_val_4207_);
lean_dec(v___x_4192_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4270_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4211_ = lean_unsigned_to_nat(0u);
v___x_4212_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4213_ = l_Lean_Syntax_setArg(v_fst_4193_, v___x_4211_, v___x_4212_);
v___x_4214_ = l_Lean_Syntax_getPos_x3f(v___x_4213_, v___x_4194_);
lean_dec(v___x_4213_);
if (lean_obj_tag(v___x_4214_) == 1)
{
lean_object* v_val_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4266_; 
lean_dec_ref(v___x_4205_);
v_val_4215_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4217_ = v___x_4214_;
v_isShared_4218_ = v_isSharedCheck_4266_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_val_4215_);
lean_dec(v___x_4214_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4266_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___y_4220_; lean_object* v___x_4246_; uint8_t v___y_4253_; lean_object* v___x_4258_; uint8_t v___x_4259_; 
v___x_4246_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4204_);
v___x_4258_ = lean_string_utf8_byte_size(v___x_4246_);
v___x_4259_ = lean_nat_dec_eq(v___x_4258_, v___x_4211_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v___x_4260_ = lean_string_length(v___x_4246_);
v___x_4261_ = lean_unsigned_to_nat(93u);
v___x_4262_ = lean_nat_dec_le(v___x_4260_, v___x_4261_);
if (v___x_4262_ == 0)
{
v___y_4253_ = v___x_4262_;
goto v___jp_4252_;
}
else
{
lean_object* v___x_4263_; uint8_t v___x_4264_; 
lean_inc_ref(v___x_4246_);
v___x_4263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4246_);
lean_ctor_set(v___x_4263_, 1, v___x_4211_);
lean_ctor_set(v___x_4263_, 2, v___x_4258_);
v___x_4264_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4263_);
lean_dec_ref_known(v___x_4263_, 3);
if (v___x_4264_ == 0)
{
v___y_4253_ = v___x_4262_;
goto v___jp_4252_;
}
else
{
goto v___jp_4247_;
}
}
}
else
{
lean_object* v___x_4265_; 
lean_dec_ref(v___x_4246_);
v___x_4265_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_4220_ = v___x_4265_;
goto v___jp_4219_;
}
v___jp_4219_:
{
lean_object* v_toEditableDocumentCore_4221_; lean_object* v_meta_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4242_; 
v_toEditableDocumentCore_4221_ = lean_ctor_get(v_a_4195_, 0);
lean_inc_ref(v_toEditableDocumentCore_4221_);
v_meta_4222_ = lean_ctor_get(v_toEditableDocumentCore_4221_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_toEditableDocumentCore_4221_);
if (v_isSharedCheck_4242_ == 0)
{
lean_object* v_unused_4243_; lean_object* v_unused_4244_; lean_object* v_unused_4245_; 
v_unused_4243_ = lean_ctor_get(v_toEditableDocumentCore_4221_, 3);
lean_dec(v_unused_4243_);
v_unused_4244_ = lean_ctor_get(v_toEditableDocumentCore_4221_, 2);
lean_dec(v_unused_4244_);
v_unused_4245_ = lean_ctor_get(v_toEditableDocumentCore_4221_, 1);
lean_dec(v_unused_4245_);
v___x_4224_ = v_toEditableDocumentCore_4221_;
v_isShared_4225_ = v_isSharedCheck_4242_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_meta_4222_);
lean_dec(v_toEditableDocumentCore_4221_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4242_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v_text_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4232_; 
v_text_4226_ = lean_ctor_get(v_meta_4222_, 3);
lean_inc_ref(v_text_4226_);
lean_dec_ref(v_meta_4222_);
v___x_4227_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4195_);
v___x_4228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4228_, 0, v_val_4207_);
lean_ctor_set(v___x_4228_, 1, v_val_4215_);
v___x_4229_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4226_, v___x_4228_);
v___x_4230_ = lean_box(0);
lean_inc(v___x_4196_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 3, v___x_4196_);
lean_ctor_set(v___x_4224_, 2, v___x_4230_);
lean_ctor_set(v___x_4224_, 1, v___y_4220_);
lean_ctor_set(v___x_4224_, 0, v___x_4229_);
v___x_4232_ = v___x_4224_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4229_);
lean_ctor_set(v_reuseFailAlloc_4241_, 1, v___y_4220_);
lean_ctor_set(v_reuseFailAlloc_4241_, 2, v___x_4230_);
lean_ctor_set(v_reuseFailAlloc_4241_, 3, v___x_4196_);
v___x_4232_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
lean_object* v___x_4233_; lean_object* v___x_4235_; 
v___x_4233_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4227_, v___x_4232_);
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 0, v___x_4233_);
v___x_4235_ = v___x_4217_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4233_);
v___x_4235_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
lean_object* v___x_4236_; lean_object* v___x_4238_; 
lean_inc(v___x_4196_);
v___x_4236_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4196_);
lean_ctor_set(v___x_4236_, 1, v___x_4196_);
lean_ctor_set(v___x_4236_, 2, v___x_4197_);
lean_ctor_set(v___x_4236_, 3, v___x_4198_);
lean_ctor_set(v___x_4236_, 4, v___x_4199_);
lean_ctor_set(v___x_4236_, 5, v___x_4200_);
lean_ctor_set(v___x_4236_, 6, v___x_4201_);
lean_ctor_set(v___x_4236_, 7, v___x_4235_);
lean_ctor_set(v___x_4236_, 8, v___x_4202_);
lean_ctor_set(v___x_4236_, 9, v___x_4203_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set_tag(v___x_4209_, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4236_);
v___x_4238_ = v___x_4209_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4236_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
}
v___jp_4247_:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4248_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4249_ = lean_string_append(v___x_4248_, v___x_4246_);
lean_dec_ref(v___x_4246_);
v___x_4250_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4251_ = lean_string_append(v___x_4249_, v___x_4250_);
v___y_4220_ = v___x_4251_;
goto v___jp_4219_;
}
v___jp_4252_:
{
if (v___y_4253_ == 0)
{
goto v___jp_4247_;
}
else
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4254_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4255_ = lean_string_append(v___x_4254_, v___x_4246_);
lean_dec_ref(v___x_4246_);
v___x_4256_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4257_ = lean_string_append(v___x_4255_, v___x_4256_);
v___y_4220_ = v___x_4257_;
goto v___jp_4219_;
}
}
}
}
else
{
lean_object* v___x_4268_; 
lean_dec(v___x_4214_);
lean_dec(v_val_4207_);
lean_dec_ref(v_snd_4204_);
lean_dec(v___x_4203_);
lean_dec(v___x_4202_);
lean_dec(v___x_4201_);
lean_dec(v___x_4200_);
lean_dec(v___x_4199_);
lean_dec(v___x_4198_);
lean_dec_ref(v___x_4197_);
lean_dec(v___x_4196_);
lean_dec_ref(v_a_4195_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set_tag(v___x_4209_, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4205_);
v___x_4268_ = v___x_4209_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4205_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
else
{
lean_object* v___x_4271_; 
lean_dec_ref(v_snd_4204_);
lean_dec(v___x_4203_);
lean_dec(v___x_4202_);
lean_dec(v___x_4201_);
lean_dec(v___x_4200_);
lean_dec(v___x_4199_);
lean_dec(v___x_4198_);
lean_dec_ref(v___x_4197_);
lean_dec(v___x_4196_);
lean_dec_ref(v_a_4195_);
lean_dec(v_fst_4193_);
lean_dec(v___x_4192_);
v___x_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4205_);
return v___x_4271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4272_, lean_object* v_fst_4273_, lean_object* v___x_4274_, lean_object* v_a_4275_, lean_object* v___x_4276_, lean_object* v___x_4277_, lean_object* v___x_4278_, lean_object* v___x_4279_, lean_object* v___x_4280_, lean_object* v___x_4281_, lean_object* v___x_4282_, lean_object* v___x_4283_, lean_object* v_snd_4284_, lean_object* v___x_4285_, lean_object* v___y_4286_){
_start:
{
uint8_t v___x_4549__boxed_4287_; lean_object* v_res_4288_; 
v___x_4549__boxed_4287_ = lean_unbox(v___x_4274_);
v_res_4288_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4272_, v_fst_4273_, v___x_4549__boxed_4287_, v_a_4275_, v___x_4276_, v___x_4277_, v___x_4278_, v___x_4279_, v___x_4280_, v___x_4281_, v___x_4282_, v___x_4283_, v_snd_4284_, v___x_4285_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4292_, size_t v_sz_4293_, size_t v_i_4294_, lean_object* v_b_4295_){
_start:
{
lean_object* v_a_4297_; uint8_t v___x_4301_; 
v___x_4301_ = lean_usize_dec_lt(v_i_4294_, v_sz_4293_);
if (v___x_4301_ == 0)
{
lean_inc_ref(v_b_4295_);
return v_b_4295_;
}
else
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v_a_4304_; 
v___x_4302_ = lean_box(0);
v___x_4303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4304_ = lean_array_uget(v_as_4292_, v_i_4294_);
if (lean_obj_tag(v_a_4304_) == 1)
{
lean_object* v_i_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4339_; 
v_i_4305_ = lean_ctor_get(v_a_4304_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_a_4304_);
if (v_isSharedCheck_4339_ == 0)
{
lean_object* v_unused_4340_; 
v_unused_4340_ = lean_ctor_get(v_a_4304_, 1);
lean_dec(v_unused_4340_);
v___x_4307_ = v_a_4304_;
v_isShared_4308_ = v_isSharedCheck_4339_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_i_4305_);
lean_dec(v_a_4304_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4339_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
if (lean_obj_tag(v_i_4305_) == 10)
{
lean_object* v_i_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4338_; 
v_i_4309_ = lean_ctor_get(v_i_4305_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v_i_4305_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4311_ = v_i_4305_;
v_isShared_4312_ = v_isSharedCheck_4338_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_i_4309_);
lean_dec(v_i_4305_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4338_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v_stx_4313_; lean_object* v_value_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4337_; 
v_stx_4313_ = lean_ctor_get(v_i_4309_, 0);
v_value_4314_ = lean_ctor_get(v_i_4309_, 1);
v_isSharedCheck_4337_ = !lean_is_exclusive(v_i_4309_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4316_ = v_i_4309_;
v_isShared_4317_ = v_isSharedCheck_4337_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_value_4314_);
lean_inc(v_stx_4313_);
lean_dec(v_i_4309_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4337_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4318_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4319_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4314_, v___x_4318_);
lean_dec(v_value_4314_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_del_object(v___x_4316_);
lean_dec(v_stx_4313_);
lean_del_object(v___x_4311_);
lean_del_object(v___x_4307_);
v_a_4297_ = v___x_4303_;
goto v___jp_4296_;
}
else
{
lean_object* v_val_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4336_; 
v_val_4320_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4322_ = v___x_4319_;
v_isShared_4323_ = v_isSharedCheck_4336_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_val_4320_);
lean_dec(v___x_4319_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4336_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 1, v_val_4320_);
v___x_4325_ = v___x_4316_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_stx_4313_);
lean_ctor_set(v_reuseFailAlloc_4335_, 1, v_val_4320_);
v___x_4325_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
lean_object* v___x_4327_; 
if (v_isShared_4323_ == 0)
{
lean_ctor_set(v___x_4322_, 0, v___x_4325_);
v___x_4327_ = v___x_4322_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4325_);
v___x_4327_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
lean_object* v___x_4329_; 
if (v_isShared_4312_ == 0)
{
lean_ctor_set_tag(v___x_4311_, 1);
lean_ctor_set(v___x_4311_, 0, v___x_4327_);
v___x_4329_ = v___x_4311_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4327_);
v___x_4329_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4331_; 
if (v_isShared_4308_ == 0)
{
lean_ctor_set_tag(v___x_4307_, 0);
lean_ctor_set(v___x_4307_, 1, v___x_4302_);
lean_ctor_set(v___x_4307_, 0, v___x_4329_);
v___x_4331_ = v___x_4307_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
lean_ctor_set(v_reuseFailAlloc_4332_, 1, v___x_4302_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
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
lean_del_object(v___x_4307_);
lean_dec_ref(v_i_4305_);
v_a_4297_ = v___x_4303_;
goto v___jp_4296_;
}
}
}
else
{
lean_dec(v_a_4304_);
v_a_4297_ = v___x_4303_;
goto v___jp_4296_;
}
}
v___jp_4296_:
{
size_t v___x_4298_; size_t v___x_4299_; 
v___x_4298_ = ((size_t)1ULL);
v___x_4299_ = lean_usize_add(v_i_4294_, v___x_4298_);
v_i_4294_ = v___x_4299_;
v_b_4295_ = v_a_4297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4341_, lean_object* v_sz_4342_, lean_object* v_i_4343_, lean_object* v_b_4344_){
_start:
{
size_t v_sz_boxed_4345_; size_t v_i_boxed_4346_; lean_object* v_res_4347_; 
v_sz_boxed_4345_ = lean_unbox_usize(v_sz_4342_);
lean_dec(v_sz_4342_);
v_i_boxed_4346_ = lean_unbox_usize(v_i_4343_);
lean_dec(v_i_4343_);
v_res_4347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4341_, v_sz_boxed_4345_, v_i_boxed_4346_, v_b_4344_);
lean_dec_ref(v_b_4344_);
lean_dec_ref(v_as_4341_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4348_, size_t v_sz_4349_, size_t v_i_4350_, lean_object* v_b_4351_){
_start:
{
lean_object* v_a_4353_; uint8_t v___x_4357_; 
v___x_4357_ = lean_usize_dec_lt(v_i_4350_, v_sz_4349_);
if (v___x_4357_ == 0)
{
lean_inc_ref(v_b_4351_);
return v_b_4351_;
}
else
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v_a_4360_; 
v___x_4358_ = lean_box(0);
v___x_4359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4360_ = lean_array_uget(v_as_4348_, v_i_4350_);
if (lean_obj_tag(v_a_4360_) == 1)
{
lean_object* v_i_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4395_; 
v_i_4361_ = lean_ctor_get(v_a_4360_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v_a_4360_);
if (v_isSharedCheck_4395_ == 0)
{
lean_object* v_unused_4396_; 
v_unused_4396_ = lean_ctor_get(v_a_4360_, 1);
lean_dec(v_unused_4396_);
v___x_4363_ = v_a_4360_;
v_isShared_4364_ = v_isSharedCheck_4395_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_i_4361_);
lean_dec(v_a_4360_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4395_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
if (lean_obj_tag(v_i_4361_) == 10)
{
lean_object* v_i_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4394_; 
v_i_4365_ = lean_ctor_get(v_i_4361_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v_i_4361_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4367_ = v_i_4361_;
v_isShared_4368_ = v_isSharedCheck_4394_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_i_4365_);
lean_dec(v_i_4361_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4394_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v_stx_4369_; lean_object* v_value_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4393_; 
v_stx_4369_ = lean_ctor_get(v_i_4365_, 0);
v_value_4370_ = lean_ctor_get(v_i_4365_, 1);
v_isSharedCheck_4393_ = !lean_is_exclusive(v_i_4365_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4372_ = v_i_4365_;
v_isShared_4373_ = v_isSharedCheck_4393_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_value_4370_);
lean_inc(v_stx_4369_);
lean_dec(v_i_4365_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4393_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4374_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4375_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4370_, v___x_4374_);
lean_dec(v_value_4370_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_del_object(v___x_4372_);
lean_dec(v_stx_4369_);
lean_del_object(v___x_4367_);
lean_del_object(v___x_4363_);
v_a_4353_ = v___x_4359_;
goto v___jp_4352_;
}
else
{
lean_object* v_val_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4392_; 
v_val_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4392_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_val_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4392_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 1, v_val_4376_);
v___x_4381_ = v___x_4372_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_stx_4369_);
lean_ctor_set(v_reuseFailAlloc_4391_, 1, v_val_4376_);
v___x_4381_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
lean_object* v___x_4383_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4381_);
v___x_4383_ = v___x_4378_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4381_);
v___x_4383_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
lean_object* v___x_4385_; 
if (v_isShared_4368_ == 0)
{
lean_ctor_set_tag(v___x_4367_, 1);
lean_ctor_set(v___x_4367_, 0, v___x_4383_);
v___x_4385_ = v___x_4367_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
lean_object* v___x_4387_; 
if (v_isShared_4364_ == 0)
{
lean_ctor_set_tag(v___x_4363_, 0);
lean_ctor_set(v___x_4363_, 1, v___x_4358_);
lean_ctor_set(v___x_4363_, 0, v___x_4385_);
v___x_4387_ = v___x_4363_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4385_);
lean_ctor_set(v_reuseFailAlloc_4388_, 1, v___x_4358_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
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
lean_del_object(v___x_4363_);
lean_dec_ref(v_i_4361_);
v_a_4353_ = v___x_4359_;
goto v___jp_4352_;
}
}
}
else
{
lean_dec(v_a_4360_);
v_a_4353_ = v___x_4359_;
goto v___jp_4352_;
}
}
v___jp_4352_:
{
size_t v___x_4354_; size_t v___x_4355_; lean_object* v___x_4356_; 
v___x_4354_ = ((size_t)1ULL);
v___x_4355_ = lean_usize_add(v_i_4350_, v___x_4354_);
v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4348_, v_sz_4349_, v___x_4355_, v_a_4353_);
return v___x_4356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4397_, lean_object* v_sz_4398_, lean_object* v_i_4399_, lean_object* v_b_4400_){
_start:
{
size_t v_sz_boxed_4401_; size_t v_i_boxed_4402_; lean_object* v_res_4403_; 
v_sz_boxed_4401_ = lean_unbox_usize(v_sz_4398_);
lean_dec(v_sz_4398_);
v_i_boxed_4402_ = lean_unbox_usize(v_i_4399_);
lean_dec(v_i_4399_);
v_res_4403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4397_, v_sz_boxed_4401_, v_i_boxed_4402_, v_b_4400_);
lean_dec_ref(v_b_4400_);
lean_dec_ref(v_as_4397_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4404_){
_start:
{
if (lean_obj_tag(v_x_4404_) == 0)
{
lean_object* v_cs_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; size_t v_sz_4408_; size_t v___x_4409_; lean_object* v___x_4410_; lean_object* v_fst_4411_; 
v_cs_4405_ = lean_ctor_get(v_x_4404_, 0);
v___x_4406_ = lean_box(0);
v___x_4407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4408_ = lean_array_size(v_cs_4405_);
v___x_4409_ = ((size_t)0ULL);
v___x_4410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4405_, v_sz_4408_, v___x_4409_, v___x_4407_);
v_fst_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_fst_4411_);
lean_dec_ref(v___x_4410_);
if (lean_obj_tag(v_fst_4411_) == 0)
{
return v___x_4406_;
}
else
{
lean_object* v_val_4412_; 
v_val_4412_ = lean_ctor_get(v_fst_4411_, 0);
lean_inc(v_val_4412_);
lean_dec_ref_known(v_fst_4411_, 1);
return v_val_4412_;
}
}
else
{
lean_object* v_vs_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; size_t v_sz_4416_; size_t v___x_4417_; lean_object* v___x_4418_; lean_object* v_fst_4419_; 
v_vs_4413_ = lean_ctor_get(v_x_4404_, 0);
v___x_4414_ = lean_box(0);
v___x_4415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4416_ = lean_array_size(v_vs_4413_);
v___x_4417_ = ((size_t)0ULL);
v___x_4418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4413_, v_sz_4416_, v___x_4417_, v___x_4415_);
v_fst_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_fst_4419_);
lean_dec_ref(v___x_4418_);
if (lean_obj_tag(v_fst_4419_) == 0)
{
return v___x_4414_;
}
else
{
lean_object* v_val_4420_; 
v_val_4420_ = lean_ctor_get(v_fst_4419_, 0);
lean_inc(v_val_4420_);
lean_dec_ref_known(v_fst_4419_, 1);
return v_val_4420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4421_, size_t v_sz_4422_, size_t v_i_4423_, lean_object* v_b_4424_){
_start:
{
uint8_t v___x_4425_; 
v___x_4425_ = lean_usize_dec_lt(v_i_4423_, v_sz_4422_);
if (v___x_4425_ == 0)
{
lean_inc_ref(v_b_4424_);
return v_b_4424_;
}
else
{
lean_object* v___x_4426_; lean_object* v_a_4427_; lean_object* v___x_4428_; 
v___x_4426_ = lean_box(0);
v_a_4427_ = lean_array_uget_borrowed(v_as_4421_, v_i_4423_);
v___x_4428_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4427_);
if (lean_obj_tag(v___x_4428_) == 1)
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
v___x_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
lean_ctor_set(v___x_4430_, 1, v___x_4426_);
return v___x_4430_;
}
else
{
lean_object* v___x_4431_; size_t v___x_4432_; size_t v___x_4433_; 
lean_dec(v___x_4428_);
v___x_4431_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4432_ = ((size_t)1ULL);
v___x_4433_ = lean_usize_add(v_i_4423_, v___x_4432_);
v_i_4423_ = v___x_4433_;
v_b_4424_ = v___x_4431_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4435_, lean_object* v_sz_4436_, lean_object* v_i_4437_, lean_object* v_b_4438_){
_start:
{
size_t v_sz_boxed_4439_; size_t v_i_boxed_4440_; lean_object* v_res_4441_; 
v_sz_boxed_4439_ = lean_unbox_usize(v_sz_4436_);
lean_dec(v_sz_4436_);
v_i_boxed_4440_ = lean_unbox_usize(v_i_4437_);
lean_dec(v_i_4437_);
v_res_4441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4435_, v_sz_boxed_4439_, v_i_boxed_4440_, v_b_4438_);
lean_dec_ref(v_b_4438_);
lean_dec_ref(v_as_4435_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4442_);
lean_dec_ref(v_x_4442_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4444_){
_start:
{
lean_object* v_root_4445_; lean_object* v_tail_4446_; lean_object* v___x_4447_; 
v_root_4445_ = lean_ctor_get(v_t_4444_, 0);
v_tail_4446_ = lean_ctor_get(v_t_4444_, 1);
v___x_4447_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4445_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v___x_4448_; size_t v_sz_4449_; size_t v___x_4450_; lean_object* v___x_4451_; lean_object* v_fst_4452_; 
v___x_4448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4449_ = lean_array_size(v_tail_4446_);
v___x_4450_ = ((size_t)0ULL);
v___x_4451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4446_, v_sz_4449_, v___x_4450_, v___x_4448_);
v_fst_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_fst_4452_);
lean_dec_ref(v___x_4451_);
if (lean_obj_tag(v_fst_4452_) == 0)
{
return v___x_4447_;
}
else
{
lean_object* v_val_4453_; 
v_val_4453_ = lean_ctor_get(v_fst_4452_, 0);
lean_inc(v_val_4453_);
lean_dec_ref_known(v_fst_4452_, 1);
return v_val_4453_;
}
}
else
{
return v___x_4447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4454_);
lean_dec_ref(v_t_4454_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4470_, lean_object* v_a_4471_){
_start:
{
if (lean_obj_tag(v_node_4470_) == 1)
{
lean_object* v_children_4473_; lean_object* v_res_4474_; 
v_children_4473_ = lean_ctor_get(v_node_4470_, 1);
v_res_4474_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4473_);
if (lean_obj_tag(v_res_4474_) == 1)
{
lean_object* v_val_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4512_; 
v_val_4475_ = lean_ctor_get(v_res_4474_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v_res_4474_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4477_ = v_res_4474_;
v_isShared_4478_ = v_isSharedCheck_4512_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_val_4475_);
lean_dec(v_res_4474_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4512_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v_fst_4479_; lean_object* v_snd_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4511_; 
v_fst_4479_ = lean_ctor_get(v_val_4475_, 0);
v_snd_4480_ = lean_ctor_get(v_val_4475_, 1);
v_isSharedCheck_4511_ = !lean_is_exclusive(v_val_4475_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4482_ = v_val_4475_;
v_isShared_4483_ = v_isSharedCheck_4511_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_snd_4480_);
lean_inc(v_fst_4479_);
lean_dec(v_val_4475_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4511_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4484_; lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4510_; 
v___x_4484_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4471_);
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4487_ = v___x_4484_;
v_isShared_4488_ = v_isSharedCheck_4510_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4510_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; uint8_t v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___y_4497_; lean_object* v___x_4499_; 
v___x_4489_ = lean_box(0);
v___x_4490_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4491_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4492_ = 1;
v___x_4493_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4494_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4495_ = l_Lean_Syntax_getPos_x3f(v_fst_4479_, v___x_4492_);
v___x_4496_ = lean_box(v___x_4492_);
v___y_4497_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4497_, 0, v___x_4495_);
lean_closure_set(v___y_4497_, 1, v_fst_4479_);
lean_closure_set(v___y_4497_, 2, v___x_4496_);
lean_closure_set(v___y_4497_, 3, v_a_4485_);
lean_closure_set(v___y_4497_, 4, v___x_4489_);
lean_closure_set(v___y_4497_, 5, v___x_4490_);
lean_closure_set(v___y_4497_, 6, v___x_4491_);
lean_closure_set(v___y_4497_, 7, v___x_4489_);
lean_closure_set(v___y_4497_, 8, v___x_4493_);
lean_closure_set(v___y_4497_, 9, v___x_4489_);
lean_closure_set(v___y_4497_, 10, v___x_4489_);
lean_closure_set(v___y_4497_, 11, v___x_4489_);
lean_closure_set(v___y_4497_, 12, v_snd_4480_);
lean_closure_set(v___y_4497_, 13, v___x_4494_);
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 0, v___y_4497_);
v___x_4499_ = v___x_4477_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___y_4497_);
v___x_4499_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
lean_object* v___x_4501_; 
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 1, v___x_4499_);
lean_ctor_set(v___x_4482_, 0, v___x_4494_);
v___x_4501_ = v___x_4482_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4494_);
lean_ctor_set(v_reuseFailAlloc_4508_, 1, v___x_4499_);
v___x_4501_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4506_; 
v___x_4502_ = lean_unsigned_to_nat(1u);
v___x_4503_ = lean_mk_empty_array_with_capacity(v___x_4502_);
v___x_4504_ = lean_array_push(v___x_4503_, v___x_4501_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 0, v___x_4504_);
v___x_4506_ = v___x_4487_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
lean_dec(v_res_4474_);
v___x_4513_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4513_);
return v___x_4514_;
}
}
else
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
return v___x_4516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4517_, v_a_4518_);
lean_dec_ref(v_a_4518_);
lean_dec_ref(v_node_4517_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4521_, lean_object* v_x_4522_, lean_object* v_x_4523_, lean_object* v_node_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v___x_4527_; 
v___x_4527_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4524_, v_a_4525_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4528_, lean_object* v_x_4529_, lean_object* v_x_4530_, lean_object* v_node_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4528_, v_x_4529_, v_x_4530_, v_node_4531_, v_a_4532_);
lean_dec_ref(v_a_4532_);
lean_dec_ref(v_node_4531_);
lean_dec_ref(v_x_4530_);
lean_dec_ref(v_x_4529_);
lean_dec_ref(v_x_4528_);
return v_res_4534_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4535_, lean_object* v_inst_4536_, lean_object* v_R_4537_, lean_object* v_a_4538_, uint8_t v_b_4539_, lean_object* v_c_4540_){
_start:
{
uint8_t v___x_4541_; 
v___x_4541_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4535_, v_a_4538_, v_b_4539_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4542_, lean_object* v_inst_4543_, lean_object* v_R_4544_, lean_object* v_a_4545_, lean_object* v_b_4546_, lean_object* v_c_4547_){
_start:
{
uint8_t v_b_boxed_4548_; uint8_t v_res_4549_; lean_object* v_r_4550_; 
v_b_boxed_4548_ = lean_unbox(v_b_4546_);
v_res_4549_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4542_, v_inst_4543_, v_R_4544_, v_a_4545_, v_b_boxed_4548_, v_c_4547_);
lean_dec_ref(v_s_4542_);
v_r_4550_ = lean_box(v_res_4549_);
return v_r_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_(){
_start:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4556_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_));
v___x_4557_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4558_ = l_Lean_CodeAction_insertBuiltin(v___x_4556_, v___x_4557_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365____boxed(lean_object* v_a_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_();
return v_res_4560_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4562_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4563_ = lean_string_utf8_byte_size(v___x_4562_);
return v___x_4563_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; uint8_t v___x_4566_; 
v___x_4564_ = lean_unsigned_to_nat(0u);
v___x_4565_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4566_ = lean_nat_dec_eq(v___x_4565_, v___x_4564_);
return v___x_4566_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4567_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4568_ = lean_unsigned_to_nat(0u);
v___x_4569_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4569_);
lean_ctor_set(v___x_4570_, 1, v___x_4568_);
lean_ctor_set(v___x_4570_, 2, v___x_4567_);
return v___x_4570_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4(void){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4571_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4572_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4571_);
return v___x_4572_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4573_ = lean_unsigned_to_nat(0u);
v___x_4574_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4);
v___x_4575_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4576_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4575_);
lean_ctor_set(v___x_4576_, 1, v___x_4574_);
lean_ctor_set(v___x_4576_, 2, v___x_4573_);
lean_ctor_set(v___x_4576_, 3, v___x_4573_);
return v___x_4576_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4577_){
_start:
{
lean_object* v___y_4579_; uint8_t v___x_4582_; 
v___x_4582_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
if (v___x_4582_ == 0)
{
lean_object* v___x_4583_; 
v___x_4583_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5);
v___y_4579_ = v___x_4583_;
goto v___jp_4578_;
}
else
{
lean_object* v___x_4584_; 
v___x_4584_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_4579_ = v___x_4584_;
goto v___jp_4578_;
}
v___jp_4578_:
{
uint8_t v___x_4580_; uint8_t v___x_4581_; 
v___x_4580_ = 0;
lean_inc(v___y_4579_);
v___x_4581_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4577_, v___y_4579_, v___x_4580_);
return v___x_4581_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4585_){
_start:
{
uint8_t v_res_4586_; lean_object* v_r_4587_; 
v_res_4586_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4585_);
lean_dec_ref(v_s_4585_);
v_r_4587_ = lean_box(v_res_4586_);
return v_r_4587_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4588_, lean_object* v_as_x27_4589_, uint8_t v_b_4590_){
_start:
{
if (lean_obj_tag(v_as_x27_4589_) == 0)
{
lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4592_ = lean_box(v_b_4590_);
v___x_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
return v___x_4593_;
}
else
{
lean_object* v_head_4594_; uint8_t v_isSilent_4595_; 
v_head_4594_ = lean_ctor_get(v_as_x27_4589_, 0);
v_isSilent_4595_ = lean_ctor_get_uint8(v_head_4594_, sizeof(void*)*5 + 2);
if (v_isSilent_4595_ == 0)
{
lean_object* v_tail_4596_; lean_object* v_data_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; uint8_t v___x_4602_; 
v_tail_4596_ = lean_ctor_get(v_as_x27_4589_, 1);
v_data_4597_ = lean_ctor_get(v_head_4594_, 4);
lean_inc(v_data_4597_);
v___x_4598_ = l_Lean_MessageData_toString(v_data_4597_);
v___x_4599_ = lean_unsigned_to_nat(0u);
v___x_4600_ = lean_string_utf8_byte_size(v___x_4598_);
v___x_4601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4598_);
lean_ctor_set(v___x_4601_, 1, v___x_4599_);
lean_ctor_set(v___x_4601_, 2, v___x_4600_);
v___x_4602_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4601_);
lean_dec_ref_known(v___x_4601_, 3);
if (v___x_4602_ == 0)
{
v_as_x27_4589_ = v_tail_4596_;
goto _start;
}
else
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4604_ = lean_box(v_foundPanic_4588_);
v___x_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4604_);
return v___x_4605_;
}
}
else
{
lean_object* v_tail_4606_; 
v_tail_4606_ = lean_ctor_get(v_as_x27_4589_, 1);
v_as_x27_4589_ = v_tail_4606_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4608_, lean_object* v_as_x27_4609_, lean_object* v_b_4610_, lean_object* v___y_4611_){
_start:
{
uint8_t v_foundPanic_boxed_4612_; uint8_t v_b_boxed_4613_; lean_object* v_res_4614_; 
v_foundPanic_boxed_4612_ = lean_unbox(v_foundPanic_4608_);
v_b_boxed_4613_ = lean_unbox(v_b_4610_);
v_res_4614_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4612_, v_as_x27_4609_, v_b_boxed_4613_);
lean_dec(v_as_x27_4609_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4615_, uint8_t v_severity_4616_, uint8_t v_isSilent_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
lean_object* v___x_4621_; 
v___x_4621_ = l_Lean_Elab_Command_getRef___redArg(v___y_4618_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; lean_object* v___x_4623_; 
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
lean_inc(v_a_4622_);
lean_dec_ref_known(v___x_4621_, 1);
v___x_4623_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4622_, v_msgData_4615_, v_severity_4616_, v_isSilent_4617_, v___y_4618_, v___y_4619_);
lean_dec(v_a_4622_);
return v___x_4623_;
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_dec_ref(v_msgData_4615_);
v_a_4624_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4621_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4621_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4632_, lean_object* v_severity_4633_, lean_object* v_isSilent_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
uint8_t v_severity_boxed_4638_; uint8_t v_isSilent_boxed_4639_; lean_object* v_res_4640_; 
v_severity_boxed_4638_ = lean_unbox(v_severity_4633_);
v_isSilent_boxed_4639_ = lean_unbox(v_isSilent_4634_);
v_res_4640_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4632_, v_severity_boxed_4638_, v_isSilent_boxed_4639_, v___y_4635_, v___y_4636_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
uint8_t v___x_4645_; uint8_t v___x_4646_; lean_object* v___x_4647_; 
v___x_4645_ = 2;
v___x_4646_ = 0;
v___x_4647_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4641_, v___x_4645_, v___x_4646_, v___y_4642_, v___y_4643_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4648_, v___y_4649_, v___y_4650_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
return v_res_4652_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4660_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4661_ = l_Lean_MessageData_ofFormat(v___x_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v___x_4666_; uint8_t v_foundPanic_4667_; 
v___x_4666_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4662_);
v_foundPanic_4667_ = l_Lean_Syntax_isOfKind(v_x_4662_, v___x_4666_);
if (v_foundPanic_4667_ == 0)
{
lean_object* v___x_4668_; 
lean_dec(v_x_4662_);
v___x_4668_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4668_;
}
else
{
lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4669_ = lean_unsigned_to_nat(2u);
v___x_4670_ = l_Lean_Syntax_getArg(v_x_4662_, v___x_4669_);
lean_dec(v_x_4662_);
v___x_4671_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4670_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; uint8_t v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4730_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4672_);
lean_dec_ref_known(v___x_4671_, 1);
v___x_4673_ = 0;
v___x_4674_ = l_Lean_MessageLog_toList(v_a_4672_);
v___x_4675_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4667_, v___x_4674_, v___x_4673_);
lean_dec(v___x_4674_);
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4678_ = v___x_4675_;
v_isShared_4679_ = v_isSharedCheck_4730_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4675_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4730_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
uint8_t v___x_4680_; 
v___x_4680_ = lean_unbox(v_a_4676_);
lean_dec(v_a_4676_);
if (v___x_4680_ == 0)
{
lean_object* v___x_4681_; lean_object* v_env_4682_; lean_object* v_scopes_4683_; lean_object* v_usedQuotCtxts_4684_; lean_object* v_nextMacroScope_4685_; lean_object* v_maxRecDepth_4686_; lean_object* v_ngen_4687_; lean_object* v_auxDeclNGen_4688_; lean_object* v_infoState_4689_; lean_object* v_traceState_4690_; lean_object* v_snapshotTasks_4691_; lean_object* v_prevLinterStates_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4702_; 
lean_del_object(v___x_4678_);
v___x_4681_ = lean_st_ref_take(v_a_4664_);
v_env_4682_ = lean_ctor_get(v___x_4681_, 0);
v_scopes_4683_ = lean_ctor_get(v___x_4681_, 2);
v_usedQuotCtxts_4684_ = lean_ctor_get(v___x_4681_, 3);
v_nextMacroScope_4685_ = lean_ctor_get(v___x_4681_, 4);
v_maxRecDepth_4686_ = lean_ctor_get(v___x_4681_, 5);
v_ngen_4687_ = lean_ctor_get(v___x_4681_, 6);
v_auxDeclNGen_4688_ = lean_ctor_get(v___x_4681_, 7);
v_infoState_4689_ = lean_ctor_get(v___x_4681_, 8);
v_traceState_4690_ = lean_ctor_get(v___x_4681_, 9);
v_snapshotTasks_4691_ = lean_ctor_get(v___x_4681_, 10);
v_prevLinterStates_4692_ = lean_ctor_get(v___x_4681_, 11);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4702_ == 0)
{
lean_object* v_unused_4703_; 
v_unused_4703_ = lean_ctor_get(v___x_4681_, 1);
lean_dec(v_unused_4703_);
v___x_4694_ = v___x_4681_;
v_isShared_4695_ = v_isSharedCheck_4702_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_prevLinterStates_4692_);
lean_inc(v_snapshotTasks_4691_);
lean_inc(v_traceState_4690_);
lean_inc(v_infoState_4689_);
lean_inc(v_auxDeclNGen_4688_);
lean_inc(v_ngen_4687_);
lean_inc(v_maxRecDepth_4686_);
lean_inc(v_nextMacroScope_4685_);
lean_inc(v_usedQuotCtxts_4684_);
lean_inc(v_scopes_4683_);
lean_inc(v_env_4682_);
lean_dec(v___x_4681_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4702_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 1, v_a_4672_);
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_env_4682_);
lean_ctor_set(v_reuseFailAlloc_4701_, 1, v_a_4672_);
lean_ctor_set(v_reuseFailAlloc_4701_, 2, v_scopes_4683_);
lean_ctor_set(v_reuseFailAlloc_4701_, 3, v_usedQuotCtxts_4684_);
lean_ctor_set(v_reuseFailAlloc_4701_, 4, v_nextMacroScope_4685_);
lean_ctor_set(v_reuseFailAlloc_4701_, 5, v_maxRecDepth_4686_);
lean_ctor_set(v_reuseFailAlloc_4701_, 6, v_ngen_4687_);
lean_ctor_set(v_reuseFailAlloc_4701_, 7, v_auxDeclNGen_4688_);
lean_ctor_set(v_reuseFailAlloc_4701_, 8, v_infoState_4689_);
lean_ctor_set(v_reuseFailAlloc_4701_, 9, v_traceState_4690_);
lean_ctor_set(v_reuseFailAlloc_4701_, 10, v_snapshotTasks_4691_);
lean_ctor_set(v_reuseFailAlloc_4701_, 11, v_prevLinterStates_4692_);
v___x_4697_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v___x_4698_ = lean_st_ref_set(v_a_4664_, v___x_4697_);
v___x_4699_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4700_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4699_, v_a_4663_, v_a_4664_);
return v___x_4700_;
}
}
}
else
{
lean_object* v___x_4704_; lean_object* v_env_4705_; lean_object* v_scopes_4706_; lean_object* v_usedQuotCtxts_4707_; lean_object* v_nextMacroScope_4708_; lean_object* v_maxRecDepth_4709_; lean_object* v_ngen_4710_; lean_object* v_auxDeclNGen_4711_; lean_object* v_infoState_4712_; lean_object* v_traceState_4713_; lean_object* v_snapshotTasks_4714_; lean_object* v_prevLinterStates_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4728_; 
lean_dec(v_a_4672_);
v___x_4704_ = lean_st_ref_take(v_a_4664_);
v_env_4705_ = lean_ctor_get(v___x_4704_, 0);
v_scopes_4706_ = lean_ctor_get(v___x_4704_, 2);
v_usedQuotCtxts_4707_ = lean_ctor_get(v___x_4704_, 3);
v_nextMacroScope_4708_ = lean_ctor_get(v___x_4704_, 4);
v_maxRecDepth_4709_ = lean_ctor_get(v___x_4704_, 5);
v_ngen_4710_ = lean_ctor_get(v___x_4704_, 6);
v_auxDeclNGen_4711_ = lean_ctor_get(v___x_4704_, 7);
v_infoState_4712_ = lean_ctor_get(v___x_4704_, 8);
v_traceState_4713_ = lean_ctor_get(v___x_4704_, 9);
v_snapshotTasks_4714_ = lean_ctor_get(v___x_4704_, 10);
v_prevLinterStates_4715_ = lean_ctor_get(v___x_4704_, 11);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4728_ == 0)
{
lean_object* v_unused_4729_; 
v_unused_4729_ = lean_ctor_get(v___x_4704_, 1);
lean_dec(v_unused_4729_);
v___x_4717_ = v___x_4704_;
v_isShared_4718_ = v_isSharedCheck_4728_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_prevLinterStates_4715_);
lean_inc(v_snapshotTasks_4714_);
lean_inc(v_traceState_4713_);
lean_inc(v_infoState_4712_);
lean_inc(v_auxDeclNGen_4711_);
lean_inc(v_ngen_4710_);
lean_inc(v_maxRecDepth_4709_);
lean_inc(v_nextMacroScope_4708_);
lean_inc(v_usedQuotCtxts_4707_);
lean_inc(v_scopes_4706_);
lean_inc(v_env_4705_);
lean_dec(v___x_4704_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4728_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4719_; lean_object* v___x_4721_; 
v___x_4719_ = l_Lean_MessageLog_empty;
if (v_isShared_4718_ == 0)
{
lean_ctor_set(v___x_4717_, 1, v___x_4719_);
v___x_4721_ = v___x_4717_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_env_4705_);
lean_ctor_set(v_reuseFailAlloc_4727_, 1, v___x_4719_);
lean_ctor_set(v_reuseFailAlloc_4727_, 2, v_scopes_4706_);
lean_ctor_set(v_reuseFailAlloc_4727_, 3, v_usedQuotCtxts_4707_);
lean_ctor_set(v_reuseFailAlloc_4727_, 4, v_nextMacroScope_4708_);
lean_ctor_set(v_reuseFailAlloc_4727_, 5, v_maxRecDepth_4709_);
lean_ctor_set(v_reuseFailAlloc_4727_, 6, v_ngen_4710_);
lean_ctor_set(v_reuseFailAlloc_4727_, 7, v_auxDeclNGen_4711_);
lean_ctor_set(v_reuseFailAlloc_4727_, 8, v_infoState_4712_);
lean_ctor_set(v_reuseFailAlloc_4727_, 9, v_traceState_4713_);
lean_ctor_set(v_reuseFailAlloc_4727_, 10, v_snapshotTasks_4714_);
lean_ctor_set(v_reuseFailAlloc_4727_, 11, v_prevLinterStates_4715_);
v___x_4721_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4725_; 
v___x_4722_ = lean_st_ref_set(v_a_4664_, v___x_4721_);
v___x_4723_ = lean_box(0);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 0, v___x_4723_);
v___x_4725_ = v___x_4678_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4723_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
}
}
else
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
v_a_4731_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4671_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4671_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4739_, v_a_4740_, v_a_4741_);
lean_dec(v_a_4741_);
lean_dec_ref(v_a_4740_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4744_, lean_object* v_as_4745_, lean_object* v_as_x27_4746_, uint8_t v_b_4747_, lean_object* v_a_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
lean_object* v___x_4752_; 
v___x_4752_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4744_, v_as_x27_4746_, v_b_4747_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4753_, lean_object* v_as_4754_, lean_object* v_as_x27_4755_, lean_object* v_b_4756_, lean_object* v_a_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
uint8_t v_foundPanic_boxed_4761_; uint8_t v_b_boxed_4762_; lean_object* v_res_4763_; 
v_foundPanic_boxed_4761_ = lean_unbox(v_foundPanic_4753_);
v_b_boxed_4762_ = lean_unbox(v_b_4756_);
v_res_4763_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4761_, v_as_4754_, v_as_x27_4755_, v_b_boxed_4762_, v_a_4757_, v___y_4758_, v___y_4759_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_as_x27_4755_);
lean_dec(v_as_4754_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4772_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4773_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4774_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4775_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4776_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4772_, v___x_4773_, v___x_4774_, v___x_4775_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4778_;
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
