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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12_value;
static const lean_closure_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__13_value;
static const lean_closure_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__14_value;
static const lean_closure_object l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Message_isTrace___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__15_value;
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
lean_object* v___y_91_; uint8_t v___y_92_; lean_object* v___y_96_; uint32_t v___y_97_; lean_object* v_str_102_; lean_object* v_pos_114_; lean_object* v_endPos_115_; uint8_t v_severity_116_; lean_object* v_caption_117_; lean_object* v_data_118_; lean_object* v___x_119_; lean_object* v___y_121_; lean_object* v___y_122_; lean_object* v___y_123_; lean_object* v_str_134_; lean_object* v_str_146_; lean_object* v___y_157_; uint8_t v___y_158_; lean_object* v_str_163_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_pos_114_ = lean_ctor_get(v_msg_87_, 1);
lean_inc_ref(v_pos_114_);
v_endPos_115_ = lean_ctor_get(v_msg_87_, 2);
lean_inc(v_endPos_115_);
v_severity_116_ = lean_ctor_get_uint8(v_msg_87_, sizeof(void*)*5 + 1);
v_caption_117_ = lean_ctor_get(v_msg_87_, 3);
v_data_118_ = lean_ctor_get(v_msg_87_, 4);
lean_inc(v_data_118_);
v___x_119_ = l_Lean_MessageData_toString(v_data_118_);
v___x_170_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_171_ = lean_string_dec_eq(v_caption_117_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__11));
lean_inc_ref(v_caption_117_);
v___x_173_ = lean_string_append(v_caption_117_, v___x_172_);
v___x_174_ = lean_string_append(v___x_173_, v___x_119_);
lean_dec_ref(v___x_119_);
v_str_163_ = v___x_174_;
goto v___jp_162_;
}
else
{
v_str_163_ = v___x_119_;
goto v___jp_162_;
}
v___jp_90_:
{
if (v___y_92_ == 0)
{
return v___y_91_;
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_94_ = lean_string_append(v___y_91_, v___x_93_);
return v___x_94_;
}
}
v___jp_95_:
{
uint32_t v___x_98_; uint8_t v___x_99_; uint8_t v___x_100_; 
v___x_98_ = 10;
v___x_99_ = lean_uint32_dec_eq(v___y_97_, v___x_98_);
v___x_100_ = lean_bool_not(v___x_99_);
v___y_91_ = v___y_96_;
v___y_92_ = v___x_100_;
goto v___jp_90_;
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
lean_dec_ref_known(v___x_106_, 3);
v___x_108_ = 65;
v___y_96_ = v_str_102_;
v___y_97_ = v___x_108_;
goto v___jp_95_;
}
else
{
lean_object* v_val_109_; lean_object* v___x_110_; 
v_val_109_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_val_109_);
lean_dec_ref_known(v___x_107_, 1);
v___x_110_ = l_String_Slice_Pos_get_x3f(v___x_106_, v_val_109_);
lean_dec(v_val_109_);
lean_dec_ref_known(v___x_106_, 3);
if (lean_obj_tag(v___x_110_) == 0)
{
uint32_t v___x_111_; 
v___x_111_ = 65;
v___y_96_ = v_str_102_;
v___y_97_ = v___x_111_;
goto v___jp_95_;
}
else
{
lean_object* v_val_112_; uint32_t v___x_113_; 
v_val_112_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_val_112_);
lean_dec_ref_known(v___x_110_, 1);
v___x_113_ = lean_unbox_uint32(v_val_112_);
lean_dec(v_val_112_);
v___y_96_ = v_str_102_;
v___y_97_ = v___x_113_;
goto v___jp_95_;
}
}
}
else
{
v___y_91_ = v_str_102_;
v___y_92_ = v___x_105_;
goto v___jp_90_;
}
}
v___jp_120_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_124_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__1));
v___x_125_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v___y_122_, v_pos_114_);
v___x_126_ = lean_string_append(v___x_124_, v___x_125_);
lean_dec_ref(v___x_125_);
v___x_127_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2));
v___x_128_ = lean_string_append(v___x_126_, v___x_127_);
v___x_129_ = lean_string_append(v___x_128_, v___y_123_);
lean_dec_ref(v___y_123_);
v___x_130_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_131_ = lean_string_append(v___x_129_, v___x_130_);
v___x_132_ = lean_string_append(v___x_131_, v___y_121_);
lean_dec_ref(v___y_121_);
v_str_102_ = v___x_132_;
goto v___jp_101_;
}
v___jp_133_:
{
if (lean_obj_tag(v_reportPos_x3f_88_) == 1)
{
if (lean_obj_tag(v_endPos_115_) == 0)
{
lean_object* v_val_135_; lean_object* v___x_136_; 
v_val_135_ = lean_ctor_get(v_reportPos_x3f_88_, 0);
v___x_136_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__3));
v___y_121_ = v_str_134_;
v___y_122_ = v_val_135_;
v___y_123_ = v___x_136_;
goto v___jp_120_;
}
else
{
lean_object* v_val_137_; lean_object* v_val_138_; lean_object* v_line_139_; lean_object* v_column_140_; lean_object* v_line_141_; uint8_t v___x_142_; 
v_val_137_ = lean_ctor_get(v_endPos_115_, 0);
lean_inc(v_val_137_);
lean_dec_ref_known(v_endPos_115_, 1);
v_val_138_ = lean_ctor_get(v_reportPos_x3f_88_, 0);
v_line_139_ = lean_ctor_get(v_val_137_, 0);
v_column_140_ = lean_ctor_get(v_val_137_, 1);
v_line_141_ = lean_ctor_get(v_pos_114_, 0);
v___x_142_ = lean_nat_dec_eq(v_line_139_, v_line_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v_val_138_, v_val_137_);
v___y_121_ = v_str_134_;
v___y_122_ = v_val_138_;
v___y_123_ = v___x_143_;
goto v___jp_120_;
}
else
{
lean_object* v___x_144_; 
lean_inc(v_column_140_);
lean_dec(v_val_137_);
v___x_144_ = l_Nat_reprFast(v_column_140_);
v___y_121_ = v_str_134_;
v___y_122_ = v_val_138_;
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
v___x_147_ = l_Lean_Message_isTrace(v_msg_87_);
lean_dec_ref(v_msg_87_);
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
uint8_t v___x_159_; 
v___x_159_ = lean_bool_not(v___y_158_);
if (v___x_159_ == 0)
{
v_str_146_ = v___y_157_;
goto v___jp_145_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_161_ = lean_string_append(v___x_160_, v___y_157_);
lean_dec_ref(v___y_157_);
v_str_146_ = v___x_161_;
goto v___jp_145_;
}
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
v___y_157_ = v_str_163_;
v___y_158_ = v___x_167_;
goto v___jp_156_;
}
else
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_string_memcmp(v_str_163_, v___x_164_, v___x_168_, v___x_168_, v___x_166_);
v___y_157_ = v_str_163_;
v___y_158_ = v___x_169_;
goto v___jp_156_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_toCtorIdx(uint8_t v_x_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx(v_x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_toCtorIdx___boxed(lean_object* v_x_188_){
_start:
{
uint8_t v_x_4__boxed_189_; lean_object* v_res_190_; 
v_x_4__boxed_189_ = lean_unbox(v_x_188_);
v_res_190_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_toCtorIdx(v_x_4__boxed_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(lean_object* v_k_191_){
_start:
{
lean_inc(v_k_191_);
return v_k_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg___boxed(lean_object* v_k_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(v_k_192_);
lean_dec(v_k_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(lean_object* v_motive_194_, lean_object* v_ctorIdx_195_, uint8_t v_t_196_, lean_object* v_h_197_, lean_object* v_k_198_){
_start:
{
lean_inc(v_k_198_);
return v_k_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___boxed(lean_object* v_motive_199_, lean_object* v_ctorIdx_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_k_203_){
_start:
{
uint8_t v_t_boxed_204_; lean_object* v_res_205_; 
v_t_boxed_204_ = lean_unbox(v_t_201_);
v_res_205_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(v_motive_199_, v_ctorIdx_200_, v_t_boxed_204_, v_h_202_, v_k_203_);
lean_dec(v_k_203_);
lean_dec(v_ctorIdx_200_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(lean_object* v_check_206_){
_start:
{
lean_inc(v_check_206_);
return v_check_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg___boxed(lean_object* v_check_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(v_check_207_);
lean_dec(v_check_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(lean_object* v_motive_209_, uint8_t v_t_210_, lean_object* v_h_211_, lean_object* v_check_212_){
_start:
{
lean_inc(v_check_212_);
return v_check_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___boxed(lean_object* v_motive_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_check_216_){
_start:
{
uint8_t v_t_boxed_217_; lean_object* v_res_218_; 
v_t_boxed_217_ = lean_unbox(v_t_214_);
v_res_218_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(v_motive_213_, v_t_boxed_217_, v_h_215_, v_check_216_);
lean_dec(v_check_216_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(lean_object* v_drop_219_){
_start:
{
lean_inc(v_drop_219_);
return v_drop_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg___boxed(lean_object* v_drop_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(v_drop_220_);
lean_dec(v_drop_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(lean_object* v_motive_222_, uint8_t v_t_223_, lean_object* v_h_224_, lean_object* v_drop_225_){
_start:
{
lean_inc(v_drop_225_);
return v_drop_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___boxed(lean_object* v_motive_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_drop_229_){
_start:
{
uint8_t v_t_boxed_230_; lean_object* v_res_231_; 
v_t_boxed_230_ = lean_unbox(v_t_227_);
v_res_231_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(v_motive_226_, v_t_boxed_230_, v_h_228_, v_drop_229_);
lean_dec(v_drop_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(lean_object* v_pass_232_){
_start:
{
lean_inc(v_pass_232_);
return v_pass_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg___boxed(lean_object* v_pass_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(v_pass_233_);
lean_dec(v_pass_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(lean_object* v_motive_235_, uint8_t v_t_236_, lean_object* v_h_237_, lean_object* v_pass_238_){
_start:
{
lean_inc(v_pass_238_);
return v_pass_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___boxed(lean_object* v_motive_239_, lean_object* v_t_240_, lean_object* v_h_241_, lean_object* v_pass_242_){
_start:
{
uint8_t v_t_boxed_243_; lean_object* v_res_244_; 
v_t_boxed_243_ = lean_unbox(v_t_240_);
v_res_244_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(v_motive_239_, v_t_boxed_243_, v_h_241_, v_pass_242_);
lean_dec(v_pass_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(uint8_t v_x_245_){
_start:
{
switch(v_x_245_)
{
case 0:
{
lean_object* v___x_246_; 
v___x_246_ = lean_unsigned_to_nat(0u);
return v___x_246_;
}
case 1:
{
lean_object* v___x_247_; 
v___x_247_ = lean_unsigned_to_nat(1u);
return v___x_247_;
}
default: 
{
lean_object* v___x_248_; 
v___x_248_ = lean_unsigned_to_nat(2u);
return v___x_248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___boxed(lean_object* v_x_249_){
_start:
{
uint8_t v_x_boxed_250_; lean_object* v_res_251_; 
v_x_boxed_250_ = lean_unbox(v_x_249_);
v_res_251_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(v_x_boxed_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx(uint8_t v_x_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx(v_x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx___boxed(lean_object* v_x_254_){
_start:
{
uint8_t v_x_4__boxed_255_; lean_object* v_res_256_; 
v_x_4__boxed_255_ = lean_unbox(v_x_254_);
v_res_256_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_toCtorIdx(v_x_4__boxed_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(lean_object* v_k_257_){
_start:
{
lean_inc(v_k_257_);
return v_k_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg___boxed(lean_object* v_k_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(v_k_258_);
lean_dec(v_k_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(lean_object* v_motive_260_, lean_object* v_ctorIdx_261_, uint8_t v_t_262_, lean_object* v_h_263_, lean_object* v_k_264_){
_start:
{
lean_inc(v_k_264_);
return v_k_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___boxed(lean_object* v_motive_265_, lean_object* v_ctorIdx_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_k_269_){
_start:
{
uint8_t v_t_boxed_270_; lean_object* v_res_271_; 
v_t_boxed_270_ = lean_unbox(v_t_267_);
v_res_271_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(v_motive_265_, v_ctorIdx_266_, v_t_boxed_270_, v_h_268_, v_k_269_);
lean_dec(v_k_269_);
lean_dec(v_ctorIdx_266_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(lean_object* v_exact_272_){
_start:
{
lean_inc(v_exact_272_);
return v_exact_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg___boxed(lean_object* v_exact_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(v_exact_273_);
lean_dec(v_exact_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(lean_object* v_motive_275_, uint8_t v_t_276_, lean_object* v_h_277_, lean_object* v_exact_278_){
_start:
{
lean_inc(v_exact_278_);
return v_exact_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___boxed(lean_object* v_motive_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_exact_282_){
_start:
{
uint8_t v_t_boxed_283_; lean_object* v_res_284_; 
v_t_boxed_283_ = lean_unbox(v_t_280_);
v_res_284_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(v_motive_279_, v_t_boxed_283_, v_h_281_, v_exact_282_);
lean_dec(v_exact_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(lean_object* v_normalized_285_){
_start:
{
lean_inc(v_normalized_285_);
return v_normalized_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg___boxed(lean_object* v_normalized_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(v_normalized_286_);
lean_dec(v_normalized_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(lean_object* v_motive_288_, uint8_t v_t_289_, lean_object* v_h_290_, lean_object* v_normalized_291_){
_start:
{
lean_inc(v_normalized_291_);
return v_normalized_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___boxed(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_normalized_295_){
_start:
{
uint8_t v_t_boxed_296_; lean_object* v_res_297_; 
v_t_boxed_296_ = lean_unbox(v_t_293_);
v_res_297_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(v_motive_292_, v_t_boxed_296_, v_h_294_, v_normalized_295_);
lean_dec(v_normalized_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(lean_object* v_lax_298_){
_start:
{
lean_inc(v_lax_298_);
return v_lax_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg___boxed(lean_object* v_lax_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(v_lax_299_);
lean_dec(v_lax_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(lean_object* v_motive_301_, uint8_t v_t_302_, lean_object* v_h_303_, lean_object* v_lax_304_){
_start:
{
lean_inc(v_lax_304_);
return v_lax_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___boxed(lean_object* v_motive_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_lax_308_){
_start:
{
uint8_t v_t_boxed_309_; lean_object* v_res_310_; 
v_t_boxed_309_ = lean_unbox(v_t_306_);
v_res_310_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(v_motive_305_, v_t_boxed_309_, v_h_307_, v_lax_308_);
lean_dec(v_lax_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(uint8_t v_x_311_){
_start:
{
if (v_x_311_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_unsigned_to_nat(0u);
return v___x_312_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = lean_unsigned_to_nat(1u);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___boxed(lean_object* v_x_314_){
_start:
{
uint8_t v_x_boxed_315_; lean_object* v_res_316_; 
v_x_boxed_315_ = lean_unbox(v_x_314_);
v_res_316_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(v_x_boxed_315_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx(uint8_t v_x_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx(v_x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx___boxed(lean_object* v_x_319_){
_start:
{
uint8_t v_x_4__boxed_320_; lean_object* v_res_321_; 
v_x_4__boxed_320_ = lean_unbox(v_x_319_);
v_res_321_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_toCtorIdx(v_x_4__boxed_320_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(lean_object* v_k_322_){
_start:
{
lean_inc(v_k_322_);
return v_k_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg___boxed(lean_object* v_k_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(v_k_323_);
lean_dec(v_k_323_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(lean_object* v_motive_325_, lean_object* v_ctorIdx_326_, uint8_t v_t_327_, lean_object* v_h_328_, lean_object* v_k_329_){
_start:
{
lean_inc(v_k_329_);
return v_k_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___boxed(lean_object* v_motive_330_, lean_object* v_ctorIdx_331_, lean_object* v_t_332_, lean_object* v_h_333_, lean_object* v_k_334_){
_start:
{
uint8_t v_t_boxed_335_; lean_object* v_res_336_; 
v_t_boxed_335_ = lean_unbox(v_t_332_);
v_res_336_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(v_motive_330_, v_ctorIdx_331_, v_t_boxed_335_, v_h_333_, v_k_334_);
lean_dec(v_k_334_);
lean_dec(v_ctorIdx_331_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(lean_object* v_exact_337_){
_start:
{
lean_inc(v_exact_337_);
return v_exact_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg___boxed(lean_object* v_exact_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(v_exact_338_);
lean_dec(v_exact_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(lean_object* v_motive_340_, uint8_t v_t_341_, lean_object* v_h_342_, lean_object* v_exact_343_){
_start:
{
lean_inc(v_exact_343_);
return v_exact_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___boxed(lean_object* v_motive_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_exact_347_){
_start:
{
uint8_t v_t_boxed_348_; lean_object* v_res_349_; 
v_t_boxed_348_ = lean_unbox(v_t_345_);
v_res_349_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(v_motive_344_, v_t_boxed_348_, v_h_346_, v_exact_347_);
lean_dec(v_exact_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(lean_object* v_sorted_350_){
_start:
{
lean_inc(v_sorted_350_);
return v_sorted_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg___boxed(lean_object* v_sorted_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(v_sorted_351_);
lean_dec(v_sorted_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(lean_object* v_motive_353_, uint8_t v_t_354_, lean_object* v_h_355_, lean_object* v_sorted_356_){
_start:
{
lean_inc(v_sorted_356_);
return v_sorted_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___boxed(lean_object* v_motive_357_, lean_object* v_t_358_, lean_object* v_h_359_, lean_object* v_sorted_360_){
_start:
{
uint8_t v_t_boxed_361_; lean_object* v_res_362_; 
v_t_boxed_361_ = lean_unbox(v_t_358_);
v_res_362_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(v_motive_357_, v_t_boxed_361_, v_h_359_, v_sorted_360_);
lean_dec(v_sorted_360_);
return v_res_362_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_box(0);
v___x_364_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg(){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___boxed(lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(lean_object* v_00_u03b1_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___boxed(lean_object* v_00_u03b1_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(v_00_u03b1_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(lean_object* v_action_x3f_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
if (lean_obj_tag(v_action_x3f_398_) == 1)
{
lean_object* v_val_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_433_; 
v_val_402_ = lean_ctor_get(v_action_x3f_398_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_action_x3f_398_);
if (v_isSharedCheck_433_ == 0)
{
v___x_404_ = v_action_x3f_398_;
v_isShared_405_ = v_isSharedCheck_433_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_val_402_);
lean_dec(v_action_x3f_398_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_433_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1));
lean_inc(v_val_402_);
v___x_407_ = l_Lean_Syntax_isOfKind(v_val_402_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_del_object(v___x_404_);
lean_dec(v_val_402_);
v___x_408_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_408_;
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = l_Lean_Syntax_getArg(v_val_402_, v___x_409_);
lean_dec(v_val_402_);
v___x_411_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4));
lean_inc(v___x_410_);
v___x_412_ = l_Lean_Syntax_isOfKind(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6));
lean_inc(v___x_410_);
v___x_414_ = l_Lean_Syntax_isOfKind(v___x_410_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8));
v___x_416_ = l_Lean_Syntax_isOfKind(v___x_410_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
lean_del_object(v___x_404_);
v___x_417_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_417_;
}
else
{
uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_418_ = 2;
v___x_419_ = lean_box(v___x_418_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 0);
lean_ctor_set(v___x_404_, 0, v___x_419_);
v___x_421_ = v___x_404_;
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
lean_dec(v___x_410_);
v___x_423_ = 1;
v___x_424_ = lean_box(v___x_423_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 0);
lean_ctor_set(v___x_404_, 0, v___x_424_);
v___x_426_ = v___x_404_;
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
else
{
uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
lean_dec(v___x_410_);
v___x_428_ = 0;
v___x_429_ = lean_box(v___x_428_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 0);
lean_ctor_set(v___x_404_, 0, v___x_429_);
v___x_431_ = v___x_404_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
else
{
uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_action_x3f_398_);
v___x_434_ = 0;
v___x_435_ = lean_box(v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___boxed(lean_object* v_action_x3f_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_437_, v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
return v_res_441_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(uint8_t v___x_442_, lean_object* v_x_443_){
_start:
{
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed(lean_object* v___x_444_, lean_object* v_x_445_){
_start:
{
uint8_t v___x_1459__boxed_446_; uint8_t v_res_447_; lean_object* v_r_448_; 
v___x_1459__boxed_446_ = lean_unbox(v___x_444_);
v_res_447_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_1459__boxed_446_, v_x_445_);
lean_dec_ref(v_x_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(lean_object* v_msg_449_){
_start:
{
uint8_t v___x_450_; uint8_t v___x_451_; 
v___x_450_ = l_Lean_Message_isTrace(v_msg_449_);
v___x_451_ = lean_bool_not(v___x_450_);
if (v___x_451_ == 0)
{
return v___x_451_;
}
else
{
uint8_t v_severity_452_; uint8_t v___x_453_; uint8_t v___x_454_; 
v_severity_452_ = lean_ctor_get_uint8(v_msg_449_, sizeof(void*)*5 + 1);
v___x_453_ = 2;
v___x_454_ = l_Lean_instBEqMessageSeverity_beq(v_severity_452_, v___x_453_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object* v_msg_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v_msg_455_);
lean_dec_ref(v_msg_455_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(lean_object* v_msg_458_){
_start:
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = l_Lean_Message_isTrace(v_msg_458_);
v___x_460_ = lean_bool_not(v___x_459_);
if (v___x_460_ == 0)
{
return v___x_460_;
}
else
{
uint8_t v_severity_461_; uint8_t v___x_462_; uint8_t v___x_463_; 
v_severity_461_ = lean_ctor_get_uint8(v_msg_458_, sizeof(void*)*5 + 1);
v___x_462_ = 1;
v___x_463_ = l_Lean_instBEqMessageSeverity_beq(v_severity_461_, v___x_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object* v_msg_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v_msg_464_);
lean_dec_ref(v_msg_464_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(lean_object* v_msg_467_){
_start:
{
uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = l_Lean_Message_isTrace(v_msg_467_);
v___x_469_ = lean_bool_not(v___x_468_);
if (v___x_469_ == 0)
{
return v___x_469_;
}
else
{
uint8_t v_severity_470_; uint8_t v___x_471_; uint8_t v___x_472_; 
v_severity_470_ = lean_ctor_get_uint8(v_msg_467_, sizeof(void*)*5 + 1);
v___x_471_ = 0;
v___x_472_ = l_Lean_instBEqMessageSeverity_beq(v_severity_470_, v___x_471_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object* v_msg_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v_msg_473_);
lean_dec_ref(v_msg_473_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(lean_object* v_x_504_){
_start:
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1));
lean_inc(v_x_504_);
v___x_507_ = l_Lean_Syntax_isOfKind(v_x_504_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec(v_x_504_);
v___x_508_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = l_Lean_Syntax_getArg(v_x_504_, v___x_509_);
lean_dec(v_x_504_);
v___x_511_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3));
lean_inc(v___x_510_);
v___x_512_ = l_Lean_Syntax_isOfKind(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5));
lean_inc(v___x_510_);
v___x_514_ = l_Lean_Syntax_isOfKind(v___x_510_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7));
lean_inc(v___x_510_);
v___x_516_ = l_Lean_Syntax_isOfKind(v___x_510_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9));
lean_inc(v___x_510_);
v___x_518_ = l_Lean_Syntax_isOfKind(v___x_510_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11));
v___x_520_ = l_Lean_Syntax_isOfKind(v___x_510_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_521_;
}
else
{
lean_object* v___x_522_; lean_object* v___f_523_; lean_object* v___x_524_; 
v___x_522_ = lean_box(v___x_520_);
v___f_523_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_523_, 0, v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___f_523_);
return v___x_524_;
}
}
else
{
lean_object* v___f_525_; lean_object* v___x_526_; 
lean_dec(v___x_510_);
v___f_525_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12));
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___f_525_);
return v___x_526_;
}
}
else
{
lean_object* v___f_527_; lean_object* v___x_528_; 
lean_dec(v___x_510_);
v___f_527_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__13));
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___f_527_);
return v___x_528_;
}
}
else
{
lean_object* v___f_529_; lean_object* v___x_530_; 
lean_dec(v___x_510_);
v___f_529_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__14));
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___f_529_);
return v___x_530_;
}
}
else
{
lean_object* v___f_531_; lean_object* v___x_532_; 
lean_dec(v___x_510_);
v___f_531_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__15));
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___f_531_);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___boxed(lean_object* v_x_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(lean_object* v_x_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_536_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___boxed(lean_object* v_x_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(v_x_541_, v_a_542_, v_a_543_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
return v_res_545_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object* v_x_546_){
_start:
{
uint8_t v___x_547_; 
v___x_547_ = 0;
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object* v_x_548_){
_start:
{
uint8_t v_res_549_; lean_object* v_r_550_; 
v_res_549_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(v_x_548_);
lean_dec_ref(v_x_548_);
v_r_550_ = lean_box(v_res_549_);
return v_r_550_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(lean_object* v_snd_551_, lean_object* v___y_552_){
_start:
{
if (lean_obj_tag(v_snd_551_) == 0)
{
uint8_t v___x_553_; 
lean_dec_ref(v___y_552_);
v___x_553_ = 0;
return v___x_553_;
}
else
{
lean_object* v_val_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_val_554_ = lean_ctor_get(v_snd_551_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v_snd_551_, 1);
v___x_555_ = lean_apply_1(v_val_554_, v___y_552_);
v___x_556_ = lean_unbox(v___x_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed(lean_object* v_snd_557_, lean_object* v___y_558_){
_start:
{
uint8_t v_res_559_; lean_object* v_r_560_; 
v_res_559_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(v_snd_557_, v___y_558_);
v_r_560_ = lean_box(v_res_559_);
return v_r_560_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(lean_object* v_a_561_, lean_object* v_snd_562_, uint8_t v_a_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_565_; uint8_t v___x_566_; 
lean_inc_ref(v___y_564_);
v___x_565_ = lean_apply_1(v_a_561_, v___y_564_);
v___x_566_ = lean_unbox(v___x_565_);
if (v___x_566_ == 0)
{
if (lean_obj_tag(v_snd_562_) == 0)
{
uint8_t v___x_567_; 
lean_dec_ref(v___y_564_);
v___x_567_ = 2;
return v___x_567_;
}
else
{
lean_object* v_val_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_val_568_ = lean_ctor_get(v_snd_562_, 0);
lean_inc(v_val_568_);
lean_dec_ref_known(v_snd_562_, 1);
v___x_569_ = lean_apply_1(v_val_568_, v___y_564_);
v___x_570_ = lean_unbox(v___x_569_);
return v___x_570_;
}
}
else
{
lean_dec_ref(v___y_564_);
lean_dec(v_snd_562_);
return v_a_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed(lean_object* v_a_571_, lean_object* v_snd_572_, lean_object* v_a_573_, lean_object* v___y_574_){
_start:
{
uint8_t v_a_11568__boxed_575_; uint8_t v_res_576_; lean_object* v_r_577_; 
v_a_11568__boxed_575_ = lean_unbox(v_a_573_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_571_, v_snd_572_, v_a_11568__boxed_575_, v___y_574_);
v_r_577_ = lean_box(v_res_576_);
return v_r_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object* v_as_638_, size_t v_sz_639_, size_t v_i_640_, lean_object* v_b_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_a_646_; uint8_t v___x_650_; 
v___x_650_ = lean_usize_dec_lt(v_i_640_, v_sz_639_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v_b_641_);
return v___x_651_;
}
else
{
lean_object* v_snd_652_; lean_object* v_snd_653_; lean_object* v_snd_654_; lean_object* v_fst_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_962_; 
v_snd_652_ = lean_ctor_get(v_b_641_, 1);
lean_inc(v_snd_652_);
v_snd_653_ = lean_ctor_get(v_snd_652_, 1);
lean_inc(v_snd_653_);
v_snd_654_ = lean_ctor_get(v_snd_653_, 1);
lean_inc(v_snd_654_);
v_fst_655_ = lean_ctor_get(v_b_641_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_b_641_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_b_641_, 1);
lean_dec(v_unused_963_);
v___x_657_ = v_b_641_;
v_isShared_658_ = v_isSharedCheck_962_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_fst_655_);
lean_dec(v_b_641_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_962_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_fst_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_960_; 
v_fst_659_ = lean_ctor_get(v_snd_652_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_snd_652_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v_snd_652_, 1);
lean_dec(v_unused_961_);
v___x_661_ = v_snd_652_;
v_isShared_662_ = v_isSharedCheck_960_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_fst_659_);
lean_dec(v_snd_652_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_960_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_fst_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_958_; 
v_fst_663_ = lean_ctor_get(v_snd_653_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v_snd_653_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v_snd_653_, 1);
lean_dec(v_unused_959_);
v___x_665_ = v_snd_653_;
v_isShared_666_ = v_isSharedCheck_958_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_fst_663_);
lean_dec(v_snd_653_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_958_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_fst_667_; lean_object* v_snd_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_957_; 
v_fst_667_ = lean_ctor_get(v_snd_654_, 0);
v_snd_668_ = lean_ctor_get(v_snd_654_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v_snd_654_);
if (v_isSharedCheck_957_ == 0)
{
v___x_670_ = v_snd_654_;
v_isShared_671_ = v_isSharedCheck_957_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_snd_668_);
lean_inc(v_fst_667_);
lean_dec(v_snd_654_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_957_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_a_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_a_672_ = lean_array_uget_borrowed(v_as_638_, v_i_640_);
v___x_673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_a_672_);
v___x_674_ = l_Lean_Syntax_isOfKind(v_a_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v___x_677_; 
lean_dec_ref_known(v___x_675_, 1);
if (v_isShared_671_ == 0)
{
v___x_677_ = v___x_670_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_fst_667_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_snd_668_);
v___x_677_ = v_reuseFailAlloc_687_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_679_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_677_);
v___x_679_ = v___x_665_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_fst_663_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_677_);
v___x_679_ = v_reuseFailAlloc_686_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_679_);
v___x_681_ = v___x_661_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_fst_659_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_681_);
v___x_683_ = v___x_657_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
v_a_646_ = v___x_683_;
goto v___jp_645_;
}
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_del_object(v___x_670_);
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_del_object(v___x_665_);
lean_dec(v_fst_663_);
lean_del_object(v___x_661_);
lean_dec(v_fst_659_);
lean_del_object(v___x_657_);
lean_dec(v_fst_655_);
v_a_688_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_675_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_675_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_action_x3f_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = l_Lean_Syntax_getArg(v_a_672_, v___x_696_);
v___x_738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3));
lean_inc(v___x_697_);
v___x_739_ = l_Lean_Syntax_isOfKind(v___x_697_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; uint8_t v___x_741_; 
lean_del_object(v___x_670_);
lean_del_object(v___x_665_);
lean_del_object(v___x_661_);
lean_del_object(v___x_657_);
v___x_740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5));
lean_inc(v___x_697_);
v___x_741_ = l_Lean_Syntax_isOfKind(v___x_697_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; uint8_t v_reportPositions_743_; 
v___x_742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7));
lean_inc(v___x_697_);
v_reportPositions_743_ = l_Lean_Syntax_isOfKind(v___x_697_, v___x_742_);
if (v_reportPositions_743_ == 0)
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9));
lean_inc(v___x_697_);
v___x_745_ = l_Lean_Syntax_isOfKind(v___x_697_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11));
lean_inc(v___x_697_);
v___x_747_ = l_Lean_Syntax_isOfKind(v___x_697_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
lean_dec(v___x_697_);
v___x_748_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec_ref_known(v___x_748_, 1);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_fst_667_);
lean_ctor_set(v___x_749_, 1, v_snd_668_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_fst_663_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_fst_659_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_fst_655_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v_a_646_ = v___x_752_;
goto v___jp_645_;
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
lean_dec(v_fst_655_);
v_a_753_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_748_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_748_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_761_ = lean_unsigned_to_nat(2u);
v___x_762_ = l_Lean_Syntax_getArg(v___x_697_, v___x_761_);
lean_dec(v___x_697_);
v___x_763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_762_);
v___x_764_ = l_Lean_Syntax_isOfKind(v___x_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_766_ = l_Lean_Syntax_isOfKind(v___x_762_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref_known(v___x_767_, 1);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v_fst_667_);
lean_ctor_set(v___x_768_, 1, v_snd_668_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v_fst_663_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v_fst_659_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_fst_655_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v_a_646_ = v___x_771_;
goto v___jp_645_;
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
lean_dec(v_fst_655_);
v_a_772_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_767_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_767_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec(v_fst_667_);
v___x_780_ = lean_box(v_reportPositions_743_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v_snd_668_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_fst_663_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v_fst_659_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_fst_655_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v_a_646_ = v___x_784_;
goto v___jp_645_;
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec(v___x_762_);
lean_dec(v_fst_667_);
v___x_785_ = lean_box(v___x_674_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v_snd_668_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_fst_663_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_fst_659_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_fst_655_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v_a_646_ = v___x_789_;
goto v___jp_645_;
}
}
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_790_ = lean_unsigned_to_nat(2u);
v___x_791_ = l_Lean_Syntax_getArg(v___x_697_, v___x_790_);
lean_dec(v___x_697_);
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17));
lean_inc(v___x_791_);
v___x_793_ = l_Lean_Syntax_isOfKind(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_dec(v___x_791_);
v___x_794_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec_ref_known(v___x_794_, 1);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_fst_667_);
lean_ctor_set(v___x_795_, 1, v_snd_668_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_fst_663_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_fst_659_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v_fst_655_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v_a_646_ = v___x_798_;
goto v___jp_645_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
lean_dec(v_fst_655_);
v_a_799_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_794_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_794_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_807_ = l_Lean_Syntax_getArg(v___x_791_, v___x_696_);
lean_dec(v___x_791_);
v___x_808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_807_);
v___x_809_ = l_Lean_Syntax_isOfKind(v___x_807_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_811_ = l_Lean_Syntax_isOfKind(v___x_807_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec_ref_known(v___x_812_, 1);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v_fst_667_);
lean_ctor_set(v___x_813_, 1, v_snd_668_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_fst_663_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_fst_659_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_fst_655_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v_a_646_ = v___x_816_;
goto v___jp_645_;
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
lean_dec(v_fst_655_);
v_a_817_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_812_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_812_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec(v_fst_663_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_fst_667_);
lean_ctor_set(v___x_825_, 1, v_snd_668_);
v___x_826_ = lean_box(v_reportPositions_743_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v___x_825_);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v_fst_659_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v_fst_655_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v_a_646_ = v___x_829_;
goto v___jp_645_;
}
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec(v___x_807_);
lean_dec(v_fst_663_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_fst_667_);
lean_ctor_set(v___x_830_, 1, v_snd_668_);
v___x_831_ = lean_box(v___x_674_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_830_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_fst_659_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_fst_655_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v_a_646_ = v___x_834_;
goto v___jp_645_;
}
}
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_835_ = lean_unsigned_to_nat(2u);
v___x_836_ = l_Lean_Syntax_getArg(v___x_697_, v___x_835_);
lean_dec(v___x_697_);
v___x_837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19));
lean_inc(v___x_836_);
v___x_838_ = l_Lean_Syntax_isOfKind(v___x_836_, v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; 
lean_dec(v___x_836_);
v___x_839_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec_ref_known(v___x_839_, 1);
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v_fst_667_);
lean_ctor_set(v___x_840_, 1, v_snd_668_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_fst_663_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v_fst_659_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_fst_655_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v_a_646_ = v___x_843_;
goto v___jp_645_;
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
lean_dec(v_fst_655_);
v_a_844_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_839_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_839_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_852_ = l_Lean_Syntax_getArg(v___x_836_, v___x_696_);
lean_dec(v___x_836_);
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_852_);
v___x_854_ = l_Lean_Syntax_isOfKind(v___x_852_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23));
v___x_856_ = l_Lean_Syntax_isOfKind(v___x_852_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec_ref_known(v___x_857_, 1);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v_fst_667_);
lean_ctor_set(v___x_858_, 1, v_snd_668_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_fst_663_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_fst_659_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_fst_655_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v_a_646_ = v___x_861_;
goto v___jp_645_;
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
lean_dec(v_fst_655_);
v_a_862_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_857_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_857_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec(v_fst_659_);
v___x_870_ = 1;
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v_fst_667_);
lean_ctor_set(v___x_871_, 1, v_snd_668_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_fst_663_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_box(v___x_870_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_872_);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v_fst_655_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v_a_646_ = v___x_875_;
goto v___jp_645_;
}
}
else
{
uint8_t v_ordering_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec(v___x_852_);
lean_dec(v_fst_659_);
v_ordering_876_ = 0;
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_fst_667_);
lean_ctor_set(v___x_877_, 1, v_snd_668_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_fst_663_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_box(v_ordering_876_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v___x_878_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v_fst_655_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v_a_646_ = v___x_881_;
goto v___jp_645_;
}
}
}
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_882_ = lean_unsigned_to_nat(2u);
v___x_883_ = l_Lean_Syntax_getArg(v___x_697_, v___x_882_);
lean_dec(v___x_697_);
v___x_884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25));
lean_inc(v___x_883_);
v___x_885_ = l_Lean_Syntax_isOfKind(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
lean_dec(v___x_883_);
v___x_886_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec_ref_known(v___x_886_, 1);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v_fst_667_);
lean_ctor_set(v___x_887_, 1, v_snd_668_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v_fst_663_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v_fst_659_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v_fst_655_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v_a_646_ = v___x_890_;
goto v___jp_645_;
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
lean_dec(v_fst_655_);
v_a_891_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_886_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_886_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_899_ = l_Lean_Syntax_getArg(v___x_883_, v___x_696_);
lean_dec(v___x_883_);
v___x_900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_899_);
v___x_901_ = l_Lean_Syntax_isOfKind(v___x_899_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27));
lean_inc(v___x_899_);
v___x_903_ = l_Lean_Syntax_isOfKind(v___x_899_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29));
v___x_905_ = l_Lean_Syntax_isOfKind(v___x_899_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec_ref_known(v___x_906_, 1);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v_fst_667_);
lean_ctor_set(v___x_907_, 1, v_snd_668_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v_fst_663_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_fst_659_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_fst_655_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v_a_646_ = v___x_910_;
goto v___jp_645_;
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
lean_dec(v_fst_655_);
v_a_911_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_906_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_906_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v_fst_655_);
v___x_919_ = 2;
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_fst_667_);
lean_ctor_set(v___x_920_, 1, v_snd_668_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v_fst_663_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_fst_659_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_box(v___x_919_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_922_);
v_a_646_ = v___x_924_;
goto v___jp_645_;
}
}
else
{
uint8_t v_whitespace_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec(v___x_899_);
lean_dec(v_fst_655_);
v_whitespace_925_ = 1;
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_fst_667_);
lean_ctor_set(v___x_926_, 1, v_snd_668_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_fst_663_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_fst_659_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = lean_box(v_whitespace_925_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_928_);
v_a_646_ = v___x_930_;
goto v___jp_645_;
}
}
else
{
uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec(v___x_899_);
lean_dec(v_fst_655_);
v___x_931_ = 0;
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_fst_667_);
lean_ctor_set(v___x_932_, 1, v_snd_668_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_fst_663_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_fst_659_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_box(v___x_931_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_934_);
v_a_646_ = v___x_936_;
goto v___jp_645_;
}
}
}
}
else
{
lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_937_ = l_Lean_Syntax_getArg(v___x_697_, v___x_696_);
v___x_938_ = l_Lean_Syntax_isNone(v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_937_);
v___x_940_ = l_Lean_Syntax_matchesNull(v___x_937_, v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
lean_dec(v___x_937_);
lean_dec(v___x_697_);
lean_del_object(v___x_670_);
lean_del_object(v___x_665_);
lean_del_object(v___x_661_);
lean_del_object(v___x_657_);
v___x_941_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec_ref_known(v___x_941_, 1);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v_fst_667_);
lean_ctor_set(v___x_942_, 1, v_snd_668_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_fst_663_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_fst_659_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_fst_655_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v_a_646_ = v___x_945_;
goto v___jp_645_;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_dec(v_fst_663_);
lean_dec(v_fst_659_);
lean_dec(v_fst_655_);
v_a_946_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_941_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_941_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = l_Lean_Syntax_getArg(v___x_937_, v___x_696_);
lean_dec(v___x_937_);
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
v_action_x3f_699_ = v___x_955_;
v___y_700_ = v___y_642_;
v___y_701_ = v___y_643_;
goto v___jp_698_;
}
}
else
{
lean_object* v___x_956_; 
lean_dec(v___x_937_);
v___x_956_ = lean_box(0);
v_action_x3f_699_ = v___x_956_;
v___y_700_ = v___y_642_;
v___y_701_ = v___y_643_;
goto v___jp_698_;
}
}
v___jp_698_:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = l_Lean_Syntax_getArg(v___x_697_, v___x_704_);
lean_dec(v___x_697_);
v___x_706_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v___x_705_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___f_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___f_708_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_708_, 0, v_a_707_);
lean_closure_set(v___f_708_, 1, v_snd_668_);
lean_closure_set(v___f_708_, 2, v_a_703_);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v___f_708_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_709_);
v___x_711_ = v___x_670_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_fst_667_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_709_);
v___x_711_ = v_reuseFailAlloc_721_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_711_);
v___x_713_ = v___x_665_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_fst_663_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_720_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_713_);
v___x_715_ = v___x_661_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_fst_659_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_713_);
v___x_715_ = v_reuseFailAlloc_719_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_715_);
v___x_717_ = v___x_657_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
v_a_646_ = v___x_717_;
goto v___jp_645_;
}
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_a_703_);
lean_del_object(v___x_670_);
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_del_object(v___x_665_);
lean_dec(v_fst_663_);
lean_del_object(v___x_661_);
lean_dec(v_fst_659_);
lean_del_object(v___x_657_);
lean_dec(v_fst_655_);
v_a_722_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_706_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_706_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v___x_697_);
lean_del_object(v___x_670_);
lean_dec(v_snd_668_);
lean_dec(v_fst_667_);
lean_del_object(v___x_665_);
lean_dec(v_fst_663_);
lean_del_object(v___x_661_);
lean_dec(v_fst_659_);
lean_del_object(v___x_657_);
lean_dec(v_fst_655_);
v_a_730_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_702_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_702_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
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
v___jp_645_:
{
size_t v___x_647_; size_t v___x_648_; 
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_640_, v___x_647_);
v_i_640_ = v___x_648_;
v_b_641_ = v_a_646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object* v_as_964_, lean_object* v_sz_965_, lean_object* v_i_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
size_t v_sz_boxed_971_; size_t v_i_boxed_972_; lean_object* v_res_973_; 
v_sz_boxed_971_ = lean_unbox_usize(v_sz_965_);
lean_dec(v_sz_965_);
v_i_boxed_972_ = lean_unbox_usize(v_i_966_);
lean_dec(v_i_966_);
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v_as_964_, v_sz_boxed_971_, v_i_boxed_972_, v_b_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec_ref(v_as_964_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(size_t v_sz_974_, size_t v_i_975_, lean_object* v_bs_976_){
_start:
{
uint8_t v___x_977_; 
v___x_977_ = lean_usize_dec_lt(v_i_975_, v_sz_974_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v_bs_976_);
return v___x_978_;
}
else
{
lean_object* v_v_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v_v_979_ = lean_array_uget(v_bs_976_, v_i_975_);
v___x_980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_v_979_);
v___x_981_ = l_Lean_Syntax_isOfKind(v_v_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
lean_dec(v_v_979_);
lean_dec_ref(v_bs_976_);
v___x_982_ = lean_box(0);
return v___x_982_;
}
else
{
lean_object* v___x_983_; lean_object* v_bs_x27_984_; size_t v___x_985_; size_t v___x_986_; lean_object* v___x_987_; 
v___x_983_ = lean_unsigned_to_nat(0u);
v_bs_x27_984_ = lean_array_uset(v_bs_976_, v_i_975_, v___x_983_);
v___x_985_ = ((size_t)1ULL);
v___x_986_ = lean_usize_add(v_i_975_, v___x_985_);
v___x_987_ = lean_array_uset(v_bs_x27_984_, v_i_975_, v_v_979_);
v_i_975_ = v___x_986_;
v_bs_976_ = v___x_987_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1___boxed(lean_object* v_sz_989_, lean_object* v_i_990_, lean_object* v_bs_991_){
_start:
{
size_t v_sz_boxed_992_; size_t v_i_boxed_993_; lean_object* v_res_994_; 
v_sz_boxed_992_ = lean_unbox_usize(v_sz_989_);
lean_dec(v_sz_989_);
v_i_boxed_993_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_res_994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_boxed_992_, v_i_boxed_993_, v_bs_991_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(uint8_t v___x_995_, lean_object* v_as_996_, size_t v_i_997_, size_t v_stop_998_, lean_object* v_b_999_){
_start:
{
lean_object* v___y_1001_; uint8_t v___x_1005_; 
v___x_1005_ = lean_usize_dec_eq(v_i_997_, v_stop_998_);
if (v___x_1005_ == 0)
{
lean_object* v_fst_1006_; uint8_t v___x_1007_; 
v_fst_1006_ = lean_ctor_get(v_b_999_, 0);
v___x_1007_ = lean_unbox(v_fst_1006_);
if (v___x_1007_ == 0)
{
lean_object* v_snd_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1016_; 
v_snd_1008_ = lean_ctor_get(v_b_999_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_b_999_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; 
v_unused_1017_ = lean_ctor_get(v_b_999_, 0);
lean_dec(v_unused_1017_);
v___x_1010_ = v_b_999_;
v_isShared_1011_ = v_isSharedCheck_1016_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_snd_1008_);
lean_dec(v_b_999_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1016_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = lean_box(v___x_995_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1012_);
v___x_1014_ = v___x_1010_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_snd_1008_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
v___y_1001_ = v___x_1014_;
goto v___jp_1000_;
}
}
}
else
{
lean_object* v_snd_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1028_; 
v_snd_1018_ = lean_ctor_get(v_b_999_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_b_999_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v_b_999_, 0);
lean_dec(v_unused_1029_);
v___x_1020_ = v_b_999_;
v_isShared_1021_ = v_isSharedCheck_1028_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_snd_1018_);
lean_dec(v_b_999_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1028_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1022_ = lean_array_uget_borrowed(v_as_996_, v_i_997_);
lean_inc(v___x_1022_);
v___x_1023_ = lean_array_push(v_snd_1018_, v___x_1022_);
v___x_1024_ = lean_box(v___x_1005_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v___x_1023_);
lean_ctor_set(v___x_1020_, 0, v___x_1024_);
v___x_1026_ = v___x_1020_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_1023_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
v___y_1001_ = v___x_1026_;
goto v___jp_1000_;
}
}
}
}
else
{
return v_b_999_;
}
v___jp_1000_:
{
size_t v___x_1002_; size_t v___x_1003_; 
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_add(v_i_997_, v___x_1002_);
v_i_997_ = v___x_1003_;
v_b_999_ = v___y_1001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object* v___x_1030_, lean_object* v_as_1031_, lean_object* v_i_1032_, lean_object* v_stop_1033_, lean_object* v_b_1034_){
_start:
{
uint8_t v___x_12443__boxed_1035_; size_t v_i_boxed_1036_; size_t v_stop_boxed_1037_; lean_object* v_res_1038_; 
v___x_12443__boxed_1035_ = lean_unbox(v___x_1030_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1032_);
lean_dec(v_i_1032_);
v_stop_boxed_1037_ = lean_unbox_usize(v_stop_1033_);
lean_dec(v_stop_1033_);
v_res_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_12443__boxed_1035_, v_as_1031_, v_i_boxed_1036_, v_stop_boxed_1037_, v_b_1034_);
lean_dec_ref(v_as_1031_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object* v_spec_x3f_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_elts_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1111_; lean_object* v_cfg_1125_; 
v_cfg_1125_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5));
if (lean_obj_tag(v_spec_x3f_1067_) == 1)
{
lean_object* v_val_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v_val_1126_ = lean_ctor_get(v_spec_x3f_1067_, 0);
lean_inc_n(v_val_1126_, 2);
lean_dec_ref_known(v_spec_x3f_1067_, 1);
v___x_1127_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7));
v___x_1128_ = l_Lean_Syntax_isOfKind(v_val_1126_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_val_1126_);
v___x_1129_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1138_ = lean_unsigned_to_nat(1u);
v___x_1139_ = l_Lean_Syntax_getArg(v_val_1126_, v___x_1138_);
lean_dec(v_val_1126_);
v___x_1140_ = l_Lean_Syntax_getArgs(v___x_1139_);
lean_dec(v___x_1139_);
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8));
v___x_1143_ = lean_array_get_size(v___x_1140_);
v___x_1144_ = lean_nat_dec_lt(v___x_1141_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_dec_ref(v___x_1140_);
v___y_1111_ = v___x_1142_;
goto v___jp_1110_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_box(v___x_1128_);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v___x_1142_);
v___x_1147_ = lean_nat_dec_le(v___x_1143_, v___x_1143_);
if (v___x_1147_ == 0)
{
if (v___x_1144_ == 0)
{
lean_dec_ref_known(v___x_1146_, 2);
lean_dec_ref(v___x_1140_);
v___y_1111_ = v___x_1142_;
goto v___jp_1110_;
}
else
{
size_t v___x_1148_; size_t v___x_1149_; lean_object* v___x_1150_; lean_object* v_snd_1151_; 
v___x_1148_ = ((size_t)0ULL);
v___x_1149_ = lean_usize_of_nat(v___x_1143_);
v___x_1150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1128_, v___x_1140_, v___x_1148_, v___x_1149_, v___x_1146_);
lean_dec_ref(v___x_1140_);
v_snd_1151_ = lean_ctor_get(v___x_1150_, 1);
lean_inc(v_snd_1151_);
lean_dec_ref(v___x_1150_);
v___y_1111_ = v_snd_1151_;
goto v___jp_1110_;
}
}
else
{
size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; lean_object* v_snd_1155_; 
v___x_1152_ = ((size_t)0ULL);
v___x_1153_ = lean_usize_of_nat(v___x_1143_);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1128_, v___x_1140_, v___x_1152_, v___x_1153_, v___x_1146_);
lean_dec_ref(v___x_1140_);
v_snd_1155_ = lean_ctor_get(v___x_1154_, 1);
lean_inc(v_snd_1155_);
lean_dec_ref(v___x_1154_);
v___y_1111_ = v_snd_1155_;
goto v___jp_1110_;
}
}
}
}
else
{
lean_object* v___x_1156_; 
lean_dec(v_spec_x3f_1067_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_cfg_1125_);
return v___x_1156_;
}
v___jp_1071_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; size_t v_sz_1077_; size_t v___x_1078_; lean_object* v___x_1079_; 
v___x_1075_ = l_Array_reverse___redArg(v_elts_1072_);
v___x_1076_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4));
v_sz_1077_ = lean_array_size(v___x_1075_);
v___x_1078_ = ((size_t)0ULL);
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v___x_1075_, v_sz_1077_, v___x_1078_, v___x_1076_, v___y_1073_, v___y_1074_);
lean_dec_ref(v___x_1075_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1101_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1101_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1101_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_snd_1084_; lean_object* v_snd_1085_; lean_object* v_snd_1086_; lean_object* v_fst_1087_; lean_object* v_fst_1088_; lean_object* v_fst_1089_; lean_object* v_fst_1090_; lean_object* v_snd_1091_; lean_object* v___y_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; uint8_t v___x_1095_; uint8_t v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1099_; 
v_snd_1084_ = lean_ctor_get(v_a_1080_, 1);
lean_inc(v_snd_1084_);
v_snd_1085_ = lean_ctor_get(v_snd_1084_, 1);
lean_inc(v_snd_1085_);
v_snd_1086_ = lean_ctor_get(v_snd_1085_, 1);
lean_inc(v_snd_1086_);
v_fst_1087_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_fst_1087_);
lean_dec(v_a_1080_);
v_fst_1088_ = lean_ctor_get(v_snd_1084_, 0);
lean_inc(v_fst_1088_);
lean_dec(v_snd_1084_);
v_fst_1089_ = lean_ctor_get(v_snd_1085_, 0);
lean_inc(v_fst_1089_);
lean_dec(v_snd_1085_);
v_fst_1090_ = lean_ctor_get(v_snd_1086_, 0);
lean_inc(v_fst_1090_);
v_snd_1091_ = lean_ctor_get(v_snd_1086_, 1);
lean_inc(v_snd_1091_);
lean_dec(v_snd_1086_);
v___y_1092_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___y_1092_, 0, v_snd_1091_);
v___x_1093_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1093_, 0, v___y_1092_);
v___x_1094_ = lean_unbox(v_fst_1087_);
lean_dec(v_fst_1087_);
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*1, v___x_1094_);
v___x_1095_ = lean_unbox(v_fst_1088_);
lean_dec(v_fst_1088_);
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*1 + 1, v___x_1095_);
v___x_1096_ = lean_unbox(v_fst_1089_);
lean_dec(v_fst_1089_);
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*1 + 2, v___x_1096_);
v___x_1097_ = lean_unbox(v_fst_1090_);
lean_dec(v_fst_1090_);
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*1 + 3, v___x_1097_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1093_);
v___x_1099_ = v___x_1082_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1093_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_a_1102_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1079_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1079_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
v___jp_1110_:
{
size_t v_sz_1112_; size_t v___x_1113_; lean_object* v___x_1114_; 
v_sz_1112_ = lean_array_size(v___y_1111_);
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_1112_, v___x_1113_, v___y_1111_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v___x_1115_; lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v___x_1115_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
else
{
lean_object* v_val_1124_; 
v_val_1124_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v___x_1114_, 1);
v_elts_1072_ = v_val_1124_;
v___y_1073_ = v_a_1068_;
v___y_1074_ = v_a_1069_;
goto v___jp_1071_;
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
lean_object* v_startInclusive_1200_; lean_object* v_endExclusive_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v_startInclusive_1200_ = lean_ctor_get(v_s_1174_, 1);
v_endExclusive_1201_ = lean_ctor_get(v_s_1174_, 2);
v___x_1202_ = lean_nat_sub(v_endExclusive_1201_, v_startInclusive_1200_);
v___x_1203_ = lean_nat_dec_eq(v_pos_1196_, v___x_1202_);
lean_dec(v___x_1202_);
if (v___x_1203_ == 0)
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
lean_object* v_needle_1222_; lean_object* v_table_1223_; lean_object* v_stackPos_1224_; lean_object* v_needlePos_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1284_; 
v_needle_1222_ = lean_ctor_get(v_a_1176_, 0);
v_table_1223_ = lean_ctor_get(v_a_1176_, 1);
v_stackPos_1224_ = lean_ctor_get(v_a_1176_, 2);
v_needlePos_1225_ = lean_ctor_get(v_a_1176_, 3);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_a_1176_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1227_ = v_a_1176_;
v_isShared_1228_ = v_isSharedCheck_1284_;
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
v_isShared_1228_ = v_isSharedCheck_1284_;
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
uint8_t v___x_1240_; 
lean_dec(v___x_1236_);
lean_del_object(v___x_1227_);
lean_dec(v_needlePos_1225_);
lean_dec(v_stackPos_1224_);
lean_dec_ref(v_table_1223_);
lean_dec_ref(v_needle_1222_);
v___x_1240_ = lean_nat_dec_lt(v_basePos_1235_, v___x_1238_);
if (v___x_1240_ == 0)
{
lean_dec(v___x_1238_);
lean_dec(v_basePos_1235_);
lean_dec_ref(v_s_1174_);
return v_b_1177_;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = l_String_Slice_pos_x21(v_s_1174_, v_basePos_1235_);
lean_dec(v_basePos_1235_);
v___x_1242_ = lean_box(3);
v_it_1179_ = v___x_1242_;
v_startPos_1180_ = v___x_1241_;
v_endPos_1181_ = v___x_1238_;
goto v___jp_1178_;
}
}
else
{
lean_object* v___x_1243_; uint8_t v_stackByte_1244_; lean_object* v___x_1245_; uint8_t v_patByte_1246_; uint8_t v___x_1247_; 
lean_dec(v___x_1238_);
v___x_1243_ = lean_nat_add(v_startInclusive_1233_, v_stackPos_1224_);
v_stackByte_1244_ = lean_string_get_byte_fast(v_str_1232_, v___x_1243_);
v___x_1245_ = lean_nat_add(v_startInclusive_1230_, v_needlePos_1225_);
v_patByte_1246_ = lean_string_get_byte_fast(v_str_1229_, v___x_1245_);
v___x_1247_ = lean_uint8_dec_eq(v_stackByte_1244_, v_patByte_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; uint8_t v___x_1249_; 
lean_dec(v___x_1236_);
v___x_1248_ = lean_unsigned_to_nat(0u);
v___x_1249_ = lean_nat_dec_eq(v_needlePos_1225_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_newNeedlePos_1252_; uint8_t v___x_1253_; 
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_sub(v_needlePos_1225_, v___x_1250_);
lean_dec(v_needlePos_1225_);
v_newNeedlePos_1252_ = lean_array_fget_borrowed(v_table_1223_, v___x_1251_);
lean_dec(v___x_1251_);
v___x_1253_ = lean_nat_dec_eq(v_newNeedlePos_1252_, v___x_1248_);
if (v___x_1253_ == 0)
{
lean_object* v_oldBasePos_1254_; lean_object* v___x_1255_; lean_object* v_newBasePos_1256_; lean_object* v___x_1258_; 
lean_inc(v_newNeedlePos_1252_);
v_oldBasePos_1254_ = l_String_Slice_pos_x21(v_s_1174_, v_basePos_1235_);
lean_dec(v_basePos_1235_);
v___x_1255_ = lean_nat_sub(v_stackPos_1224_, v_newNeedlePos_1252_);
v_newBasePos_1256_ = l_String_Slice_pos_x21(v_s_1174_, v___x_1255_);
lean_dec(v___x_1255_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v_newNeedlePos_1252_);
v___x_1258_ = v___x_1227_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_needle_1222_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_table_1223_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_stackPos_1224_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v_newNeedlePos_1252_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
v_it_1179_ = v___x_1258_;
v_startPos_1180_ = v_oldBasePos_1254_;
v_endPos_1181_ = v_newBasePos_1256_;
goto v___jp_1178_;
}
}
else
{
lean_object* v_basePos_1260_; lean_object* v_nextStackPos_1261_; lean_object* v___x_1263_; 
v_basePos_1260_ = l_String_Slice_pos_x21(v_s_1174_, v_basePos_1235_);
lean_dec(v_basePos_1235_);
v_nextStackPos_1261_ = l_String_Slice_posGE___redArg(v_s_1174_, v_stackPos_1224_);
lean_inc(v_nextStackPos_1261_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v___x_1248_);
lean_ctor_set(v___x_1227_, 2, v_nextStackPos_1261_);
v___x_1263_ = v___x_1227_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_needle_1222_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_table_1223_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_nextStackPos_1261_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v___x_1248_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v_it_1179_ = v___x_1263_;
v_startPos_1180_ = v_basePos_1260_;
v_endPos_1181_ = v_nextStackPos_1261_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v_basePos_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v_nextStackPos_1268_; lean_object* v___x_1270_; 
lean_dec(v_basePos_1235_);
lean_dec(v_needlePos_1225_);
v_basePos_1265_ = l_String_Slice_pos_x21(v_s_1174_, v_stackPos_1224_);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_add(v_stackPos_1224_, v___x_1266_);
lean_dec(v_stackPos_1224_);
v_nextStackPos_1268_ = l_String_Slice_posGE___redArg(v_s_1174_, v___x_1267_);
lean_inc(v_nextStackPos_1268_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v___x_1248_);
lean_ctor_set(v___x_1227_, 2, v_nextStackPos_1268_);
v___x_1270_ = v___x_1227_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_needle_1222_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_table_1223_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_nextStackPos_1268_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v___x_1248_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
v_it_1179_ = v___x_1270_;
v_startPos_1180_ = v_basePos_1265_;
v_endPos_1181_ = v_nextStackPos_1268_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v___x_1272_; lean_object* v_nextStackPos_1273_; lean_object* v_nextNeedlePos_1274_; uint8_t v___x_1275_; 
lean_dec(v_basePos_1235_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1273_ = lean_nat_add(v_stackPos_1224_, v___x_1272_);
lean_dec(v_stackPos_1224_);
v_nextNeedlePos_1274_ = lean_nat_add(v_needlePos_1225_, v___x_1272_);
lean_dec(v_needlePos_1225_);
v___x_1275_ = lean_nat_dec_eq(v_nextNeedlePos_1274_, v___x_1236_);
lean_dec(v___x_1236_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1277_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v_nextNeedlePos_1274_);
lean_ctor_set(v___x_1227_, 2, v_nextStackPos_1273_);
v___x_1277_ = v___x_1227_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_needle_1222_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_table_1223_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_nextStackPos_1273_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v_nextNeedlePos_1274_);
v___x_1277_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
v_a_1176_ = v___x_1277_;
goto _start;
}
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
lean_dec(v_nextNeedlePos_1274_);
v___x_1280_ = lean_unsigned_to_nat(0u);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v___x_1280_);
lean_ctor_set(v___x_1227_, 2, v_nextStackPos_1273_);
v___x_1282_ = v___x_1227_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_needle_1222_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_table_1223_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_nextStackPos_1273_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
v_it_1190_ = v___x_1282_;
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
v___x_1186_ = lean_string_utf8_extract(v_str_1183_, v_startInclusive_1184_, v_endExclusive_1185_);
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
v___x_1193_ = lean_string_utf8_extract(v_replacement_1175_, v___x_1191_, v___x_1192_);
v___x_1194_ = lean_string_append(v_b_1177_, v___x_1193_);
lean_dec_ref(v___x_1193_);
v_a_1176_ = v_it_1190_;
v_b_1177_ = v___x_1194_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg___boxed(lean_object* v_s_1285_, lean_object* v_replacement_1286_, lean_object* v_a_1287_, lean_object* v_b_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1285_, v_replacement_1286_, v_a_1287_, v_b_1288_);
lean_dec_ref(v_replacement_1286_);
return v_res_1289_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1292_ = lean_string_utf8_byte_size(v___x_1291_);
return v___x_1292_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1295_ = lean_nat_dec_eq(v___x_1294_, v___x_1293_);
return v___x_1295_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1296_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1297_);
lean_ctor_set(v___x_1299_, 2, v___x_1296_);
return v___x_1299_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1301_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4);
v___x_1304_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1305_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
lean_ctor_set(v___x_1305_, 2, v___x_1302_);
lean_ctor_set(v___x_1305_, 3, v___x_1302_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object* v_s_1308_, lean_object* v_replacement_1309_){
_start:
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1311_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5);
v___x_1313_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1308_, v_replacement_1309_, v___x_1312_, v___x_1310_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1315_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1308_, v_replacement_1309_, v___x_1314_, v___x_1310_);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___boxed(lean_object* v_s_1316_, lean_object* v_replacement_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1316_, v_replacement_1317_);
lean_dec_ref(v_replacement_1317_);
return v_res_1318_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1321_ = lean_string_utf8_byte_size(v___x_1320_);
return v___x_1321_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1322_ = lean_unsigned_to_nat(0u);
v___x_1323_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1324_ = lean_nat_dec_eq(v___x_1323_, v___x_1322_);
return v___x_1324_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1325_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1326_ = lean_unsigned_to_nat(0u);
v___x_1327_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v___x_1326_);
lean_ctor_set(v___x_1328_, 2, v___x_1325_);
return v___x_1328_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1330_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4);
v___x_1333_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1334_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1332_);
lean_ctor_set(v___x_1334_, 2, v___x_1331_);
lean_ctor_set(v___x_1334_, 3, v___x_1331_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object* v_s_1335_, lean_object* v_replacement_1336_){
_start:
{
lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1338_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5);
v___x_1340_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1335_, v_replacement_1336_, v___x_1339_, v___x_1337_);
return v___x_1340_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1342_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1335_, v_replacement_1336_, v___x_1341_, v___x_1337_);
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object* v_s_1343_, lean_object* v_replacement_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1343_, v_replacement_1344_);
lean_dec_ref(v_replacement_1344_);
return v_res_1345_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1348_ = lean_string_utf8_byte_size(v___x_1347_);
return v___x_1348_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1351_ = lean_nat_dec_eq(v___x_1350_, v___x_1349_);
return v___x_1351_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1352_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v___x_1353_);
lean_ctor_set(v___x_1355_, 2, v___x_1352_);
return v___x_1355_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1357_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1356_);
return v___x_1357_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4);
v___x_1360_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1361_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v___x_1359_);
lean_ctor_set(v___x_1361_, 2, v___x_1358_);
lean_ctor_set(v___x_1361_, 3, v___x_1358_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(lean_object* v_s_1362_, lean_object* v_replacement_1363_){
_start:
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1365_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5);
v___x_1367_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1362_, v_replacement_1363_, v___x_1366_, v___x_1364_);
return v___x_1367_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1369_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1362_, v_replacement_1363_, v___x_1368_, v___x_1364_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___boxed(lean_object* v_s_1370_, lean_object* v_replacement_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1370_, v_replacement_1371_);
lean_dec_ref(v_replacement_1371_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object* v_s_1376_){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0));
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = lean_string_utf8_byte_size(v_s_1376_);
v___x_1380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1380_, 0, v_s_1376_);
lean_ctor_set(v___x_1380_, 1, v___x_1378_);
lean_ctor_set(v___x_1380_, 2, v___x_1379_);
v___x_1381_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1380_, v___x_1377_);
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1));
v___x_1383_ = lean_string_utf8_byte_size(v___x_1381_);
v___x_1384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1381_);
lean_ctor_set(v___x_1384_, 1, v___x_1378_);
lean_ctor_set(v___x_1384_, 2, v___x_1383_);
v___x_1385_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v___x_1384_, v___x_1382_);
v___x_1386_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2));
v___x_1387_ = lean_string_utf8_byte_size(v___x_1385_);
v___x_1388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1385_);
lean_ctor_set(v___x_1388_, 1, v___x_1378_);
lean_ctor_set(v___x_1388_, 2, v___x_1387_);
v___x_1389_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v___x_1388_, v___x_1386_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(lean_object* v_s_1390_, lean_object* v_pattern_1391_, lean_object* v_replacement_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1390_, v_replacement_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___boxed(lean_object* v_s_1394_, lean_object* v_pattern_1395_, lean_object* v_replacement_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(v_s_1394_, v_pattern_1395_, v_replacement_1396_);
lean_dec_ref(v_replacement_1396_);
lean_dec_ref(v_pattern_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(lean_object* v_s_1398_, lean_object* v_pattern_1399_, lean_object* v_replacement_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1398_, v_replacement_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___boxed(lean_object* v_s_1402_, lean_object* v_pattern_1403_, lean_object* v_replacement_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(v_s_1402_, v_pattern_1403_, v_replacement_1404_);
lean_dec_ref(v_replacement_1404_);
lean_dec_ref(v_pattern_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(lean_object* v_s_1406_, lean_object* v_pattern_1407_, lean_object* v_replacement_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1406_, v_replacement_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___boxed(lean_object* v_s_1410_, lean_object* v_pattern_1411_, lean_object* v_replacement_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(v_s_1410_, v_pattern_1411_, v_replacement_1412_);
lean_dec_ref(v_replacement_1412_);
lean_dec_ref(v_pattern_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(lean_object* v_s_1414_, lean_object* v_replacement_1415_, lean_object* v_inst_1416_, lean_object* v_R_1417_, lean_object* v_a_1418_, lean_object* v_b_1419_, lean_object* v_c_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1414_, v_replacement_1415_, v_a_1418_, v_b_1419_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___boxed(lean_object* v_s_1422_, lean_object* v_replacement_1423_, lean_object* v_inst_1424_, lean_object* v_R_1425_, lean_object* v_a_1426_, lean_object* v_b_1427_, lean_object* v_c_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(v_s_1422_, v_replacement_1423_, v_inst_1424_, v_R_1425_, v_a_1426_, v_b_1427_, v_c_1428_);
lean_dec_ref(v_replacement_1423_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object* v_s_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1431_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1433_ = lean_string_utf8_byte_size(v_s_1430_);
v___x_1434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1434_, 0, v_s_1430_);
lean_ctor_set(v___x_1434_, 1, v___x_1432_);
lean_ctor_set(v___x_1434_, 2, v___x_1433_);
v___x_1435_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1434_, v___x_1431_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object* v_s_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0));
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object* v_s_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v_s_1440_);
lean_dec_ref(v_s_1440_);
return v_res_1441_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1444_ = lean_nat_dec_eq(v___x_1443_, v___x_1442_);
return v___x_1444_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1445_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
lean_ctor_set(v___x_1448_, 1, v___x_1446_);
lean_ctor_set(v___x_1448_, 2, v___x_1445_);
return v___x_1448_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1450_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1449_);
return v___x_1450_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2);
v___x_1453_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1454_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v___x_1452_);
lean_ctor_set(v___x_1454_, 2, v___x_1451_);
lean_ctor_set(v___x_1454_, 3, v___x_1451_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object* v_s_1455_, lean_object* v_replacement_1456_){
_start:
{
lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1458_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3);
v___x_1460_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1455_, v_replacement_1456_, v___x_1459_, v___x_1457_);
return v___x_1460_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1462_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1455_, v_replacement_1456_, v___x_1461_, v___x_1457_);
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object* v_s_1463_, lean_object* v_replacement_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1463_, v_replacement_1464_);
lean_dec_ref(v_replacement_1464_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object* v_s_1466_, lean_object* v___x_1467_, lean_object* v___x_1468_, lean_object* v_a_1469_, lean_object* v_b_1470_){
_start:
{
lean_object* v_it_1472_; lean_object* v_startInclusive_1473_; lean_object* v_endExclusive_1474_; 
if (lean_obj_tag(v_a_1469_) == 0)
{
lean_object* v_currPos_1483_; lean_object* v_searcher_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1519_; 
v_currPos_1483_ = lean_ctor_get(v_a_1469_, 0);
v_searcher_1484_ = lean_ctor_get(v_a_1469_, 1);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_a_1469_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1486_ = v_a_1469_;
v_isShared_1487_ = v_isSharedCheck_1519_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_searcher_1484_);
lean_inc(v_currPos_1483_);
lean_dec(v_a_1469_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1519_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
uint8_t v___y_1499_; lean_object* v_startInclusive_1503_; lean_object* v_endExclusive_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v_startInclusive_1503_ = lean_ctor_get(v___x_1467_, 1);
v_endExclusive_1504_ = lean_ctor_get(v___x_1467_, 2);
v___x_1505_ = lean_nat_sub(v_endExclusive_1504_, v_startInclusive_1503_);
v___x_1506_ = lean_nat_dec_eq(v_searcher_1484_, v___x_1505_);
lean_dec(v___x_1505_);
if (v___x_1506_ == 0)
{
uint32_t v___x_1507_; uint8_t v___y_1509_; uint32_t v___x_1514_; uint8_t v___x_1515_; 
v___x_1507_ = lean_string_utf8_get_fast(v_s_1466_, v_searcher_1484_);
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
lean_inc(v___x_1468_);
v_it_1472_ = v___x_1518_;
v_startInclusive_1473_ = v_currPos_1483_;
v_endExclusive_1474_ = v___x_1468_;
goto v___jp_1471_;
}
v___jp_1488_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v_slice_1492_; lean_object* v_nextIt_1494_; 
v___x_1489_ = lean_string_utf8_next_fast(v_s_1466_, v_searcher_1484_);
v___x_1490_ = lean_nat_sub(v___x_1489_, v_searcher_1484_);
v___x_1491_ = lean_nat_add(v_searcher_1484_, v___x_1490_);
lean_dec(v___x_1490_);
v_slice_1492_ = l_String_Slice_subslice_x21(v___x_1467_, v_currPos_1483_, v_searcher_1484_);
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
v_it_1472_ = v_nextIt_1494_;
v_startInclusive_1473_ = v_startInclusive_1495_;
v_endExclusive_1474_ = v_endExclusive_1496_;
goto v___jp_1471_;
}
}
v___jp_1498_:
{
if (v___y_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_del_object(v___x_1486_);
v___x_1500_ = lean_string_utf8_next_fast(v_s_1466_, v_searcher_1484_);
lean_dec(v_searcher_1484_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_currPos_1483_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v_a_1469_ = v___x_1501_;
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
lean_dec(v___x_1468_);
lean_dec_ref(v_s_1466_);
return v_b_1470_;
}
v___jp_1471_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1475_ = lean_nat_sub(v_endExclusive_1474_, v_startInclusive_1473_);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_nat_dec_eq(v___x_1475_, v___x_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_bool_not(v___x_1477_);
if (v___x_1478_ == 0)
{
lean_dec(v_endExclusive_1474_);
lean_dec(v_startInclusive_1473_);
v_a_1469_ = v_it_1472_;
goto _start;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_inc_ref(v_s_1466_);
v___x_1480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1480_, 0, v_s_1466_);
lean_ctor_set(v___x_1480_, 1, v_startInclusive_1473_);
lean_ctor_set(v___x_1480_, 2, v_endExclusive_1474_);
v___x_1481_ = lean_array_push(v_b_1470_, v___x_1480_);
v_a_1469_ = v_it_1472_;
v_b_1470_ = v___x_1481_;
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
lean_dec_ref_known(v___x_1544_, 3);
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
lean_object* v_fileName_1764_; lean_object* v_fileMap_1765_; lean_object* v_currRecDepth_1766_; lean_object* v_cmdPos_1767_; lean_object* v_macroStack_1768_; lean_object* v_quotContext_x3f_1769_; lean_object* v_currMacroScope_1770_; lean_object* v_ref_1771_; lean_object* v_cancelTk_x3f_1772_; uint8_t v_suppressElabErrors_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
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
v___x_1774_ = lean_unsigned_to_nat(0u);
v___x_1775_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
v___x_1776_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1772_);
lean_inc(v_ref_1771_);
lean_inc(v_currMacroScope_1770_);
lean_inc(v_quotContext_x3f_1769_);
lean_inc(v_macroStack_1768_);
lean_inc(v_cmdPos_1767_);
lean_inc(v_currRecDepth_1766_);
lean_inc_ref(v_fileMap_1765_);
lean_inc_ref(v_fileName_1764_);
v___x_1777_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1777_, 0, v_fileName_1764_);
lean_ctor_set(v___x_1777_, 1, v_fileMap_1765_);
lean_ctor_set(v___x_1777_, 2, v_currRecDepth_1766_);
lean_ctor_set(v___x_1777_, 3, v_cmdPos_1767_);
lean_ctor_set(v___x_1777_, 4, v_macroStack_1768_);
lean_ctor_set(v___x_1777_, 5, v_quotContext_x3f_1769_);
lean_ctor_set(v___x_1777_, 6, v_currMacroScope_1770_);
lean_ctor_set(v___x_1777_, 7, v_ref_1771_);
lean_ctor_set(v___x_1777_, 8, v___x_1776_);
lean_ctor_set(v___x_1777_, 9, v_cancelTk_x3f_1772_);
lean_ctor_set_uint8(v___x_1777_, sizeof(void*)*10, v_suppressElabErrors_1773_);
v___x_1778_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1760_, v___x_1775_, v___x_1777_, v_a_1762_);
lean_dec_ref_known(v___x_1777_, 10);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1822_; 
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v___x_1778_, 0);
lean_dec(v_unused_1823_);
v___x_1780_ = v___x_1778_;
v_isShared_1781_ = v_isSharedCheck_1822_;
goto v_resetjp_1779_;
}
else
{
lean_dec(v___x_1778_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1822_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_messages_1784_; lean_object* v___y_1786_; lean_object* v_snapshotTasks_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1782_ = lean_st_ref_get(v_a_1762_);
v___x_1783_ = lean_st_ref_get(v_a_1762_);
v_messages_1784_ = lean_ctor_get(v___x_1782_, 1);
lean_inc_ref(v_messages_1784_);
lean_dec(v___x_1782_);
v_snapshotTasks_1811_ = lean_ctor_get(v___x_1783_, 10);
lean_inc_ref(v_snapshotTasks_1811_);
lean_dec(v___x_1783_);
v___x_1812_ = l_Lean_MessageLog_empty;
v___x_1813_ = lean_array_get_size(v_snapshotTasks_1811_);
v___x_1814_ = lean_nat_dec_lt(v___x_1774_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_dec_ref(v_snapshotTasks_1811_);
v___y_1786_ = v___x_1812_;
goto v___jp_1785_;
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_nat_dec_le(v___x_1813_, v___x_1813_);
if (v___x_1815_ == 0)
{
if (v___x_1814_ == 0)
{
lean_dec_ref(v_snapshotTasks_1811_);
v___y_1786_ = v___x_1812_;
goto v___jp_1785_;
}
else
{
size_t v___x_1816_; size_t v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = lean_usize_of_nat(v___x_1813_);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1811_, v___x_1816_, v___x_1817_, v___x_1812_);
lean_dec_ref(v_snapshotTasks_1811_);
v___y_1786_ = v___x_1818_;
goto v___jp_1785_;
}
}
else
{
size_t v___x_1819_; size_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = ((size_t)0ULL);
v___x_1820_ = lean_usize_of_nat(v___x_1813_);
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1811_, v___x_1819_, v___x_1820_, v___x_1812_);
lean_dec_ref(v_snapshotTasks_1811_);
v___y_1786_ = v___x_1821_;
goto v___jp_1785_;
}
}
v___jp_1785_:
{
lean_object* v___x_1787_; lean_object* v_env_1788_; lean_object* v_messages_1789_; lean_object* v_scopes_1790_; lean_object* v_usedQuotCtxts_1791_; lean_object* v_nextMacroScope_1792_; lean_object* v_maxRecDepth_1793_; lean_object* v_ngen_1794_; lean_object* v_auxDeclNGen_1795_; lean_object* v_infoState_1796_; lean_object* v_traceState_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1809_; 
v___x_1787_ = lean_st_ref_take(v_a_1762_);
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
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v___x_1787_, 10);
lean_dec(v_unused_1810_);
v___x_1799_ = v___x_1787_;
v_isShared_1800_ = v_isSharedCheck_1809_;
goto v_resetjp_1798_;
}
else
{
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
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1809_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 10, v___x_1775_);
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_env_1788_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_messages_1789_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_scopes_1790_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_usedQuotCtxts_1791_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_nextMacroScope_1792_);
lean_ctor_set(v_reuseFailAlloc_1808_, 5, v_maxRecDepth_1793_);
lean_ctor_set(v_reuseFailAlloc_1808_, 6, v_ngen_1794_);
lean_ctor_set(v_reuseFailAlloc_1808_, 7, v_auxDeclNGen_1795_);
lean_ctor_set(v_reuseFailAlloc_1808_, 8, v_infoState_1796_);
lean_ctor_set(v_reuseFailAlloc_1808_, 9, v_traceState_1797_);
lean_ctor_set(v_reuseFailAlloc_1808_, 10, v___x_1775_);
v___x_1802_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1803_ = lean_st_ref_set(v_a_1762_, v___x_1802_);
v___x_1804_ = l_Lean_MessageLog_append(v_messages_1784_, v___y_1786_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1804_);
v___x_1806_ = v___x_1780_;
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
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1778_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1778_);
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
lean_dec_ref_known(v___x_1842_, 1);
if (lean_obj_tag(v_val_1844_) == 1)
{
uint8_t v_v_1845_; 
v_v_1845_ = lean_ctor_get_uint8(v_val_1844_, 0);
lean_dec_ref_known(v_val_1844_, 0);
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
lean_object* v___x_1899_; lean_object* v_scopes_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v_opts_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; uint8_t v___x_1906_; 
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
v___x_1906_ = lean_bool_not(v___x_1905_);
if (v___x_1906_ == 0)
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
else
{
lean_object* v___x_1926_; 
lean_dec(v_macroStack_1896_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_msgData_1895_);
return v___x_1926_;
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
lean_dec_ref_known(v___x_1974_, 1);
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
lean_dec_ref_known(v___x_2008_, 1);
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
lean_dec_ref_known(v___x_2021_, 10);
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
lean_dec_ref_known(v___x_2062_, 2);
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
lean_dec_ref_known(v_kind_2064_, 2);
v_str_2070_ = lean_ctor_get(v_pre_2065_, 1);
lean_inc_ref(v_str_2070_);
lean_dec_ref_known(v_pre_2065_, 2);
v_str_2071_ = lean_ctor_get(v_pre_2066_, 1);
lean_inc_ref(v_str_2071_);
lean_dec_ref_known(v_pre_2066_, 2);
v_str_2072_ = lean_ctor_get(v_pre_2067_, 1);
lean_inc_ref(v_str_2072_);
lean_dec_ref_known(v_pre_2067_, 2);
v___x_2073_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_2074_ = lean_string_dec_eq(v_str_2072_, v___x_2073_);
lean_dec_ref(v_str_2072_);
if (v___x_2074_ == 0)
{
lean_dec_ref(v_str_2071_);
lean_dec_ref(v_str_2070_);
lean_dec_ref(v_str_2069_);
lean_dec_ref_known(v___x_2062_, 3);
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
lean_dec_ref_known(v___x_2062_, 3);
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
lean_dec_ref_known(v___x_2062_, 3);
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
lean_dec_ref_known(v___x_2062_, 3);
goto v___jp_2047_;
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = l_Lean_Syntax_getArg(v___x_2062_, v___x_2081_);
lean_dec_ref_known(v___x_2062_, 3);
if (lean_obj_tag(v___x_2082_) == 2)
{
lean_object* v_val_2083_; 
lean_dec(v_stx_2043_);
v_val_2083_ = lean_ctor_get(v___x_2082_, 1);
lean_inc_ref(v_val_2083_);
lean_dec_ref_known(v___x_2082_, 2);
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
lean_dec_ref_known(v_pre_2067_, 2);
lean_dec_ref_known(v_pre_2066_, 2);
lean_dec_ref_known(v_pre_2065_, 2);
lean_dec_ref_known(v_kind_2064_, 2);
lean_dec_ref_known(v___x_2062_, 3);
goto v___jp_2047_;
}
}
else
{
lean_dec(v_pre_2067_);
lean_dec_ref_known(v_pre_2066_, 2);
lean_dec_ref_known(v_pre_2065_, 2);
lean_dec_ref_known(v_kind_2064_, 2);
lean_dec_ref_known(v___x_2062_, 3);
goto v___jp_2047_;
}
}
else
{
lean_dec_ref_known(v_pre_2065_, 2);
lean_dec(v_pre_2066_);
lean_dec_ref_known(v_kind_2064_, 2);
lean_dec_ref_known(v___x_2062_, 3);
goto v___jp_2047_;
}
}
else
{
lean_dec(v_pre_2065_);
lean_dec_ref_known(v_kind_2064_, 2);
lean_dec_ref_known(v___x_2062_, 3);
goto v___jp_2047_;
}
}
else
{
lean_dec(v_kind_2064_);
lean_dec_ref_known(v___x_2062_, 3);
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
lean_dec_ref_known(v_a_2183_, 1);
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
uint8_t v___y_29312__boxed_2291_; uint8_t v_suppressElabErrors_boxed_2292_; uint8_t v_res_2293_; lean_object* v_r_2294_; 
v___y_29312__boxed_2291_ = lean_unbox(v___y_2288_);
v_suppressElabErrors_boxed_2292_ = lean_unbox(v_suppressElabErrors_2289_);
v_res_2293_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v___y_29312__boxed_2291_, v_suppressElabErrors_boxed_2292_, v_x_2290_);
lean_dec(v_x_2290_);
v_r_2294_ = lean_box(v_res_2293_);
return v_r_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2295_, lean_object* v_msgData_2296_, uint8_t v_severity_2297_, uint8_t v_isSilent_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___y_2303_; lean_object* v___y_2304_; uint8_t v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; uint8_t v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; uint8_t v___y_2366_; uint8_t v___y_2367_; uint8_t v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; uint8_t v___y_2394_; uint8_t v___y_2395_; lean_object* v___y_2396_; uint8_t v___y_2397_; lean_object* v___y_2398_; uint8_t v___y_2402_; uint8_t v___y_2403_; uint8_t v___y_2404_; uint8_t v___x_2419_; uint8_t v___y_2421_; uint8_t v___y_2422_; uint8_t v___y_2423_; uint8_t v___y_2425_; uint8_t v___x_2437_; 
v___x_2419_ = 2;
v___x_2437_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2297_, v___x_2419_);
if (v___x_2437_ == 0)
{
v___y_2425_ = v___x_2437_;
goto v___jp_2424_;
}
else
{
uint8_t v___x_2438_; 
lean_inc_ref(v_msgData_2296_);
v___x_2438_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2296_);
v___y_2425_ = v___x_2438_;
goto v___jp_2424_;
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
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = l_Lean_Elab_Command_getScope___redArg(v___y_2310_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2348_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2348_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2348_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v_currNamespace_2319_; lean_object* v_openDecls_2320_; lean_object* v_env_2321_; lean_object* v_messages_2322_; lean_object* v_scopes_2323_; lean_object* v_usedQuotCtxts_2324_; lean_object* v_nextMacroScope_2325_; lean_object* v_maxRecDepth_2326_; lean_object* v_ngen_2327_; lean_object* v_auxDeclNGen_2328_; lean_object* v_infoState_2329_; lean_object* v_traceState_2330_; lean_object* v_snapshotTasks_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2347_; 
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
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2333_ = v___x_2318_;
v_isShared_2334_ = v_isSharedCheck_2347_;
goto v_resetjp_2332_;
}
else
{
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
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2347_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v_currNamespace_2319_);
lean_ctor_set(v___x_2335_, 1, v_openDecls_2320_);
v___x_2336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
lean_ctor_set(v___x_2336_, 1, v___y_2306_);
lean_inc_ref(v___y_2307_);
lean_inc_ref(v___y_2304_);
v___x_2337_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2337_, 0, v___y_2304_);
lean_ctor_set(v___x_2337_, 1, v___y_2309_);
lean_ctor_set(v___x_2337_, 2, v___y_2303_);
lean_ctor_set(v___x_2337_, 3, v___y_2307_);
lean_ctor_set(v___x_2337_, 4, v___x_2336_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*5, v___y_2305_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*5 + 1, v___y_2308_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*5 + 2, v_isSilent_2298_);
v___x_2338_ = l_Lean_MessageLog_add(v___x_2337_, v_messages_2322_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 1, v___x_2338_);
v___x_2340_ = v___x_2333_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_env_2321_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_scopes_2323_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_usedQuotCtxts_2324_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_nextMacroScope_2325_);
lean_ctor_set(v_reuseFailAlloc_2346_, 5, v_maxRecDepth_2326_);
lean_ctor_set(v_reuseFailAlloc_2346_, 6, v_ngen_2327_);
lean_ctor_set(v_reuseFailAlloc_2346_, 7, v_auxDeclNGen_2328_);
lean_ctor_set(v_reuseFailAlloc_2346_, 8, v_infoState_2329_);
lean_ctor_set(v_reuseFailAlloc_2346_, 9, v_traceState_2330_);
lean_ctor_set(v_reuseFailAlloc_2346_, 10, v_snapshotTasks_2331_);
v___x_2340_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2341_ = lean_st_ref_set(v___y_2310_, v___x_2340_);
v___x_2342_ = lean_box(0);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2342_);
v___x_2344_ = v___x_2316_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_a_2312_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2303_);
v_a_2349_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2313_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2313_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref(v___y_2309_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2303_);
v_a_2357_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2311_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2311_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
v___jp_2365_:
{
lean_object* v_fileName_2371_; lean_object* v_fileMap_2372_; uint8_t v_suppressElabErrors_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2392_; 
v_fileName_2371_ = lean_ctor_get(v___y_2299_, 0);
v_fileMap_2372_ = lean_ctor_get(v___y_2299_, 1);
v_suppressElabErrors_2373_ = lean_ctor_get_uint8(v___y_2299_, sizeof(void*)*10);
v___x_2374_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2296_);
v___x_2375_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2374_, v___y_2300_);
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2392_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2392_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_inc_ref_n(v_fileMap_2372_, 2);
v___x_2380_ = l_Lean_FileMap_toPosition(v_fileMap_2372_, v___y_2369_);
lean_dec(v___y_2369_);
v___x_2381_ = l_Lean_FileMap_toPosition(v_fileMap_2372_, v___y_2370_);
lean_dec(v___y_2370_);
v___x_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
v___x_2383_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
if (v_suppressElabErrors_2373_ == 0)
{
lean_del_object(v___x_2378_);
v___y_2303_ = v___x_2382_;
v___y_2304_ = v_fileName_2371_;
v___y_2305_ = v___y_2367_;
v___y_2306_ = v_a_2376_;
v___y_2307_ = v___x_2383_;
v___y_2308_ = v___y_2368_;
v___y_2309_ = v___x_2380_;
v___y_2310_ = v___y_2300_;
goto v___jp_2302_;
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___f_2386_; uint8_t v___x_2387_; 
v___x_2384_ = lean_box(v___y_2366_);
v___x_2385_ = lean_box(v_suppressElabErrors_2373_);
v___f_2386_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2386_, 0, v___x_2384_);
lean_closure_set(v___f_2386_, 1, v___x_2385_);
lean_inc(v_a_2376_);
v___x_2387_ = l_Lean_MessageData_hasTag(v___f_2386_, v_a_2376_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2390_; 
lean_dec_ref_known(v___x_2382_, 1);
lean_dec_ref(v___x_2380_);
lean_dec(v_a_2376_);
v___x_2388_ = lean_box(0);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2388_);
v___x_2390_ = v___x_2378_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
else
{
lean_del_object(v___x_2378_);
v___y_2303_ = v___x_2382_;
v___y_2304_ = v_fileName_2371_;
v___y_2305_ = v___y_2367_;
v___y_2306_ = v_a_2376_;
v___y_2307_ = v___x_2383_;
v___y_2308_ = v___y_2368_;
v___y_2309_ = v___x_2380_;
v___y_2310_ = v___y_2300_;
goto v___jp_2302_;
}
}
}
}
v___jp_2393_:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_Syntax_getTailPos_x3f(v___y_2396_, v___y_2395_);
lean_dec(v___y_2396_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_inc(v___y_2398_);
v___y_2366_ = v___y_2394_;
v___y_2367_ = v___y_2395_;
v___y_2368_ = v___y_2397_;
v___y_2369_ = v___y_2398_;
v___y_2370_ = v___y_2398_;
goto v___jp_2365_;
}
else
{
lean_object* v_val_2400_; 
v_val_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_val_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v___y_2366_ = v___y_2394_;
v___y_2367_ = v___y_2395_;
v___y_2368_ = v___y_2397_;
v___y_2369_ = v___y_2398_;
v___y_2370_ = v_val_2400_;
goto v___jp_2365_;
}
}
v___jp_2401_:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_Elab_Command_getRef___redArg(v___y_2299_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v_ref_2407_; lean_object* v___x_2408_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v_ref_2407_ = l_Lean_replaceRef(v_ref_2295_, v_a_2406_);
lean_dec(v_a_2406_);
v___x_2408_ = l_Lean_Syntax_getPos_x3f(v_ref_2407_, v___y_2403_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_unsigned_to_nat(0u);
v___y_2394_ = v___y_2402_;
v___y_2395_ = v___y_2403_;
v___y_2396_ = v_ref_2407_;
v___y_2397_ = v___y_2404_;
v___y_2398_ = v___x_2409_;
goto v___jp_2393_;
}
else
{
lean_object* v_val_2410_; 
v_val_2410_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_val_2410_);
lean_dec_ref_known(v___x_2408_, 1);
v___y_2394_ = v___y_2402_;
v___y_2395_ = v___y_2403_;
v___y_2396_ = v_ref_2407_;
v___y_2397_ = v___y_2404_;
v___y_2398_ = v_val_2410_;
goto v___jp_2393_;
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec_ref(v_msgData_2296_);
v_a_2411_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2405_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2405_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
v___jp_2420_:
{
if (v___y_2423_ == 0)
{
v___y_2402_ = v___y_2421_;
v___y_2403_ = v___y_2422_;
v___y_2404_ = v_severity_2297_;
goto v___jp_2401_;
}
else
{
v___y_2402_ = v___y_2421_;
v___y_2403_ = v___y_2422_;
v___y_2404_ = v___x_2419_;
goto v___jp_2401_;
}
}
v___jp_2424_:
{
if (v___y_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v_scopes_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v_opts_2430_; uint8_t v___x_2431_; uint8_t v___x_2432_; 
v___x_2426_ = lean_st_ref_get(v___y_2300_);
v_scopes_2427_ = lean_ctor_get(v___x_2426_, 2);
lean_inc(v_scopes_2427_);
lean_dec(v___x_2426_);
v___x_2428_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2429_ = l_List_head_x21___redArg(v___x_2428_, v_scopes_2427_);
lean_dec(v_scopes_2427_);
v_opts_2430_ = lean_ctor_get(v___x_2429_, 1);
lean_inc_ref(v_opts_2430_);
lean_dec(v___x_2429_);
v___x_2431_ = 1;
v___x_2432_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2297_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_dec_ref(v_opts_2430_);
v___y_2421_ = v___y_2425_;
v___y_2422_ = v___y_2425_;
v___y_2423_ = v___x_2432_;
goto v___jp_2420_;
}
else
{
lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2433_ = l_Lean_warningAsError;
v___x_2434_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2430_, v___x_2433_);
lean_dec_ref(v_opts_2430_);
v___y_2421_ = v___y_2425_;
v___y_2422_ = v___y_2425_;
v___y_2423_ = v___x_2434_;
goto v___jp_2420_;
}
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec_ref(v_msgData_2296_);
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
return v___x_2436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2439_, lean_object* v_msgData_2440_, lean_object* v_severity_2441_, lean_object* v_isSilent_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
uint8_t v_severity_boxed_2446_; uint8_t v_isSilent_boxed_2447_; lean_object* v_res_2448_; 
v_severity_boxed_2446_ = lean_unbox(v_severity_2441_);
v_isSilent_boxed_2447_ = lean_unbox(v_isSilent_2442_);
v_res_2448_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2439_, v_msgData_2440_, v_severity_boxed_2446_, v_isSilent_boxed_2447_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v_ref_2439_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2449_, lean_object* v_msgData_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
uint8_t v___x_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; 
v___x_2454_ = 2;
v___x_2455_ = 0;
v___x_2456_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2449_, v_msgData_2450_, v___x_2454_, v___x_2455_, v___y_2451_, v___y_2452_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2457_, lean_object* v_msgData_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2457_, v_msgData_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v_ref_2457_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2463_, lean_object* v___x_2464_, lean_object* v___x_2465_, lean_object* v_a_2466_, lean_object* v_b_2467_){
_start:
{
lean_object* v_it_2469_; lean_object* v_startInclusive_2470_; lean_object* v_endExclusive_2471_; 
if (lean_obj_tag(v_a_2466_) == 0)
{
lean_object* v_currPos_2476_; lean_object* v_searcher_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2506_; 
v_currPos_2476_ = lean_ctor_get(v_a_2466_, 0);
v_searcher_2477_ = lean_ctor_get(v_a_2466_, 1);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_a_2466_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2479_ = v_a_2466_;
v_isShared_2480_ = v_isSharedCheck_2506_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_searcher_2477_);
lean_inc(v_currPos_2476_);
lean_dec(v_a_2466_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2506_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v_str_2481_; lean_object* v_startInclusive_2482_; lean_object* v_endExclusive_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
v_str_2481_ = lean_ctor_get(v___x_2464_, 0);
v_startInclusive_2482_ = lean_ctor_get(v___x_2464_, 1);
v_endExclusive_2483_ = lean_ctor_get(v___x_2464_, 2);
v___x_2484_ = lean_nat_sub(v_endExclusive_2483_, v_startInclusive_2482_);
v___x_2485_ = lean_nat_dec_eq(v_searcher_2477_, v___x_2484_);
lean_dec(v___x_2484_);
if (v___x_2485_ == 0)
{
uint32_t v___x_2486_; lean_object* v___x_2487_; uint32_t v___x_2488_; uint8_t v___x_2489_; 
v___x_2486_ = 10;
v___x_2487_ = lean_nat_add(v_startInclusive_2482_, v_searcher_2477_);
v___x_2488_ = lean_string_utf8_get_fast(v_str_2481_, v___x_2487_);
v___x_2489_ = lean_uint32_dec_eq(v___x_2488_, v___x_2486_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_dec(v_searcher_2477_);
v___x_2490_ = lean_string_utf8_next_fast(v_str_2481_, v___x_2487_);
lean_dec(v___x_2487_);
v___x_2491_ = lean_nat_sub(v___x_2490_, v_startInclusive_2482_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___x_2491_);
v___x_2493_ = v___x_2479_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_currPos_2476_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
v_a_2466_ = v___x_2493_;
goto _start;
}
}
else
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v_slice_2499_; lean_object* v_nextIt_2501_; 
v___x_2496_ = lean_string_utf8_next_fast(v_str_2481_, v___x_2487_);
v___x_2497_ = lean_nat_sub(v___x_2496_, v___x_2487_);
lean_dec(v___x_2487_);
v___x_2498_ = lean_nat_add(v_searcher_2477_, v___x_2497_);
lean_dec(v___x_2497_);
v_slice_2499_ = l_String_Slice_subslice_x21(v___x_2464_, v_currPos_2476_, v_searcher_2477_);
lean_inc(v___x_2498_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___x_2498_);
lean_ctor_set(v___x_2479_, 0, v___x_2498_);
v_nextIt_2501_ = v___x_2479_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v___x_2498_);
v_nextIt_2501_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v_startInclusive_2502_; lean_object* v_endExclusive_2503_; 
v_startInclusive_2502_ = lean_ctor_get(v_slice_2499_, 0);
lean_inc(v_startInclusive_2502_);
v_endExclusive_2503_ = lean_ctor_get(v_slice_2499_, 1);
lean_inc(v_endExclusive_2503_);
lean_dec_ref(v_slice_2499_);
v_it_2469_ = v_nextIt_2501_;
v_startInclusive_2470_ = v_startInclusive_2502_;
v_endExclusive_2471_ = v_endExclusive_2503_;
goto v___jp_2468_;
}
}
}
else
{
lean_object* v___x_2505_; 
lean_del_object(v___x_2479_);
lean_dec(v_searcher_2477_);
v___x_2505_ = lean_box(1);
lean_inc(v___x_2465_);
v_it_2469_ = v___x_2505_;
v_startInclusive_2470_ = v_currPos_2476_;
v_endExclusive_2471_ = v___x_2465_;
goto v___jp_2468_;
}
}
}
else
{
lean_dec(v___x_2465_);
lean_dec_ref(v___x_2463_);
return v_b_2467_;
}
v___jp_2468_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_inc_ref(v___x_2463_);
v___x_2472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2463_);
lean_ctor_set(v___x_2472_, 1, v_startInclusive_2470_);
lean_ctor_set(v___x_2472_, 2, v_endExclusive_2471_);
v___x_2473_ = l_String_Slice_toString(v___x_2472_);
lean_dec_ref_known(v___x_2472_, 3);
v___x_2474_ = lean_array_push(v_b_2467_, v___x_2473_);
v_a_2466_ = v_it_2469_;
v_b_2467_ = v___x_2474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2507_, lean_object* v___x_2508_, lean_object* v___x_2509_, lean_object* v_a_2510_, lean_object* v_b_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2507_, v___x_2508_, v___x_2509_, v_a_2510_, v_b_2511_);
lean_dec_ref(v___x_2508_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2513_, lean_object* v___x_2514_, lean_object* v___x_2515_, lean_object* v_a_2516_, lean_object* v_b_2517_){
_start:
{
lean_object* v_it_2519_; lean_object* v_startInclusive_2520_; lean_object* v_endExclusive_2521_; 
if (lean_obj_tag(v_a_2516_) == 0)
{
lean_object* v_currPos_2526_; lean_object* v_searcher_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2556_; 
v_currPos_2526_ = lean_ctor_get(v_a_2516_, 0);
v_searcher_2527_ = lean_ctor_get(v_a_2516_, 1);
v_isSharedCheck_2556_ = !lean_is_exclusive(v_a_2516_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2529_ = v_a_2516_;
v_isShared_2530_ = v_isSharedCheck_2556_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_searcher_2527_);
lean_inc(v_currPos_2526_);
lean_dec(v_a_2516_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2556_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v_str_2531_; lean_object* v_startInclusive_2532_; lean_object* v_endExclusive_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v_str_2531_ = lean_ctor_get(v___x_2514_, 0);
v_startInclusive_2532_ = lean_ctor_get(v___x_2514_, 1);
v_endExclusive_2533_ = lean_ctor_get(v___x_2514_, 2);
v___x_2534_ = lean_nat_sub(v_endExclusive_2533_, v_startInclusive_2532_);
v___x_2535_ = lean_nat_dec_eq(v_searcher_2527_, v___x_2534_);
lean_dec(v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; uint32_t v___x_2537_; uint32_t v___x_2538_; uint8_t v___x_2539_; 
v___x_2536_ = lean_nat_add(v_startInclusive_2532_, v_searcher_2527_);
v___x_2537_ = lean_string_utf8_get_fast(v_str_2531_, v___x_2536_);
v___x_2538_ = 10;
v___x_2539_ = lean_uint32_dec_eq(v___x_2537_, v___x_2538_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2543_; 
lean_dec(v_searcher_2527_);
v___x_2540_ = lean_string_utf8_next_fast(v_str_2531_, v___x_2536_);
lean_dec(v___x_2536_);
v___x_2541_ = lean_nat_sub(v___x_2540_, v_startInclusive_2532_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v___x_2541_);
v___x_2543_ = v___x_2529_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_currPos_2526_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2544_; 
v___x_2544_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2513_, v___x_2514_, v___x_2515_, v___x_2543_, v_b_2517_);
return v___x_2544_;
}
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v_slice_2549_; lean_object* v_nextIt_2551_; 
v___x_2546_ = lean_string_utf8_next_fast(v_str_2531_, v___x_2536_);
v___x_2547_ = lean_nat_sub(v___x_2546_, v___x_2536_);
lean_dec(v___x_2536_);
v___x_2548_ = lean_nat_add(v_searcher_2527_, v___x_2547_);
lean_dec(v___x_2547_);
v_slice_2549_ = l_String_Slice_subslice_x21(v___x_2514_, v_currPos_2526_, v_searcher_2527_);
lean_inc(v___x_2548_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v___x_2548_);
lean_ctor_set(v___x_2529_, 0, v___x_2548_);
v_nextIt_2551_ = v___x_2529_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v___x_2548_);
v_nextIt_2551_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v_startInclusive_2552_; lean_object* v_endExclusive_2553_; 
v_startInclusive_2552_ = lean_ctor_get(v_slice_2549_, 0);
lean_inc(v_startInclusive_2552_);
v_endExclusive_2553_ = lean_ctor_get(v_slice_2549_, 1);
lean_inc(v_endExclusive_2553_);
lean_dec_ref(v_slice_2549_);
v_it_2519_ = v_nextIt_2551_;
v_startInclusive_2520_ = v_startInclusive_2552_;
v_endExclusive_2521_ = v_endExclusive_2553_;
goto v___jp_2518_;
}
}
}
else
{
lean_object* v___x_2555_; 
lean_del_object(v___x_2529_);
lean_dec(v_searcher_2527_);
v___x_2555_ = lean_box(1);
lean_inc(v___x_2515_);
v_it_2519_ = v___x_2555_;
v_startInclusive_2520_ = v_currPos_2526_;
v_endExclusive_2521_ = v___x_2515_;
goto v___jp_2518_;
}
}
}
else
{
lean_dec(v___x_2515_);
lean_dec_ref(v___x_2513_);
return v_b_2517_;
}
v___jp_2518_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_inc_ref(v___x_2513_);
v___x_2522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2513_);
lean_ctor_set(v___x_2522_, 1, v_startInclusive_2520_);
lean_ctor_set(v___x_2522_, 2, v_endExclusive_2521_);
v___x_2523_ = l_String_Slice_toString(v___x_2522_);
lean_dec_ref_known(v___x_2522_, 3);
v___x_2524_ = lean_array_push(v_b_2517_, v___x_2523_);
v___x_2525_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2513_, v___x_2514_, v___x_2515_, v_it_2519_, v___x_2524_);
return v___x_2525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2557_, lean_object* v___x_2558_, lean_object* v___x_2559_, lean_object* v_a_2560_, lean_object* v_b_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2557_, v___x_2558_, v___x_2559_, v_a_2560_, v_b_2561_);
lean_dec_ref(v___x_2558_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; lean_object* v_infoState_2567_; uint8_t v_enabled_2568_; 
v___x_2566_ = lean_st_ref_get(v___y_2564_);
v_infoState_2567_ = lean_ctor_get(v___x_2566_, 8);
lean_inc_ref(v_infoState_2567_);
lean_dec(v___x_2566_);
v_enabled_2568_ = lean_ctor_get_uint8(v_infoState_2567_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2567_);
if (v_enabled_2568_ == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
lean_dec_ref(v_t_2563_);
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
return v___x_2570_;
}
else
{
lean_object* v___x_2571_; lean_object* v_infoState_2572_; lean_object* v_env_2573_; lean_object* v_messages_2574_; lean_object* v_scopes_2575_; lean_object* v_usedQuotCtxts_2576_; lean_object* v_nextMacroScope_2577_; lean_object* v_maxRecDepth_2578_; lean_object* v_ngen_2579_; lean_object* v_auxDeclNGen_2580_; lean_object* v_traceState_2581_; lean_object* v_snapshotTasks_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2604_; 
v___x_2571_ = lean_st_ref_take(v___y_2564_);
v_infoState_2572_ = lean_ctor_get(v___x_2571_, 8);
v_env_2573_ = lean_ctor_get(v___x_2571_, 0);
v_messages_2574_ = lean_ctor_get(v___x_2571_, 1);
v_scopes_2575_ = lean_ctor_get(v___x_2571_, 2);
v_usedQuotCtxts_2576_ = lean_ctor_get(v___x_2571_, 3);
v_nextMacroScope_2577_ = lean_ctor_get(v___x_2571_, 4);
v_maxRecDepth_2578_ = lean_ctor_get(v___x_2571_, 5);
v_ngen_2579_ = lean_ctor_get(v___x_2571_, 6);
v_auxDeclNGen_2580_ = lean_ctor_get(v___x_2571_, 7);
v_traceState_2581_ = lean_ctor_get(v___x_2571_, 9);
v_snapshotTasks_2582_ = lean_ctor_get(v___x_2571_, 10);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2584_ = v___x_2571_;
v_isShared_2585_ = v_isSharedCheck_2604_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_snapshotTasks_2582_);
lean_inc(v_traceState_2581_);
lean_inc(v_infoState_2572_);
lean_inc(v_auxDeclNGen_2580_);
lean_inc(v_ngen_2579_);
lean_inc(v_maxRecDepth_2578_);
lean_inc(v_nextMacroScope_2577_);
lean_inc(v_usedQuotCtxts_2576_);
lean_inc(v_scopes_2575_);
lean_inc(v_messages_2574_);
lean_inc(v_env_2573_);
lean_dec(v___x_2571_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2604_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
uint8_t v_enabled_2586_; lean_object* v_assignment_2587_; lean_object* v_lazyAssignment_2588_; lean_object* v_trees_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2603_; 
v_enabled_2586_ = lean_ctor_get_uint8(v_infoState_2572_, sizeof(void*)*3);
v_assignment_2587_ = lean_ctor_get(v_infoState_2572_, 0);
v_lazyAssignment_2588_ = lean_ctor_get(v_infoState_2572_, 1);
v_trees_2589_ = lean_ctor_get(v_infoState_2572_, 2);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_infoState_2572_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2591_ = v_infoState_2572_;
v_isShared_2592_ = v_isSharedCheck_2603_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_trees_2589_);
lean_inc(v_lazyAssignment_2588_);
lean_inc(v_assignment_2587_);
lean_dec(v_infoState_2572_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2603_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2593_ = l_Lean_PersistentArray_push___redArg(v_trees_2589_, v_t_2563_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 2, v___x_2593_);
v___x_2595_ = v___x_2591_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_assignment_2587_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_lazyAssignment_2588_);
lean_ctor_set(v_reuseFailAlloc_2602_, 2, v___x_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2602_, sizeof(void*)*3, v_enabled_2586_);
v___x_2595_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 8, v___x_2595_);
v___x_2597_ = v___x_2584_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_env_2573_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_messages_2574_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_scopes_2575_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_usedQuotCtxts_2576_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_nextMacroScope_2577_);
lean_ctor_set(v_reuseFailAlloc_2601_, 5, v_maxRecDepth_2578_);
lean_ctor_set(v_reuseFailAlloc_2601_, 6, v_ngen_2579_);
lean_ctor_set(v_reuseFailAlloc_2601_, 7, v_auxDeclNGen_2580_);
lean_ctor_set(v_reuseFailAlloc_2601_, 8, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2601_, 9, v_traceState_2581_);
lean_ctor_set(v_reuseFailAlloc_2601_, 10, v_snapshotTasks_2582_);
v___x_2597_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_st_ref_set(v___y_2564_, v___x_2597_);
v___x_2599_ = lean_box(0);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2605_, v___y_2606_);
lean_dec(v___y_2606_);
return v_res_2608_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_unsigned_to_nat(32u);
v___x_2610_ = lean_mk_empty_array_with_capacity(v___x_2609_);
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2612_ = ((size_t)5ULL);
v___x_2613_ = lean_unsigned_to_nat(0u);
v___x_2614_ = lean_unsigned_to_nat(32u);
v___x_2615_ = lean_mk_empty_array_with_capacity(v___x_2614_);
v___x_2616_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2617_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
lean_ctor_set(v___x_2617_, 1, v___x_2615_);
lean_ctor_set(v___x_2617_, 2, v___x_2613_);
lean_ctor_set(v___x_2617_, 3, v___x_2613_);
lean_ctor_set_usize(v___x_2617_, 4, v___x_2612_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; lean_object* v_infoState_2623_; uint8_t v_enabled_2624_; 
v___x_2622_ = lean_st_ref_get(v___y_2620_);
v_infoState_2623_ = lean_ctor_get(v___x_2622_, 8);
lean_inc_ref(v_infoState_2623_);
lean_dec(v___x_2622_);
v_enabled_2624_ = lean_ctor_get_uint8(v_infoState_2623_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2623_);
if (v_enabled_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec_ref(v_t_2618_);
v___x_2625_ = lean_box(0);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2628_, 0, v_t_2618_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2628_, v___y_2620_);
return v___x_2629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(lean_object* v_edited_2635_, lean_object* v___x_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v_fst_2639_; lean_object* v_snd_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2665_; 
v_fst_2639_ = lean_ctor_get(v_a_2638_, 0);
v_snd_2640_ = lean_ctor_get(v_a_2638_, 1);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_a_2638_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2642_ = v_a_2638_;
v_isShared_2643_ = v_isSharedCheck_2665_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_snd_2640_);
lean_inc(v_fst_2639_);
lean_dec(v_a_2638_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2665_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; uint8_t v___y_2646_; uint8_t v___x_2661_; 
v___x_2644_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2661_ = lean_nat_dec_lt(v_snd_2640_, v___x_2636_);
if (v___x_2661_ == 0)
{
v___y_2646_ = v___x_2661_;
goto v___jp_2645_;
}
else
{
lean_object* v___x_2662_; uint8_t v___x_2663_; uint8_t v___x_2664_; 
v___x_2662_ = lean_array_get_borrowed(v___x_2644_, v_edited_2635_, v_snd_2640_);
v___x_2663_ = lean_string_dec_eq(v___x_2662_, v_a_2637_);
v___x_2664_ = lean_bool_not(v___x_2663_);
v___y_2646_ = v___x_2664_;
goto v___jp_2645_;
}
v___jp_2645_:
{
if (v___y_2646_ == 0)
{
lean_object* v___x_2648_; 
if (v_isShared_2643_ == 0)
{
v___x_2648_ = v___x_2642_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_fst_2639_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_snd_2640_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
else
{
uint8_t v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2650_ = 0;
v___x_2651_ = lean_array_get_borrowed(v___x_2644_, v_edited_2635_, v_snd_2640_);
v___x_2652_ = lean_box(v___x_2650_);
lean_inc(v___x_2651_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 1, v___x_2651_);
lean_ctor_set(v___x_2642_, 0, v___x_2652_);
v___x_2654_ = v___x_2642_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2651_);
v___x_2654_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2655_ = lean_array_push(v_fst_2639_, v___x_2654_);
v___x_2656_ = lean_unsigned_to_nat(1u);
v___x_2657_ = lean_nat_add(v_snd_2640_, v___x_2656_);
lean_dec(v_snd_2640_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2655_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v_a_2638_ = v___x_2658_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg___boxed(lean_object* v_edited_2666_, lean_object* v___x_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2666_, v___x_2667_, v_a_2668_, v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v___x_2667_);
lean_dec_ref(v_edited_2666_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v_original_2671_, lean_object* v___x_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v_fst_2675_; lean_object* v_snd_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2701_; 
v_fst_2675_ = lean_ctor_get(v_a_2674_, 0);
v_snd_2676_ = lean_ctor_get(v_a_2674_, 1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_a_2674_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2678_ = v_a_2674_;
v_isShared_2679_ = v_isSharedCheck_2701_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_snd_2676_);
lean_inc(v_fst_2675_);
lean_dec(v_a_2674_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2701_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; uint8_t v___y_2682_; uint8_t v___x_2697_; 
v___x_2680_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2697_ = lean_nat_dec_lt(v_snd_2676_, v___x_2672_);
if (v___x_2697_ == 0)
{
v___y_2682_ = v___x_2697_;
goto v___jp_2681_;
}
else
{
lean_object* v___x_2698_; uint8_t v___x_2699_; uint8_t v___x_2700_; 
v___x_2698_ = lean_array_get_borrowed(v___x_2680_, v_original_2671_, v_snd_2676_);
v___x_2699_ = lean_string_dec_eq(v___x_2698_, v_a_2673_);
v___x_2700_ = lean_bool_not(v___x_2699_);
v___y_2682_ = v___x_2700_;
goto v___jp_2681_;
}
v___jp_2681_:
{
if (v___y_2682_ == 0)
{
lean_object* v___x_2684_; 
if (v_isShared_2679_ == 0)
{
v___x_2684_ = v___x_2678_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_fst_2675_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_snd_2676_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
else
{
uint8_t v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2686_ = 1;
v___x_2687_ = lean_array_get_borrowed(v___x_2680_, v_original_2671_, v_snd_2676_);
v___x_2688_ = lean_box(v___x_2686_);
lean_inc(v___x_2687_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2687_);
lean_ctor_set(v___x_2678_, 0, v___x_2688_);
v___x_2690_ = v___x_2678_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2687_);
v___x_2690_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2691_ = lean_array_push(v_fst_2675_, v___x_2690_);
v___x_2692_ = lean_unsigned_to_nat(1u);
v___x_2693_ = lean_nat_add(v_snd_2676_, v___x_2692_);
lean_dec(v_snd_2676_);
v___x_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2691_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v_a_2674_ = v___x_2694_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v_original_2702_, lean_object* v___x_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2702_, v___x_2703_, v_a_2704_, v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v___x_2703_);
lean_dec_ref(v_original_2702_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v_original_2707_, lean_object* v___x_2708_, lean_object* v_edited_2709_, lean_object* v___x_2710_, lean_object* v_as_2711_, size_t v_sz_2712_, size_t v_i_2713_, lean_object* v_b_2714_){
_start:
{
uint8_t v___x_2715_; 
v___x_2715_ = lean_usize_dec_lt(v_i_2713_, v_sz_2712_);
if (v___x_2715_ == 0)
{
return v_b_2714_;
}
else
{
lean_object* v_snd_2716_; lean_object* v_fst_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2764_; 
v_snd_2716_ = lean_ctor_get(v_b_2714_, 1);
v_fst_2717_ = lean_ctor_get(v_b_2714_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_b_2714_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2719_ = v_b_2714_;
v_isShared_2720_ = v_isSharedCheck_2764_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_snd_2716_);
lean_inc(v_fst_2717_);
lean_dec(v_b_2714_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2764_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v_fst_2721_; lean_object* v_snd_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2763_; 
v_fst_2721_ = lean_ctor_get(v_snd_2716_, 0);
v_snd_2722_ = lean_ctor_get(v_snd_2716_, 1);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_snd_2716_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2724_ = v_snd_2716_;
v_isShared_2725_ = v_isSharedCheck_2763_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_snd_2722_);
lean_inc(v_fst_2721_);
lean_dec(v_snd_2716_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2763_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_a_2726_; lean_object* v___x_2728_; 
v_a_2726_ = lean_array_uget_borrowed(v_as_2711_, v_i_2713_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 1, v_fst_2721_);
lean_ctor_set(v___x_2724_, 0, v_fst_2717_);
v___x_2728_ = v___x_2724_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_fst_2717_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_fst_2721_);
v___x_2728_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; lean_object* v_fst_2730_; lean_object* v_snd_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2761_; 
v___x_2729_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2707_, v___x_2708_, v_a_2726_, v___x_2728_);
v_fst_2730_ = lean_ctor_get(v___x_2729_, 0);
v_snd_2731_ = lean_ctor_get(v___x_2729_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2733_ = v___x_2729_;
v_isShared_2734_ = v_isSharedCheck_2761_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_snd_2731_);
lean_inc(v_fst_2730_);
lean_dec(v___x_2729_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2761_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v_snd_2722_);
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_fst_2730_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v_snd_2722_);
v___x_2736_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; lean_object* v_fst_2738_; lean_object* v_snd_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2759_; 
v___x_2737_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2709_, v___x_2710_, v_a_2726_, v___x_2736_);
v_fst_2738_ = lean_ctor_get(v___x_2737_, 0);
v_snd_2739_ = lean_ctor_get(v___x_2737_, 1);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2741_ = v___x_2737_;
v_isShared_2742_ = v_isSharedCheck_2759_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_snd_2739_);
lean_inc(v_fst_2738_);
lean_dec(v___x_2737_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2759_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
uint8_t v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2743_ = 2;
v___x_2744_ = lean_box(v___x_2743_);
lean_inc(v_a_2726_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 1, v_a_2726_);
lean_ctor_set(v___x_2741_, 0, v___x_2744_);
v___x_2746_ = v___x_2741_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_a_2726_);
v___x_2746_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2747_ = lean_array_push(v_fst_2738_, v___x_2746_);
v___x_2748_ = lean_unsigned_to_nat(1u);
v___x_2749_ = lean_nat_add(v_snd_2731_, v___x_2748_);
lean_dec(v_snd_2731_);
v___x_2750_ = lean_nat_add(v_snd_2739_, v___x_2748_);
lean_dec(v_snd_2739_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 1, v___x_2750_);
lean_ctor_set(v___x_2719_, 0, v___x_2749_);
v___x_2752_ = v___x_2719_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; size_t v___x_2754_; size_t v___x_2755_; 
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2747_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = ((size_t)1ULL);
v___x_2755_ = lean_usize_add(v_i_2713_, v___x_2754_);
v_i_2713_ = v___x_2755_;
v_b_2714_ = v___x_2753_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v_original_2765_, lean_object* v___x_2766_, lean_object* v_edited_2767_, lean_object* v___x_2768_, lean_object* v_as_2769_, lean_object* v_sz_2770_, lean_object* v_i_2771_, lean_object* v_b_2772_){
_start:
{
size_t v_sz_boxed_2773_; size_t v_i_boxed_2774_; lean_object* v_res_2775_; 
v_sz_boxed_2773_ = lean_unbox_usize(v_sz_2770_);
lean_dec(v_sz_2770_);
v_i_boxed_2774_ = lean_unbox_usize(v_i_2771_);
lean_dec(v_i_2771_);
v_res_2775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2765_, v___x_2766_, v_edited_2767_, v___x_2768_, v_as_2769_, v_sz_boxed_2773_, v_i_boxed_2774_, v_b_2772_);
lean_dec_ref(v_as_2769_);
lean_dec(v___x_2768_);
lean_dec_ref(v_edited_2767_);
lean_dec(v___x_2766_);
lean_dec_ref(v_original_2765_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v_edited_2776_, lean_object* v___x_2777_, lean_object* v_original_2778_, lean_object* v___x_2779_, lean_object* v_as_2780_, size_t v_sz_2781_, size_t v_i_2782_, lean_object* v_b_2783_){
_start:
{
uint8_t v___x_2784_; 
v___x_2784_ = lean_usize_dec_lt(v_i_2782_, v_sz_2781_);
if (v___x_2784_ == 0)
{
return v_b_2783_;
}
else
{
lean_object* v_snd_2785_; lean_object* v_fst_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2833_; 
v_snd_2785_ = lean_ctor_get(v_b_2783_, 1);
v_fst_2786_ = lean_ctor_get(v_b_2783_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_b_2783_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2788_ = v_b_2783_;
v_isShared_2789_ = v_isSharedCheck_2833_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_snd_2785_);
lean_inc(v_fst_2786_);
lean_dec(v_b_2783_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2833_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v_fst_2790_; lean_object* v_snd_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2832_; 
v_fst_2790_ = lean_ctor_get(v_snd_2785_, 0);
v_snd_2791_ = lean_ctor_get(v_snd_2785_, 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_snd_2785_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2793_ = v_snd_2785_;
v_isShared_2794_ = v_isSharedCheck_2832_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_snd_2791_);
lean_inc(v_fst_2790_);
lean_dec(v_snd_2785_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2832_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_a_2795_; lean_object* v___x_2797_; 
v_a_2795_ = lean_array_uget_borrowed(v_as_2780_, v_i_2782_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 1, v_fst_2790_);
lean_ctor_set(v___x_2793_, 0, v_fst_2786_);
v___x_2797_ = v___x_2793_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_fst_2786_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_fst_2790_);
v___x_2797_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v_fst_2799_; lean_object* v_snd_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2830_; 
v___x_2798_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2778_, v___x_2779_, v_a_2795_, v___x_2797_);
v_fst_2799_ = lean_ctor_get(v___x_2798_, 0);
v_snd_2800_ = lean_ctor_get(v___x_2798_, 1);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2802_ = v___x_2798_;
v_isShared_2803_ = v_isSharedCheck_2830_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_snd_2800_);
lean_inc(v_fst_2799_);
lean_dec(v___x_2798_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2830_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 1, v_snd_2791_);
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_fst_2799_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_snd_2791_);
v___x_2805_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
lean_object* v___x_2806_; lean_object* v_fst_2807_; lean_object* v_snd_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2828_; 
v___x_2806_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2776_, v___x_2777_, v_a_2795_, v___x_2805_);
v_fst_2807_ = lean_ctor_get(v___x_2806_, 0);
v_snd_2808_ = lean_ctor_get(v___x_2806_, 1);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2810_ = v___x_2806_;
v_isShared_2811_ = v_isSharedCheck_2828_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_snd_2808_);
lean_inc(v_fst_2807_);
lean_dec(v___x_2806_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2828_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
uint8_t v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2815_; 
v___x_2812_ = 2;
v___x_2813_ = lean_box(v___x_2812_);
lean_inc(v_a_2795_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 1, v_a_2795_);
lean_ctor_set(v___x_2810_, 0, v___x_2813_);
v___x_2815_ = v___x_2810_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_a_2795_);
v___x_2815_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2816_ = lean_array_push(v_fst_2807_, v___x_2815_);
v___x_2817_ = lean_unsigned_to_nat(1u);
v___x_2818_ = lean_nat_add(v_snd_2800_, v___x_2817_);
lean_dec(v_snd_2800_);
v___x_2819_ = lean_nat_add(v_snd_2808_, v___x_2817_);
lean_dec(v_snd_2808_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 1, v___x_2819_);
lean_ctor_set(v___x_2788_, 0, v___x_2818_);
v___x_2821_ = v___x_2788_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2822_; size_t v___x_2823_; size_t v___x_2824_; lean_object* v___x_2825_; 
v___x_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2816_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = ((size_t)1ULL);
v___x_2824_ = lean_usize_add(v_i_2782_, v___x_2823_);
v___x_2825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2778_, v___x_2779_, v_edited_2776_, v___x_2777_, v_as_2780_, v_sz_2781_, v___x_2824_, v___x_2822_);
return v___x_2825_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v_edited_2834_, lean_object* v___x_2835_, lean_object* v_original_2836_, lean_object* v___x_2837_, lean_object* v_as_2838_, lean_object* v_sz_2839_, lean_object* v_i_2840_, lean_object* v_b_2841_){
_start:
{
size_t v_sz_boxed_2842_; size_t v_i_boxed_2843_; lean_object* v_res_2844_; 
v_sz_boxed_2842_ = lean_unbox_usize(v_sz_2839_);
lean_dec(v_sz_2839_);
v_i_boxed_2843_ = lean_unbox_usize(v_i_2840_);
lean_dec(v_i_2840_);
v_res_2844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_2834_, v___x_2835_, v_original_2836_, v___x_2837_, v_as_2838_, v_sz_boxed_2842_, v_i_boxed_2843_, v_b_2841_);
lean_dec_ref(v_as_2838_);
lean_dec(v___x_2837_);
lean_dec_ref(v_original_2836_);
lean_dec(v___x_2835_);
lean_dec_ref(v_edited_2834_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(lean_object* v_a_2845_, lean_object* v_x_2846_){
_start:
{
if (lean_obj_tag(v_x_2846_) == 0)
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_box(0);
return v___x_2847_;
}
else
{
lean_object* v_key_2848_; lean_object* v_value_2849_; lean_object* v_tail_2850_; uint8_t v___x_2851_; 
v_key_2848_ = lean_ctor_get(v_x_2846_, 0);
v_value_2849_ = lean_ctor_get(v_x_2846_, 1);
v_tail_2850_ = lean_ctor_get(v_x_2846_, 2);
v___x_2851_ = lean_string_dec_eq(v_key_2848_, v_a_2845_);
if (v___x_2851_ == 0)
{
v_x_2846_ = v_tail_2850_;
goto _start;
}
else
{
lean_object* v___x_2853_; 
lean_inc(v_value_2849_);
v___x_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2853_, 0, v_value_2849_);
return v___x_2853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg___boxed(lean_object* v_a_2854_, lean_object* v_x_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2854_, v_x_2855_);
lean_dec(v_x_2855_);
lean_dec_ref(v_a_2854_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(lean_object* v_m_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_buckets_2859_; lean_object* v___x_2860_; uint64_t v___x_2861_; uint64_t v___x_2862_; uint64_t v___x_2863_; uint64_t v_fold_2864_; uint64_t v___x_2865_; uint64_t v___x_2866_; uint64_t v___x_2867_; size_t v___x_2868_; size_t v___x_2869_; size_t v___x_2870_; size_t v___x_2871_; size_t v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_buckets_2859_ = lean_ctor_get(v_m_2857_, 1);
v___x_2860_ = lean_array_get_size(v_buckets_2859_);
v___x_2861_ = lean_string_hash(v_a_2858_);
v___x_2862_ = 32ULL;
v___x_2863_ = lean_uint64_shift_right(v___x_2861_, v___x_2862_);
v_fold_2864_ = lean_uint64_xor(v___x_2861_, v___x_2863_);
v___x_2865_ = 16ULL;
v___x_2866_ = lean_uint64_shift_right(v_fold_2864_, v___x_2865_);
v___x_2867_ = lean_uint64_xor(v_fold_2864_, v___x_2866_);
v___x_2868_ = lean_uint64_to_usize(v___x_2867_);
v___x_2869_ = lean_usize_of_nat(v___x_2860_);
v___x_2870_ = ((size_t)1ULL);
v___x_2871_ = lean_usize_sub(v___x_2869_, v___x_2870_);
v___x_2872_ = lean_usize_land(v___x_2868_, v___x_2871_);
v___x_2873_ = lean_array_uget_borrowed(v_buckets_2859_, v___x_2872_);
v___x_2874_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2858_, v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_m_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_2875_, v_a_2876_);
lean_dec_ref(v_a_2876_);
lean_dec_ref(v_m_2875_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(lean_object* v_a_2878_, lean_object* v_b_2879_, lean_object* v_x_2880_){
_start:
{
if (lean_obj_tag(v_x_2880_) == 0)
{
lean_dec(v_b_2879_);
lean_dec_ref(v_a_2878_);
return v_x_2880_;
}
else
{
lean_object* v_key_2881_; lean_object* v_value_2882_; lean_object* v_tail_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2895_; 
v_key_2881_ = lean_ctor_get(v_x_2880_, 0);
v_value_2882_ = lean_ctor_get(v_x_2880_, 1);
v_tail_2883_ = lean_ctor_get(v_x_2880_, 2);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_x_2880_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2885_ = v_x_2880_;
v_isShared_2886_ = v_isSharedCheck_2895_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_tail_2883_);
lean_inc(v_value_2882_);
lean_inc(v_key_2881_);
lean_dec(v_x_2880_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2895_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
uint8_t v___x_2887_; 
v___x_2887_ = lean_string_dec_eq(v_key_2881_, v_a_2878_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2888_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2878_, v_b_2879_, v_tail_2883_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 2, v___x_2888_);
v___x_2890_ = v___x_2885_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_key_2881_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_value_2882_);
lean_ctor_set(v_reuseFailAlloc_2891_, 2, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
else
{
lean_object* v___x_2893_; 
lean_dec(v_value_2882_);
lean_dec(v_key_2881_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 1, v_b_2879_);
lean_ctor_set(v___x_2885_, 0, v_a_2878_);
v___x_2893_ = v___x_2885_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2878_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_b_2879_);
lean_ctor_set(v_reuseFailAlloc_2894_, 2, v_tail_2883_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(lean_object* v_a_2896_, lean_object* v_x_2897_){
_start:
{
if (lean_obj_tag(v_x_2897_) == 0)
{
uint8_t v___x_2898_; 
v___x_2898_ = 0;
return v___x_2898_;
}
else
{
lean_object* v_key_2899_; lean_object* v_tail_2900_; uint8_t v___x_2901_; 
v_key_2899_ = lean_ctor_get(v_x_2897_, 0);
v_tail_2900_ = lean_ctor_get(v_x_2897_, 2);
v___x_2901_ = lean_string_dec_eq(v_key_2899_, v_a_2896_);
if (v___x_2901_ == 0)
{
v_x_2897_ = v_tail_2900_;
goto _start;
}
else
{
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg___boxed(lean_object* v_a_2903_, lean_object* v_x_2904_){
_start:
{
uint8_t v_res_2905_; lean_object* v_r_2906_; 
v_res_2905_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2903_, v_x_2904_);
lean_dec(v_x_2904_);
lean_dec_ref(v_a_2903_);
v_r_2906_ = lean_box(v_res_2905_);
return v_r_2906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2907_, lean_object* v_x_2908_){
_start:
{
if (lean_obj_tag(v_x_2908_) == 0)
{
return v_x_2907_;
}
else
{
lean_object* v_key_2909_; lean_object* v_value_2910_; lean_object* v_tail_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2934_; 
v_key_2909_ = lean_ctor_get(v_x_2908_, 0);
v_value_2910_ = lean_ctor_get(v_x_2908_, 1);
v_tail_2911_ = lean_ctor_get(v_x_2908_, 2);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_x_2908_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2913_ = v_x_2908_;
v_isShared_2914_ = v_isSharedCheck_2934_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_tail_2911_);
lean_inc(v_value_2910_);
lean_inc(v_key_2909_);
lean_dec(v_x_2908_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2934_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; uint64_t v___x_2916_; uint64_t v___x_2917_; uint64_t v___x_2918_; uint64_t v_fold_2919_; uint64_t v___x_2920_; uint64_t v___x_2921_; uint64_t v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; size_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2915_ = lean_array_get_size(v_x_2907_);
v___x_2916_ = lean_string_hash(v_key_2909_);
v___x_2917_ = 32ULL;
v___x_2918_ = lean_uint64_shift_right(v___x_2916_, v___x_2917_);
v_fold_2919_ = lean_uint64_xor(v___x_2916_, v___x_2918_);
v___x_2920_ = 16ULL;
v___x_2921_ = lean_uint64_shift_right(v_fold_2919_, v___x_2920_);
v___x_2922_ = lean_uint64_xor(v_fold_2919_, v___x_2921_);
v___x_2923_ = lean_uint64_to_usize(v___x_2922_);
v___x_2924_ = lean_usize_of_nat(v___x_2915_);
v___x_2925_ = ((size_t)1ULL);
v___x_2926_ = lean_usize_sub(v___x_2924_, v___x_2925_);
v___x_2927_ = lean_usize_land(v___x_2923_, v___x_2926_);
v___x_2928_ = lean_array_uget_borrowed(v_x_2907_, v___x_2927_);
lean_inc(v___x_2928_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 2, v___x_2928_);
v___x_2930_ = v___x_2913_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_key_2909_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_value_2910_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_array_uset(v_x_2907_, v___x_2927_, v___x_2930_);
v_x_2907_ = v___x_2931_;
v_x_2908_ = v_tail_2911_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(lean_object* v_i_2935_, lean_object* v_source_2936_, lean_object* v_target_2937_){
_start:
{
lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___x_2938_ = lean_array_get_size(v_source_2936_);
v___x_2939_ = lean_nat_dec_lt(v_i_2935_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_dec_ref(v_source_2936_);
lean_dec(v_i_2935_);
return v_target_2937_;
}
else
{
lean_object* v_es_2940_; lean_object* v___x_2941_; lean_object* v_source_2942_; lean_object* v_target_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_es_2940_ = lean_array_fget(v_source_2936_, v_i_2935_);
v___x_2941_ = lean_box(0);
v_source_2942_ = lean_array_fset(v_source_2936_, v_i_2935_, v___x_2941_);
v_target_2943_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_target_2937_, v_es_2940_);
v___x_2944_ = lean_unsigned_to_nat(1u);
v___x_2945_ = lean_nat_add(v_i_2935_, v___x_2944_);
lean_dec(v_i_2935_);
v_i_2935_ = v___x_2945_;
v_source_2936_ = v_source_2942_;
v_target_2937_ = v_target_2943_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(lean_object* v_data_2947_){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v_nbuckets_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2948_ = lean_array_get_size(v_data_2947_);
v___x_2949_ = lean_unsigned_to_nat(2u);
v_nbuckets_2950_ = lean_nat_mul(v___x_2948_, v___x_2949_);
v___x_2951_ = lean_unsigned_to_nat(0u);
v___x_2952_ = lean_box(0);
v___x_2953_ = lean_mk_array(v_nbuckets_2950_, v___x_2952_);
v___x_2954_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v___x_2951_, v_data_2947_, v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(lean_object* v_m_2955_, lean_object* v_a_2956_, lean_object* v_b_2957_){
_start:
{
lean_object* v_size_2958_; lean_object* v_buckets_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_3002_; 
v_size_2958_ = lean_ctor_get(v_m_2955_, 0);
v_buckets_2959_ = lean_ctor_get(v_m_2955_, 1);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_m_2955_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2961_ = v_m_2955_;
v_isShared_2962_ = v_isSharedCheck_3002_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_buckets_2959_);
lean_inc(v_size_2958_);
lean_dec(v_m_2955_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_3002_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; uint64_t v___x_2964_; uint64_t v___x_2965_; uint64_t v___x_2966_; uint64_t v_fold_2967_; uint64_t v___x_2968_; uint64_t v___x_2969_; uint64_t v___x_2970_; size_t v___x_2971_; size_t v___x_2972_; size_t v___x_2973_; size_t v___x_2974_; size_t v___x_2975_; lean_object* v_bkt_2976_; uint8_t v___x_2977_; 
v___x_2963_ = lean_array_get_size(v_buckets_2959_);
v___x_2964_ = lean_string_hash(v_a_2956_);
v___x_2965_ = 32ULL;
v___x_2966_ = lean_uint64_shift_right(v___x_2964_, v___x_2965_);
v_fold_2967_ = lean_uint64_xor(v___x_2964_, v___x_2966_);
v___x_2968_ = 16ULL;
v___x_2969_ = lean_uint64_shift_right(v_fold_2967_, v___x_2968_);
v___x_2970_ = lean_uint64_xor(v_fold_2967_, v___x_2969_);
v___x_2971_ = lean_uint64_to_usize(v___x_2970_);
v___x_2972_ = lean_usize_of_nat(v___x_2963_);
v___x_2973_ = ((size_t)1ULL);
v___x_2974_ = lean_usize_sub(v___x_2972_, v___x_2973_);
v___x_2975_ = lean_usize_land(v___x_2971_, v___x_2974_);
v_bkt_2976_ = lean_array_uget_borrowed(v_buckets_2959_, v___x_2975_);
v___x_2977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2956_, v_bkt_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; lean_object* v_size_x27_2979_; lean_object* v___x_2980_; lean_object* v_buckets_x27_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2978_ = lean_unsigned_to_nat(1u);
v_size_x27_2979_ = lean_nat_add(v_size_2958_, v___x_2978_);
lean_dec(v_size_2958_);
lean_inc(v_bkt_2976_);
v___x_2980_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2980_, 0, v_a_2956_);
lean_ctor_set(v___x_2980_, 1, v_b_2957_);
lean_ctor_set(v___x_2980_, 2, v_bkt_2976_);
v_buckets_x27_2981_ = lean_array_uset(v_buckets_2959_, v___x_2975_, v___x_2980_);
v___x_2982_ = lean_unsigned_to_nat(4u);
v___x_2983_ = lean_nat_mul(v_size_x27_2979_, v___x_2982_);
v___x_2984_ = lean_unsigned_to_nat(3u);
v___x_2985_ = lean_nat_div(v___x_2983_, v___x_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_array_get_size(v_buckets_x27_2981_);
v___x_2987_ = lean_nat_dec_le(v___x_2985_, v___x_2986_);
lean_dec(v___x_2985_);
if (v___x_2987_ == 0)
{
lean_object* v_val_2988_; lean_object* v___x_2990_; 
v_val_2988_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_buckets_x27_2981_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v_val_2988_);
lean_ctor_set(v___x_2961_, 0, v_size_x27_2979_);
v___x_2990_ = v___x_2961_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_size_x27_2979_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_val_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
else
{
lean_object* v___x_2993_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v_buckets_x27_2981_);
lean_ctor_set(v___x_2961_, 0, v_size_x27_2979_);
v___x_2993_ = v___x_2961_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_size_x27_2979_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_buckets_x27_2981_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
else
{
lean_object* v___x_2995_; lean_object* v_buckets_x27_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_3000_; 
lean_inc(v_bkt_2976_);
v___x_2995_ = lean_box(0);
v_buckets_x27_2996_ = lean_array_uset(v_buckets_2959_, v___x_2975_, v___x_2995_);
v___x_2997_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2956_, v_b_2957_, v_bkt_2976_);
v___x_2998_ = lean_array_uset(v_buckets_x27_2996_, v___x_2975_, v___x_2997_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v___x_2998_);
v___x_3000_ = v___x_2961_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_size_2958_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(lean_object* v_histogram_3003_, lean_object* v_index_3004_, lean_object* v_val_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3003_, v_val_3005_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3007_ = lean_unsigned_to_nat(1u);
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_index_3004_);
v___x_3009_ = lean_unsigned_to_nat(0u);
v___x_3010_ = lean_box(0);
v___x_3011_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3007_);
lean_ctor_set(v___x_3011_, 1, v___x_3008_);
lean_ctor_set(v___x_3011_, 2, v___x_3009_);
lean_ctor_set(v___x_3011_, 3, v___x_3010_);
v___x_3012_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3003_, v_val_3005_, v___x_3011_);
return v___x_3012_;
}
else
{
lean_object* v_val_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3034_; 
v_val_3013_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3015_ = v___x_3006_;
v_isShared_3016_ = v_isSharedCheck_3034_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_val_3013_);
lean_dec(v___x_3006_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3034_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v_leftCount_3017_; lean_object* v_rightCount_3018_; lean_object* v_rightIndex_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3032_; 
v_leftCount_3017_ = lean_ctor_get(v_val_3013_, 0);
v_rightCount_3018_ = lean_ctor_get(v_val_3013_, 2);
v_rightIndex_3019_ = lean_ctor_get(v_val_3013_, 3);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_val_3013_);
if (v_isSharedCheck_3032_ == 0)
{
lean_object* v_unused_3033_; 
v_unused_3033_ = lean_ctor_get(v_val_3013_, 1);
lean_dec(v_unused_3033_);
v___x_3021_ = v_val_3013_;
v_isShared_3022_ = v_isSharedCheck_3032_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_rightIndex_3019_);
lean_inc(v_rightCount_3018_);
lean_inc(v_leftCount_3017_);
lean_dec(v_val_3013_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3032_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3023_ = lean_unsigned_to_nat(1u);
v___x_3024_ = lean_nat_add(v_leftCount_3017_, v___x_3023_);
lean_dec(v_leftCount_3017_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v_index_3004_);
v___x_3026_ = v___x_3015_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_index_3004_);
v___x_3026_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3028_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 1, v___x_3026_);
lean_ctor_set(v___x_3021_, 0, v___x_3024_);
v___x_3028_ = v___x_3021_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3030_, 2, v_rightCount_3018_);
lean_ctor_set(v_reuseFailAlloc_3030_, 3, v_rightIndex_3019_);
v___x_3028_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3003_, v_val_3005_, v___x_3028_);
return v___x_3029_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(lean_object* v_upperBound_3035_, lean_object* v_fst_3036_, lean_object* v___x_3037_, lean_object* v_fst_3038_, lean_object* v_a_3039_, lean_object* v_b_3040_){
_start:
{
uint8_t v___x_3041_; 
v___x_3041_ = lean_nat_dec_lt(v_a_3039_, v_upperBound_3035_);
if (v___x_3041_ == 0)
{
lean_dec(v_a_3039_);
return v_b_3040_;
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3042_ = l_Subarray_get___redArg(v_fst_3038_, v_a_3039_);
lean_inc(v_a_3039_);
v___x_3043_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_b_3040_, v_a_3039_, v___x_3042_);
v___x_3044_ = lean_unsigned_to_nat(1u);
v___x_3045_ = lean_nat_add(v_a_3039_, v___x_3044_);
lean_dec(v_a_3039_);
v_a_3039_ = v___x_3045_;
v_b_3040_ = v___x_3043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg___boxed(lean_object* v_upperBound_3047_, lean_object* v_fst_3048_, lean_object* v___x_3049_, lean_object* v_fst_3050_, lean_object* v_a_3051_, lean_object* v_b_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3047_, v_fst_3048_, v___x_3049_, v_fst_3050_, v_a_3051_, v_b_3052_);
lean_dec_ref(v_fst_3050_);
lean_dec(v___x_3049_);
lean_dec_ref(v_fst_3048_);
lean_dec(v_upperBound_3047_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(lean_object* v_x_3054_, lean_object* v_x_3055_){
_start:
{
if (lean_obj_tag(v_x_3055_) == 0)
{
lean_inc(v_x_3054_);
return v_x_3054_;
}
else
{
lean_object* v_key_3056_; lean_object* v_value_3057_; lean_object* v_tail_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_key_3056_ = lean_ctor_get(v_x_3055_, 0);
v_value_3057_ = lean_ctor_get(v_x_3055_, 1);
v_tail_3058_ = lean_ctor_get(v_x_3055_, 2);
v___x_3059_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3054_, v_tail_3058_);
lean_inc(v_value_3057_);
lean_inc(v_key_3056_);
v___x_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3060_, 0, v_key_3056_);
lean_ctor_set(v___x_3060_, 1, v_value_3057_);
v___x_3061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
lean_ctor_set(v___x_3061_, 1, v___x_3059_);
return v___x_3061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___boxed(lean_object* v_x_3062_, lean_object* v_x_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3062_, v_x_3063_);
lean_dec(v_x_3063_);
lean_dec(v_x_3062_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(lean_object* v_as_3065_, size_t v_i_3066_, size_t v_stop_3067_, lean_object* v_b_3068_){
_start:
{
uint8_t v___x_3069_; 
v___x_3069_ = lean_usize_dec_eq(v_i_3066_, v_stop_3067_);
if (v___x_3069_ == 0)
{
size_t v___x_3070_; size_t v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3070_ = ((size_t)1ULL);
v___x_3071_ = lean_usize_sub(v_i_3066_, v___x_3070_);
v___x_3072_ = lean_array_uget_borrowed(v_as_3065_, v___x_3071_);
v___x_3073_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_b_3068_, v___x_3072_);
lean_dec(v_b_3068_);
v_i_3066_ = v___x_3071_;
v_b_3068_ = v___x_3073_;
goto _start;
}
else
{
return v_b_3068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___boxed(lean_object* v_as_3075_, lean_object* v_i_3076_, lean_object* v_stop_3077_, lean_object* v_b_3078_){
_start:
{
size_t v_i_boxed_3079_; size_t v_stop_boxed_3080_; lean_object* v_res_3081_; 
v_i_boxed_3079_ = lean_unbox_usize(v_i_3076_);
lean_dec(v_i_3076_);
v_stop_boxed_3080_ = lean_unbox_usize(v_stop_3077_);
lean_dec(v_stop_3077_);
v_res_3081_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_as_3075_, v_i_boxed_3079_, v_stop_boxed_3080_, v_b_3078_);
lean_dec_ref(v_as_3075_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(lean_object* v_left_3082_, lean_object* v_right_3083_, lean_object* v_pref_3084_){
_start:
{
lean_object* v_start_3085_; lean_object* v_stop_3086_; lean_object* v_i_3087_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v_start_3085_ = lean_ctor_get(v_left_3082_, 1);
v_stop_3086_ = lean_ctor_get(v_left_3082_, 2);
v_i_3087_ = lean_array_get_size(v_pref_3084_);
v___x_3093_ = lean_nat_sub(v_stop_3086_, v_start_3085_);
v___x_3094_ = lean_nat_dec_lt(v_i_3087_, v___x_3093_);
lean_dec(v___x_3093_);
if (v___x_3094_ == 0)
{
goto v___jp_3088_;
}
else
{
lean_object* v_start_3095_; lean_object* v_stop_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v_start_3095_ = lean_ctor_get(v_right_3083_, 1);
v_stop_3096_ = lean_ctor_get(v_right_3083_, 2);
v___x_3097_ = lean_nat_sub(v_stop_3096_, v_start_3095_);
v___x_3098_ = lean_nat_dec_lt(v_i_3087_, v___x_3097_);
lean_dec(v___x_3097_);
if (v___x_3098_ == 0)
{
goto v___jp_3088_;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v___x_3099_ = l_Subarray_get___redArg(v_left_3082_, v_i_3087_);
v___x_3100_ = l_Subarray_get___redArg(v_right_3083_, v_i_3087_);
v___x_3101_ = lean_string_dec_eq(v___x_3099_, v___x_3100_);
lean_dec(v___x_3100_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec(v___x_3099_);
v___x_3102_ = l_Subarray_drop___redArg(v_left_3082_, v_i_3087_);
v___x_3103_ = l_Subarray_drop___redArg(v_right_3083_, v_i_3087_);
v___x_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3102_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3105_, 0, v_pref_3084_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_array_push(v_pref_3084_, v___x_3099_);
v_pref_3084_ = v___x_3106_;
goto _start;
}
}
}
v___jp_3088_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3089_ = l_Subarray_drop___redArg(v_left_3082_, v_i_3087_);
v___x_3090_ = l_Subarray_drop___redArg(v_right_3083_, v_i_3087_);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3092_, 0, v_pref_3084_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
return v___x_3092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(lean_object* v_left_3110_, lean_object* v_right_3111_){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3113_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(v_left_3110_, v_right_3111_, v___x_3112_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(lean_object* v_a_3114_, lean_object* v_b_3115_){
_start:
{
lean_object* v_array_3116_; lean_object* v_start_3117_; lean_object* v_stop_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3131_; 
v_array_3116_ = lean_ctor_get(v_a_3114_, 0);
v_start_3117_ = lean_ctor_get(v_a_3114_, 1);
v_stop_3118_ = lean_ctor_get(v_a_3114_, 2);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_a_3114_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3120_ = v_a_3114_;
v_isShared_3121_ = v_isSharedCheck_3131_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_stop_3118_);
lean_inc(v_start_3117_);
lean_inc(v_array_3116_);
lean_dec(v_a_3114_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3131_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_nat_dec_lt(v_start_3117_, v_stop_3118_);
if (v___x_3122_ == 0)
{
lean_del_object(v___x_3120_);
lean_dec(v_stop_3118_);
lean_dec(v_start_3117_);
lean_dec_ref(v_array_3116_);
return v_b_3115_;
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3123_ = lean_unsigned_to_nat(1u);
v___x_3124_ = lean_nat_add(v_start_3117_, v___x_3123_);
lean_inc_ref(v_array_3116_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 1, v___x_3124_);
v___x_3126_ = v___x_3120_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_array_3116_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_3124_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_stop_3118_);
v___x_3126_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = lean_array_fget(v_array_3116_, v_start_3117_);
lean_dec(v_start_3117_);
lean_dec_ref(v_array_3116_);
v___x_3128_ = lean_array_push(v_b_3115_, v___x_3127_);
v_a_3114_ = v___x_3126_;
v_b_3115_ = v___x_3128_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(lean_object* v_left_3132_, lean_object* v_right_3133_, lean_object* v_i_3134_){
_start:
{
lean_object* v_start_3135_; lean_object* v_stop_3136_; lean_object* v___x_3137_; uint8_t v___x_3151_; 
v_start_3135_ = lean_ctor_get(v_left_3132_, 1);
v_stop_3136_ = lean_ctor_get(v_left_3132_, 2);
v___x_3137_ = lean_nat_sub(v_stop_3136_, v_start_3135_);
v___x_3151_ = lean_nat_dec_lt(v_i_3134_, v___x_3137_);
if (v___x_3151_ == 0)
{
goto v___jp_3138_;
}
else
{
lean_object* v_start_3152_; lean_object* v_stop_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; 
v_start_3152_ = lean_ctor_get(v_right_3133_, 1);
v_stop_3153_ = lean_ctor_get(v_right_3133_, 2);
v___x_3154_ = lean_nat_sub(v_stop_3153_, v_start_3152_);
v___x_3155_ = lean_nat_dec_lt(v_i_3134_, v___x_3154_);
if (v___x_3155_ == 0)
{
lean_dec(v___x_3154_);
goto v___jp_3138_;
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3156_ = lean_nat_sub(v___x_3137_, v_i_3134_);
lean_dec(v___x_3137_);
v___x_3157_ = lean_unsigned_to_nat(1u);
v___x_3158_ = lean_nat_sub(v___x_3156_, v___x_3157_);
v___x_3159_ = l_Subarray_get___redArg(v_left_3132_, v___x_3158_);
lean_dec(v___x_3158_);
v___x_3160_ = lean_nat_sub(v___x_3154_, v_i_3134_);
lean_dec(v___x_3154_);
v___x_3161_ = lean_nat_sub(v___x_3160_, v___x_3157_);
v___x_3162_ = l_Subarray_get___redArg(v_right_3133_, v___x_3161_);
lean_dec(v___x_3161_);
v___x_3163_ = lean_string_dec_eq(v___x_3159_, v___x_3162_);
lean_dec(v___x_3162_);
lean_dec(v___x_3159_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_dec(v_i_3134_);
lean_inc_ref(v_left_3132_);
v___x_3164_ = l_Subarray_take___redArg(v_left_3132_, v___x_3156_);
v___x_3165_ = l_Subarray_take___redArg(v_right_3133_, v___x_3160_);
lean_dec(v___x_3160_);
v___x_3166_ = l_Subarray_drop___redArg(v_left_3132_, v___x_3156_);
lean_dec(v___x_3156_);
v___x_3167_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3168_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3166_, v___x_3167_);
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3165_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3164_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
return v___x_3170_;
}
else
{
lean_object* v___x_3171_; 
lean_dec(v___x_3160_);
lean_dec(v___x_3156_);
v___x_3171_ = lean_nat_add(v_i_3134_, v___x_3157_);
lean_dec(v_i_3134_);
v_i_3134_ = v___x_3171_;
goto _start;
}
}
}
v___jp_3138_:
{
lean_object* v_start_3139_; lean_object* v_stop_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v_start_3139_ = lean_ctor_get(v_right_3133_, 1);
v_stop_3140_ = lean_ctor_get(v_right_3133_, 2);
v___x_3141_ = lean_nat_sub(v___x_3137_, v_i_3134_);
lean_dec(v___x_3137_);
lean_inc_ref(v_left_3132_);
v___x_3142_ = l_Subarray_take___redArg(v_left_3132_, v___x_3141_);
v___x_3143_ = lean_nat_sub(v_stop_3140_, v_start_3139_);
v___x_3144_ = lean_nat_sub(v___x_3143_, v_i_3134_);
lean_dec(v_i_3134_);
lean_dec(v___x_3143_);
v___x_3145_ = l_Subarray_take___redArg(v_right_3133_, v___x_3144_);
lean_dec(v___x_3144_);
v___x_3146_ = l_Subarray_drop___redArg(v_left_3132_, v___x_3141_);
lean_dec(v___x_3141_);
v___x_3147_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3148_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3146_, v___x_3147_);
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3145_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3142_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(lean_object* v_left_3173_, lean_object* v_right_3174_){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = lean_unsigned_to_nat(0u);
v___x_3176_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(v_left_3173_, v_right_3174_, v___x_3175_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(lean_object* v_as_x27_3177_, lean_object* v_b_3178_){
_start:
{
if (lean_obj_tag(v_as_x27_3177_) == 0)
{
return v_b_3178_;
}
else
{
lean_object* v_head_3179_; lean_object* v_snd_3180_; lean_object* v_leftIndex_3181_; 
v_head_3179_ = lean_ctor_get(v_as_x27_3177_, 0);
v_snd_3180_ = lean_ctor_get(v_head_3179_, 1);
v_leftIndex_3181_ = lean_ctor_get(v_snd_3180_, 1);
if (lean_obj_tag(v_leftIndex_3181_) == 1)
{
lean_object* v_rightIndex_3182_; 
v_rightIndex_3182_ = lean_ctor_get(v_snd_3180_, 3);
if (lean_obj_tag(v_rightIndex_3182_) == 1)
{
if (lean_obj_tag(v_b_3178_) == 0)
{
lean_object* v_tail_3183_; lean_object* v_fst_3184_; lean_object* v_leftCount_3185_; lean_object* v_rightCount_3186_; lean_object* v_val_3187_; lean_object* v_val_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_tail_3183_ = lean_ctor_get(v_as_x27_3177_, 1);
v_fst_3184_ = lean_ctor_get(v_head_3179_, 0);
v_leftCount_3185_ = lean_ctor_get(v_snd_3180_, 0);
v_rightCount_3186_ = lean_ctor_get(v_snd_3180_, 2);
v_val_3187_ = lean_ctor_get(v_leftIndex_3181_, 0);
v_val_3188_ = lean_ctor_get(v_rightIndex_3182_, 0);
v___x_3189_ = lean_nat_add(v_leftCount_3185_, v_rightCount_3186_);
lean_inc(v_val_3188_);
lean_inc(v_val_3187_);
v___x_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3190_, 0, v_val_3187_);
lean_ctor_set(v___x_3190_, 1, v_val_3188_);
lean_inc(v_fst_3184_);
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v_fst_3184_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3189_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
v_as_x27_3177_ = v_tail_3183_;
v_b_3178_ = v___x_3193_;
goto _start;
}
else
{
lean_object* v_val_3195_; lean_object* v_tail_3196_; lean_object* v_fst_3197_; lean_object* v_leftCount_3198_; lean_object* v_rightCount_3199_; lean_object* v_val_3200_; lean_object* v_val_3201_; lean_object* v_fst_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3223_; 
v_val_3195_ = lean_ctor_get(v_b_3178_, 0);
lean_inc(v_val_3195_);
v_tail_3196_ = lean_ctor_get(v_as_x27_3177_, 1);
v_fst_3197_ = lean_ctor_get(v_head_3179_, 0);
v_leftCount_3198_ = lean_ctor_get(v_snd_3180_, 0);
v_rightCount_3199_ = lean_ctor_get(v_snd_3180_, 2);
v_val_3200_ = lean_ctor_get(v_leftIndex_3181_, 0);
v_val_3201_ = lean_ctor_get(v_rightIndex_3182_, 0);
v_fst_3202_ = lean_ctor_get(v_val_3195_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v_val_3195_);
if (v_isSharedCheck_3223_ == 0)
{
lean_object* v_unused_3224_; 
v_unused_3224_ = lean_ctor_get(v_val_3195_, 1);
lean_dec(v_unused_3224_);
v___x_3204_ = v_val_3195_;
v_isShared_3205_ = v_isSharedCheck_3223_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_fst_3202_);
lean_dec(v_val_3195_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3223_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; uint8_t v___x_3207_; 
v___x_3206_ = lean_nat_add(v_leftCount_3198_, v_rightCount_3199_);
v___x_3207_ = lean_nat_dec_lt(v___x_3206_, v_fst_3202_);
lean_dec(v_fst_3202_);
if (v___x_3207_ == 0)
{
lean_dec(v___x_3206_);
lean_del_object(v___x_3204_);
v_as_x27_3177_ = v_tail_3196_;
goto _start;
}
else
{
lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3221_; 
v_isSharedCheck_3221_ = !lean_is_exclusive(v_b_3178_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v_b_3178_, 0);
lean_dec(v_unused_3222_);
v___x_3210_ = v_b_3178_;
v_isShared_3211_ = v_isSharedCheck_3221_;
goto v_resetjp_3209_;
}
else
{
lean_dec(v_b_3178_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3221_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
lean_inc(v_val_3201_);
lean_inc(v_val_3200_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v_val_3201_);
lean_ctor_set(v___x_3204_, 0, v_val_3200_);
v___x_3213_ = v___x_3204_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_val_3200_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_val_3201_);
v___x_3213_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
lean_inc(v_fst_3197_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v_fst_3197_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3206_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3215_);
v___x_3217_ = v___x_3210_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
v_as_x27_3177_ = v_tail_3196_;
v_b_3178_ = v___x_3217_;
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
lean_object* v_tail_3225_; 
v_tail_3225_ = lean_ctor_get(v_as_x27_3177_, 1);
v_as_x27_3177_ = v_tail_3225_;
goto _start;
}
}
else
{
lean_object* v_tail_3227_; 
v_tail_3227_ = lean_ctor_get(v_as_x27_3177_, 1);
v_as_x27_3177_ = v_tail_3227_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg___boxed(lean_object* v_as_x27_3229_, lean_object* v_b_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3229_, v_b_3230_);
lean_dec(v_as_x27_3229_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(lean_object* v_histogram_3232_, lean_object* v_index_3233_, lean_object* v_val_3234_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3232_, v_val_3234_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3236_ = lean_unsigned_to_nat(0u);
v___x_3237_ = lean_box(0);
v___x_3238_ = lean_unsigned_to_nat(1u);
v___x_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3239_, 0, v_index_3233_);
v___x_3240_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3236_);
lean_ctor_set(v___x_3240_, 1, v___x_3237_);
lean_ctor_set(v___x_3240_, 2, v___x_3238_);
lean_ctor_set(v___x_3240_, 3, v___x_3239_);
v___x_3241_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3232_, v_val_3234_, v___x_3240_);
return v___x_3241_;
}
else
{
lean_object* v_val_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3263_; 
v_val_3242_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3244_ = v___x_3235_;
v_isShared_3245_ = v_isSharedCheck_3263_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_val_3242_);
lean_dec(v___x_3235_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3263_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v_leftCount_3246_; lean_object* v_leftIndex_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3260_; 
v_leftCount_3246_ = lean_ctor_get(v_val_3242_, 0);
v_leftIndex_3247_ = lean_ctor_get(v_val_3242_, 1);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_val_3242_);
if (v_isSharedCheck_3260_ == 0)
{
lean_object* v_unused_3261_; lean_object* v_unused_3262_; 
v_unused_3261_ = lean_ctor_get(v_val_3242_, 3);
lean_dec(v_unused_3261_);
v_unused_3262_ = lean_ctor_get(v_val_3242_, 2);
lean_dec(v_unused_3262_);
v___x_3249_ = v_val_3242_;
v_isShared_3250_ = v_isSharedCheck_3260_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_leftIndex_3247_);
lean_inc(v_leftCount_3246_);
lean_dec(v_val_3242_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3260_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3251_ = lean_unsigned_to_nat(1u);
v___x_3252_ = lean_nat_add(v_leftCount_3246_, v___x_3251_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v_index_3233_);
v___x_3254_ = v___x_3244_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_index_3233_);
v___x_3254_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3256_; 
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 3, v___x_3254_);
lean_ctor_set(v___x_3249_, 2, v___x_3252_);
v___x_3256_ = v___x_3249_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_leftCount_3246_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_leftIndex_3247_);
lean_ctor_set(v_reuseFailAlloc_3258_, 2, v___x_3252_);
lean_ctor_set(v_reuseFailAlloc_3258_, 3, v___x_3254_);
v___x_3256_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3232_, v_val_3234_, v___x_3256_);
return v___x_3257_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(lean_object* v_upperBound_3264_, lean_object* v___x_3265_, lean_object* v_fst_3266_, lean_object* v___x_3267_, lean_object* v_a_3268_, lean_object* v_b_3269_){
_start:
{
uint8_t v___x_3270_; 
v___x_3270_ = lean_nat_dec_lt(v_a_3268_, v_upperBound_3264_);
if (v___x_3270_ == 0)
{
lean_dec(v_a_3268_);
return v_b_3269_;
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3271_ = l_Subarray_get___redArg(v_fst_3266_, v_a_3268_);
lean_inc(v_a_3268_);
v___x_3272_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_b_3269_, v_a_3268_, v___x_3271_);
v___x_3273_ = lean_unsigned_to_nat(1u);
v___x_3274_ = lean_nat_add(v_a_3268_, v___x_3273_);
lean_dec(v_a_3268_);
v_a_3268_ = v___x_3274_;
v_b_3269_ = v___x_3272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg___boxed(lean_object* v_upperBound_3276_, lean_object* v___x_3277_, lean_object* v_fst_3278_, lean_object* v___x_3279_, lean_object* v_a_3280_, lean_object* v_b_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3276_, v___x_3277_, v_fst_3278_, v___x_3279_, v_a_3280_, v_b_3281_);
lean_dec(v___x_3279_);
lean_dec_ref(v_fst_3278_);
lean_dec(v___x_3277_);
lean_dec(v_upperBound_3276_);
return v_res_3282_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3283_ = lean_box(0);
v___x_3284_ = lean_unsigned_to_nat(16u);
v___x_3285_ = lean_mk_array(v___x_3284_, v___x_3283_);
return v___x_3285_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v_hist_3288_; 
v___x_3286_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0);
v___x_3287_ = lean_unsigned_to_nat(0u);
v_hist_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3288_, 0, v___x_3287_);
lean_ctor_set(v_hist_3288_, 1, v___x_3286_);
return v_hist_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v_left_3289_, lean_object* v_right_3290_){
_start:
{
lean_object* v___x_3291_; lean_object* v_snd_3292_; lean_object* v_fst_3293_; lean_object* v_fst_3294_; lean_object* v_snd_3295_; lean_object* v___x_3296_; lean_object* v_snd_3297_; lean_object* v_fst_3298_; lean_object* v_fst_3299_; lean_object* v_snd_3300_; lean_object* v_start_3301_; lean_object* v_stop_3302_; lean_object* v___x_3303_; lean_object* v_hist_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v_start_3307_; lean_object* v_stop_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v_buckets_3311_; lean_object* v___x_3312_; lean_object* v___y_3314_; lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; 
v___x_3291_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(v_left_3289_, v_right_3290_);
v_snd_3292_ = lean_ctor_get(v___x_3291_, 1);
lean_inc(v_snd_3292_);
v_fst_3293_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_fst_3293_);
lean_dec_ref(v___x_3291_);
v_fst_3294_ = lean_ctor_get(v_snd_3292_, 0);
lean_inc(v_fst_3294_);
v_snd_3295_ = lean_ctor_get(v_snd_3292_, 1);
lean_inc(v_snd_3295_);
lean_dec(v_snd_3292_);
v___x_3296_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(v_fst_3294_, v_snd_3295_);
v_snd_3297_ = lean_ctor_get(v___x_3296_, 1);
lean_inc(v_snd_3297_);
v_fst_3298_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_fst_3298_);
lean_dec_ref(v___x_3296_);
v_fst_3299_ = lean_ctor_get(v_snd_3297_, 0);
lean_inc(v_fst_3299_);
v_snd_3300_ = lean_ctor_get(v_snd_3297_, 1);
lean_inc(v_snd_3300_);
lean_dec(v_snd_3297_);
v_start_3301_ = lean_ctor_get(v_fst_3298_, 1);
v_stop_3302_ = lean_ctor_get(v_fst_3298_, 2);
v___x_3303_ = lean_unsigned_to_nat(0u);
v_hist_3304_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1);
v___x_3305_ = lean_nat_sub(v_stop_3302_, v_start_3301_);
v___x_3306_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v___x_3305_, v_fst_3299_, v___x_3305_, v_fst_3298_, v___x_3303_, v_hist_3304_);
v_start_3307_ = lean_ctor_get(v_fst_3299_, 1);
v_stop_3308_ = lean_ctor_get(v_fst_3299_, 2);
v___x_3309_ = lean_nat_sub(v_stop_3308_, v_start_3307_);
v___x_3310_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v___x_3309_, v___x_3309_, v_fst_3299_, v___x_3305_, v___x_3303_, v___x_3306_);
lean_dec(v___x_3305_);
lean_dec(v___x_3309_);
v_buckets_3311_ = lean_ctor_get(v___x_3310_, 1);
lean_inc_ref(v_buckets_3311_);
lean_dec_ref(v___x_3310_);
v___x_3312_ = lean_box(0);
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_array_get_size(v_buckets_3311_);
v___x_3342_ = lean_nat_dec_lt(v___x_3303_, v___x_3341_);
if (v___x_3342_ == 0)
{
lean_dec_ref(v_buckets_3311_);
v___y_3314_ = v___x_3340_;
goto v___jp_3313_;
}
else
{
size_t v___x_3343_; size_t v___x_3344_; lean_object* v___x_3345_; 
v___x_3343_ = lean_usize_of_nat(v___x_3341_);
v___x_3344_ = ((size_t)0ULL);
v___x_3345_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_buckets_3311_, v___x_3343_, v___x_3344_, v___x_3340_);
lean_dec_ref(v_buckets_3311_);
v___y_3314_ = v___x_3345_;
goto v___jp_3313_;
}
v___jp_3313_:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v___y_3314_, v___x_3312_);
lean_dec(v___y_3314_);
if (lean_obj_tag(v___x_3315_) == 1)
{
lean_object* v_val_3316_; lean_object* v_snd_3317_; lean_object* v_snd_3318_; lean_object* v_fst_3319_; lean_object* v_fst_3320_; lean_object* v_snd_3321_; lean_object* v___x_3322_; lean_object* v_fst_3323_; lean_object* v_snd_3324_; lean_object* v___x_3325_; lean_object* v_fst_3326_; lean_object* v_snd_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_val_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_val_3316_);
lean_dec_ref_known(v___x_3315_, 1);
v_snd_3317_ = lean_ctor_get(v_val_3316_, 1);
lean_inc(v_snd_3317_);
lean_dec(v_val_3316_);
v_snd_3318_ = lean_ctor_get(v_snd_3317_, 1);
lean_inc(v_snd_3318_);
v_fst_3319_ = lean_ctor_get(v_snd_3317_, 0);
lean_inc(v_fst_3319_);
lean_dec(v_snd_3317_);
v_fst_3320_ = lean_ctor_get(v_snd_3318_, 0);
lean_inc(v_fst_3320_);
v_snd_3321_ = lean_ctor_get(v_snd_3318_, 1);
lean_inc(v_snd_3321_);
lean_dec(v_snd_3318_);
v___x_3322_ = l_Subarray_split___redArg(v_fst_3298_, v_fst_3320_);
lean_dec(v_fst_3320_);
v_fst_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_fst_3323_);
v_snd_3324_ = lean_ctor_get(v___x_3322_, 1);
lean_inc(v_snd_3324_);
lean_dec_ref(v___x_3322_);
v___x_3325_ = l_Subarray_split___redArg(v_fst_3299_, v_snd_3321_);
lean_dec(v_snd_3321_);
v_fst_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_fst_3326_);
v_snd_3327_ = lean_ctor_get(v___x_3325_, 1);
lean_inc(v_snd_3327_);
lean_dec_ref(v___x_3325_);
v___x_3328_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v_fst_3323_, v_fst_3326_);
v___x_3329_ = l_Array_append___redArg(v_fst_3293_, v___x_3328_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = lean_unsigned_to_nat(1u);
v___x_3331_ = lean_mk_empty_array_with_capacity(v___x_3330_);
v___x_3332_ = lean_array_push(v___x_3331_, v_fst_3319_);
v___x_3333_ = l_Array_append___redArg(v___x_3329_, v___x_3332_);
lean_dec_ref(v___x_3332_);
v___x_3334_ = l_Subarray_drop___redArg(v_snd_3324_, v___x_3330_);
v___x_3335_ = l_Subarray_drop___redArg(v_snd_3327_, v___x_3330_);
v___x_3336_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3334_, v___x_3335_);
v___x_3337_ = l_Array_append___redArg(v___x_3333_, v___x_3336_);
lean_dec_ref(v___x_3336_);
v___x_3338_ = l_Array_append___redArg(v___x_3337_, v_snd_3300_);
lean_dec(v_snd_3300_);
return v___x_3338_;
}
else
{
lean_object* v___x_3339_; 
lean_dec(v___x_3315_);
lean_dec(v_fst_3299_);
lean_dec(v_fst_3298_);
v___x_3339_ = l_Array_append___redArg(v_fst_3293_, v_snd_3300_);
lean_dec(v_snd_3300_);
return v___x_3339_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_3346_, lean_object* v_original_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v_fst_3349_; lean_object* v_snd_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3369_; 
v_fst_3349_ = lean_ctor_get(v_a_3348_, 0);
v_snd_3350_ = lean_ctor_get(v_a_3348_, 1);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_a_3348_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3352_ = v_a_3348_;
v_isShared_3353_ = v_isSharedCheck_3369_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_snd_3350_);
lean_inc(v_fst_3349_);
lean_dec(v_a_3348_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3369_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
uint8_t v___x_3354_; 
v___x_3354_ = lean_nat_dec_lt(v_snd_3350_, v___x_3346_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3356_; 
if (v_isShared_3353_ == 0)
{
v___x_3356_ = v___x_3352_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_fst_3349_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v_snd_3350_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
else
{
uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3358_ = 1;
v___x_3359_ = lean_array_fget_borrowed(v_original_3347_, v_snd_3350_);
v___x_3360_ = lean_box(v___x_3358_);
lean_inc(v___x_3359_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 1, v___x_3359_);
lean_ctor_set(v___x_3352_, 0, v___x_3360_);
v___x_3362_ = v___x_3352_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v___x_3359_);
v___x_3362_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3363_ = lean_array_push(v_fst_3349_, v___x_3362_);
v___x_3364_ = lean_unsigned_to_nat(1u);
v___x_3365_ = lean_nat_add(v_snd_3350_, v___x_3364_);
lean_dec(v_snd_3350_);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3363_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v_a_3348_ = v___x_3366_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_3370_, lean_object* v_original_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3370_, v_original_3371_, v_a_3372_);
lean_dec_ref(v_original_3371_);
lean_dec(v___x_3370_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_3374_, size_t v_i_3375_, lean_object* v_bs_3376_){
_start:
{
uint8_t v___x_3377_; 
v___x_3377_ = lean_usize_dec_lt(v_i_3375_, v_sz_3374_);
if (v___x_3377_ == 0)
{
return v_bs_3376_;
}
else
{
lean_object* v_v_3378_; lean_object* v___x_3379_; lean_object* v_bs_x27_3380_; uint8_t v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; size_t v___x_3384_; size_t v___x_3385_; lean_object* v___x_3386_; 
v_v_3378_ = lean_array_uget(v_bs_3376_, v_i_3375_);
v___x_3379_ = lean_unsigned_to_nat(0u);
v_bs_x27_3380_ = lean_array_uset(v_bs_3376_, v_i_3375_, v___x_3379_);
v___x_3381_ = 0;
v___x_3382_ = lean_box(v___x_3381_);
v___x_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
lean_ctor_set(v___x_3383_, 1, v_v_3378_);
v___x_3384_ = ((size_t)1ULL);
v___x_3385_ = lean_usize_add(v_i_3375_, v___x_3384_);
v___x_3386_ = lean_array_uset(v_bs_x27_3380_, v_i_3375_, v___x_3383_);
v_i_3375_ = v___x_3385_;
v_bs_3376_ = v___x_3386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_3388_, lean_object* v_i_3389_, lean_object* v_bs_3390_){
_start:
{
size_t v_sz_boxed_3391_; size_t v_i_boxed_3392_; lean_object* v_res_3393_; 
v_sz_boxed_3391_ = lean_unbox_usize(v_sz_3388_);
lean_dec(v_sz_3388_);
v_i_boxed_3392_ = lean_unbox_usize(v_i_3389_);
lean_dec(v_i_3389_);
v_res_3393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_3391_, v_i_boxed_3392_, v_bs_3390_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_3394_, lean_object* v_edited_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v_fst_3397_; lean_object* v_snd_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3417_; 
v_fst_3397_ = lean_ctor_get(v_a_3396_, 0);
v_snd_3398_ = lean_ctor_get(v_a_3396_, 1);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_a_3396_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3400_ = v_a_3396_;
v_isShared_3401_ = v_isSharedCheck_3417_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_snd_3398_);
lean_inc(v_fst_3397_);
lean_dec(v_a_3396_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3417_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
uint8_t v___x_3402_; 
v___x_3402_ = lean_nat_dec_lt(v_snd_3398_, v___x_3394_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3404_; 
if (v_isShared_3401_ == 0)
{
v___x_3404_ = v___x_3400_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_fst_3397_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_snd_3398_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
else
{
uint8_t v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3410_; 
v___x_3406_ = 0;
v___x_3407_ = lean_array_fget_borrowed(v_edited_3395_, v_snd_3398_);
v___x_3408_ = lean_box(v___x_3406_);
lean_inc(v___x_3407_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 1, v___x_3407_);
lean_ctor_set(v___x_3400_, 0, v___x_3408_);
v___x_3410_ = v___x_3400_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v___x_3407_);
v___x_3410_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3411_ = lean_array_push(v_fst_3397_, v___x_3410_);
v___x_3412_ = lean_unsigned_to_nat(1u);
v___x_3413_ = lean_nat_add(v_snd_3398_, v___x_3412_);
lean_dec(v_snd_3398_);
v___x_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3411_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
v_a_3396_ = v___x_3414_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_3418_, lean_object* v_edited_3419_, lean_object* v_a_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3418_, v_edited_3419_, v_a_3420_);
lean_dec_ref(v_edited_3419_);
lean_dec(v___x_3418_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3422_, size_t v_i_3423_, lean_object* v_bs_3424_){
_start:
{
uint8_t v___x_3425_; 
v___x_3425_ = lean_usize_dec_lt(v_i_3423_, v_sz_3422_);
if (v___x_3425_ == 0)
{
return v_bs_3424_;
}
else
{
lean_object* v_v_3426_; lean_object* v___x_3427_; lean_object* v_bs_x27_3428_; uint8_t v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; size_t v___x_3432_; size_t v___x_3433_; lean_object* v___x_3434_; 
v_v_3426_ = lean_array_uget(v_bs_3424_, v_i_3423_);
v___x_3427_ = lean_unsigned_to_nat(0u);
v_bs_x27_3428_ = lean_array_uset(v_bs_3424_, v_i_3423_, v___x_3427_);
v___x_3429_ = 1;
v___x_3430_ = lean_box(v___x_3429_);
v___x_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
lean_ctor_set(v___x_3431_, 1, v_v_3426_);
v___x_3432_ = ((size_t)1ULL);
v___x_3433_ = lean_usize_add(v_i_3423_, v___x_3432_);
v___x_3434_ = lean_array_uset(v_bs_x27_3428_, v_i_3423_, v___x_3431_);
v_i_3423_ = v___x_3433_;
v_bs_3424_ = v___x_3434_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3436_, lean_object* v_i_3437_, lean_object* v_bs_3438_){
_start:
{
size_t v_sz_boxed_3439_; size_t v_i_boxed_3440_; lean_object* v_res_3441_; 
v_sz_boxed_3439_ = lean_unbox_usize(v_sz_3436_);
lean_dec(v_sz_3436_);
v_i_boxed_3440_ = lean_unbox_usize(v_i_3437_);
lean_dec(v_i_3437_);
v_res_3441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3439_, v_i_boxed_3440_, v_bs_3438_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3449_, lean_object* v_edited_3450_){
_start:
{
lean_object* v_i_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v_i_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = lean_array_get_size(v_original_3449_);
v___x_3453_ = lean_nat_dec_lt(v_i_3451_, v___x_3452_);
if (v___x_3453_ == 0)
{
size_t v_sz_3454_; size_t v___x_3455_; lean_object* v___x_3456_; 
lean_dec_ref(v_original_3449_);
v_sz_3454_ = lean_array_size(v_edited_3450_);
v___x_3455_ = ((size_t)0ULL);
v___x_3456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3454_, v___x_3455_, v_edited_3450_);
return v___x_3456_;
}
else
{
lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3457_ = lean_array_get_size(v_edited_3450_);
v___x_3458_ = lean_nat_dec_lt(v_i_3451_, v___x_3457_);
if (v___x_3458_ == 0)
{
size_t v_sz_3459_; size_t v___x_3460_; lean_object* v___x_3461_; 
lean_dec_ref(v_edited_3450_);
v_sz_3459_ = lean_array_size(v_original_3449_);
v___x_3460_ = ((size_t)0ULL);
v___x_3461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3459_, v___x_3460_, v_original_3449_);
return v___x_3461_;
}
else
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v_ds_3464_; lean_object* v___x_3465_; size_t v_sz_3466_; size_t v___x_3467_; lean_object* v___x_3468_; lean_object* v_snd_3469_; lean_object* v_fst_3470_; lean_object* v_fst_3471_; lean_object* v_snd_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3491_; 
lean_inc_ref(v_original_3449_);
v___x_3462_ = l_Array_toSubarray___redArg(v_original_3449_, v_i_3451_, v___x_3452_);
lean_inc_ref(v_edited_3450_);
v___x_3463_ = l_Array_toSubarray___redArg(v_edited_3450_, v_i_3451_, v___x_3457_);
v_ds_3464_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3462_, v___x_3463_);
v___x_3465_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3466_ = lean_array_size(v_ds_3464_);
v___x_3467_ = ((size_t)0ULL);
v___x_3468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_3450_, v___x_3457_, v_original_3449_, v___x_3452_, v_ds_3464_, v_sz_3466_, v___x_3467_, v___x_3465_);
lean_dec_ref(v_ds_3464_);
v_snd_3469_ = lean_ctor_get(v___x_3468_, 1);
lean_inc(v_snd_3469_);
v_fst_3470_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_fst_3470_);
lean_dec_ref(v___x_3468_);
v_fst_3471_ = lean_ctor_get(v_snd_3469_, 0);
v_snd_3472_ = lean_ctor_get(v_snd_3469_, 1);
v_isSharedCheck_3491_ = !lean_is_exclusive(v_snd_3469_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3474_ = v_snd_3469_;
v_isShared_3475_ = v_isSharedCheck_3491_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_snd_3472_);
lean_inc(v_fst_3471_);
lean_dec(v_snd_3469_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3491_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 1, v_fst_3471_);
lean_ctor_set(v___x_3474_, 0, v_fst_3470_);
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_fst_3470_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_fst_3471_);
v___x_3477_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3478_; lean_object* v_fst_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3488_; 
v___x_3478_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3452_, v_original_3449_, v___x_3477_);
lean_dec_ref(v_original_3449_);
v_fst_3479_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; 
v_unused_3489_ = lean_ctor_get(v___x_3478_, 1);
lean_dec(v_unused_3489_);
v___x_3481_ = v___x_3478_;
v_isShared_3482_ = v_isSharedCheck_3488_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_fst_3479_);
lean_dec(v___x_3478_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3488_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v_snd_3472_);
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_fst_3479_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_snd_3472_);
v___x_3484_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v___x_3485_; lean_object* v_fst_3486_; 
v___x_3485_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3457_, v_edited_3450_, v___x_3484_);
lean_dec_ref(v_edited_3450_);
v_fst_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_fst_3486_);
lean_dec_ref(v___x_3485_);
return v_fst_3486_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3492_, lean_object* v_x_3493_, lean_object* v_x_3494_){
_start:
{
if (lean_obj_tag(v_x_3493_) == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = l_List_reverse___redArg(v_x_3494_);
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
return v___x_3497_;
}
else
{
lean_object* v_head_3498_; lean_object* v_tail_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3508_; 
v_head_3498_ = lean_ctor_get(v_x_3493_, 0);
v_tail_3499_ = lean_ctor_get(v_x_3493_, 1);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_x_3493_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3501_ = v_x_3493_;
v_isShared_3502_ = v_isSharedCheck_3508_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_tail_3499_);
lean_inc(v_head_3498_);
lean_dec(v_x_3493_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3508_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3503_; lean_object* v___x_3505_; 
v___x_3503_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3498_, v___y_3492_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 1, v_x_3494_);
lean_ctor_set(v___x_3501_, 0, v___x_3503_);
v___x_3505_ = v___x_3501_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3503_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_x_3494_);
v___x_3505_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
v_x_3493_ = v_tail_3499_;
v_x_3494_ = v___x_3505_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3509_, lean_object* v_x_3510_, lean_object* v_x_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3509_, v_x_3510_, v_x_3511_);
lean_dec(v___y_3509_);
return v_res_3513_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0));
v___x_3516_ = l_Lean_stringToMessageData(v___x_3515_);
return v___x_3516_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = l_Lean_MessageLog_empty;
v___x_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_){
_start:
{
lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; uint8_t v___y_3575_; uint8_t v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; uint8_t v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; uint8_t v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v_dc_x3f_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
v___x_3778_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
lean_inc(v_x_3530_);
v___x_3779_ = l_Lean_Syntax_isOfKind(v_x_3530_, v___x_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; 
lean_dec(v_x_3530_);
v___x_3780_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3780_;
}
else
{
lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3781_ = lean_unsigned_to_nat(0u);
v___x_3782_ = l_Lean_Syntax_getArg(v_x_3530_, v___x_3781_);
v___x_3783_ = l_Lean_Syntax_isNone(v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; uint8_t v___x_3785_; 
v___x_3784_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3782_);
v___x_3785_ = l_Lean_Syntax_matchesNull(v___x_3782_, v___x_3784_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; 
lean_dec(v___x_3782_);
lean_dec(v_x_3530_);
v___x_3786_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3786_;
}
else
{
lean_object* v_dc_x3f_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v_dc_x3f_3787_ = l_Lean_Syntax_getArg(v___x_3782_, v___x_3781_);
lean_dec(v___x_3782_);
v___x_3788_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3787_);
v___x_3789_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3787_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; 
lean_dec(v_dc_x3f_3787_);
lean_dec(v_x_3530_);
v___x_3790_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3790_;
}
else
{
lean_object* v___x_3791_; 
v___x_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3791_, 0, v_dc_x3f_3787_);
v_dc_x3f_3759_ = v___x_3791_;
v___y_3760_ = v_a_3531_;
v___y_3761_ = v_a_3532_;
goto v___jp_3758_;
}
}
}
else
{
lean_object* v___x_3792_; 
lean_dec(v___x_3782_);
v___x_3792_ = lean_box(0);
v_dc_x3f_3759_ = v___x_3792_;
v___y_3760_ = v_a_3531_;
v___y_3761_ = v_a_3532_;
goto v___jp_3758_;
}
}
v___jp_3534_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3540_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1);
v___x_3541_ = l_Lean_stringToMessageData(v___y_3539_);
v___x_3542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3540_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3537_, v___x_3542_, v___y_3538_, v___y_3535_);
lean_dec(v___y_3537_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3564_; 
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3564_ == 0)
{
lean_object* v_unused_3565_; 
v_unused_3565_ = lean_ctor_get(v___x_3543_, 0);
lean_dec(v_unused_3565_);
v___x_3545_ = v___x_3543_;
v_isShared_3546_ = v_isSharedCheck_3564_;
goto v_resetjp_3544_;
}
else
{
lean_dec(v___x_3543_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3564_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3547_; 
v___x_3547_ = l_Lean_Elab_Command_getRef___redArg(v___y_3538_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3553_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
v___x_3549_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
lean_ctor_set(v___x_3550_, 1, v___y_3536_);
v___x_3551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3551_, 0, v_a_3548_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set_tag(v___x_3545_, 10);
lean_ctor_set(v___x_3545_, 0, v___x_3551_);
v___x_3553_ = v___x_3545_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3553_, v___y_3538_, v___y_3535_);
return v___x_3554_;
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_del_object(v___x_3545_);
lean_dec_ref(v___y_3536_);
v_a_3556_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3547_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3547_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3536_);
return v___x_3543_;
}
}
v___jp_3566_:
{
if (v___y_3575_ == 0)
{
lean_object* v___x_3576_; lean_object* v_env_3577_; lean_object* v_scopes_3578_; lean_object* v_usedQuotCtxts_3579_; lean_object* v_nextMacroScope_3580_; lean_object* v_maxRecDepth_3581_; lean_object* v_ngen_3582_; lean_object* v_auxDeclNGen_3583_; lean_object* v_infoState_3584_; lean_object* v_traceState_3585_; lean_object* v_snapshotTasks_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3612_; 
lean_dec(v___y_3571_);
v___x_3576_ = lean_st_ref_take(v___y_3568_);
v_env_3577_ = lean_ctor_get(v___x_3576_, 0);
v_scopes_3578_ = lean_ctor_get(v___x_3576_, 2);
v_usedQuotCtxts_3579_ = lean_ctor_get(v___x_3576_, 3);
v_nextMacroScope_3580_ = lean_ctor_get(v___x_3576_, 4);
v_maxRecDepth_3581_ = lean_ctor_get(v___x_3576_, 5);
v_ngen_3582_ = lean_ctor_get(v___x_3576_, 6);
v_auxDeclNGen_3583_ = lean_ctor_get(v___x_3576_, 7);
v_infoState_3584_ = lean_ctor_get(v___x_3576_, 8);
v_traceState_3585_ = lean_ctor_get(v___x_3576_, 9);
v_snapshotTasks_3586_ = lean_ctor_get(v___x_3576_, 10);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; 
v_unused_3613_ = lean_ctor_get(v___x_3576_, 1);
lean_dec(v_unused_3613_);
v___x_3588_ = v___x_3576_;
v_isShared_3589_ = v_isSharedCheck_3612_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_snapshotTasks_3586_);
lean_inc(v_traceState_3585_);
lean_inc(v_infoState_3584_);
lean_inc(v_auxDeclNGen_3583_);
lean_inc(v_ngen_3582_);
lean_inc(v_maxRecDepth_3581_);
lean_inc(v_nextMacroScope_3580_);
lean_inc(v_usedQuotCtxts_3579_);
lean_inc(v_scopes_3578_);
lean_inc(v_env_3577_);
lean_dec(v___x_3576_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3612_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 1, v___y_3569_);
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_env_3577_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v___y_3569_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_scopes_3578_);
lean_ctor_set(v_reuseFailAlloc_3611_, 3, v_usedQuotCtxts_3579_);
lean_ctor_set(v_reuseFailAlloc_3611_, 4, v_nextMacroScope_3580_);
lean_ctor_set(v_reuseFailAlloc_3611_, 5, v_maxRecDepth_3581_);
lean_ctor_set(v_reuseFailAlloc_3611_, 6, v_ngen_3582_);
lean_ctor_set(v_reuseFailAlloc_3611_, 7, v_auxDeclNGen_3583_);
lean_ctor_set(v_reuseFailAlloc_3611_, 8, v_infoState_3584_);
lean_ctor_set(v_reuseFailAlloc_3611_, 9, v_traceState_3585_);
lean_ctor_set(v_reuseFailAlloc_3611_, 10, v_snapshotTasks_3586_);
v___x_3591_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v_scopes_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v_opts_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v___x_3592_ = lean_st_ref_set(v___y_3568_, v___x_3591_);
v___x_3593_ = lean_st_ref_get(v___y_3568_);
v_scopes_3594_ = lean_ctor_get(v___x_3593_, 2);
lean_inc(v_scopes_3594_);
lean_dec(v___x_3593_);
v___x_3595_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3596_ = l_List_head_x21___redArg(v___x_3595_, v_scopes_3594_);
lean_dec(v_scopes_3594_);
v_opts_3597_ = lean_ctor_get(v___x_3596_, 1);
lean_inc_ref(v_opts_3597_);
lean_dec(v___x_3596_);
v___x_3598_ = l_Lean_guard__msgs_diff;
v___x_3599_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3597_, v___x_3598_);
lean_dec_ref(v_opts_3597_);
if (v___x_3599_ == 0)
{
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3567_);
lean_inc_ref(v___y_3572_);
v___y_3535_ = v___y_3568_;
v___y_3536_ = v___y_3572_;
v___y_3537_ = v___y_3573_;
v___y_3538_ = v___y_3574_;
v___y_3539_ = v___y_3572_;
goto v___jp_3534_;
}
else
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3600_ = lean_string_utf8_byte_size(v___y_3570_);
lean_inc(v___y_3567_);
lean_inc_ref(v___y_3570_);
v___x_3601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3601_, 0, v___y_3570_);
lean_ctor_set(v___x_3601_, 1, v___y_3567_);
lean_ctor_set(v___x_3601_, 2, v___x_3600_);
v___x_3602_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3601_);
v___x_3603_ = lean_mk_empty_array_with_capacity(v___y_3567_);
lean_inc_ref(v___x_3603_);
v___x_3604_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3570_, v___x_3601_, v___x_3600_, v___x_3602_, v___x_3603_);
lean_dec_ref_known(v___x_3601_, 3);
v___x_3605_ = lean_string_utf8_byte_size(v___y_3572_);
lean_inc_ref_n(v___y_3572_, 2);
v___x_3606_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3606_, 0, v___y_3572_);
lean_ctor_set(v___x_3606_, 1, v___y_3567_);
lean_ctor_set(v___x_3606_, 2, v___x_3605_);
v___x_3607_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3606_);
v___x_3608_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3572_, v___x_3606_, v___x_3605_, v___x_3607_, v___x_3603_);
lean_dec_ref_known(v___x_3606_, 3);
v___x_3609_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3604_, v___x_3608_);
v___x_3610_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3609_);
lean_dec_ref(v___x_3609_);
v___y_3535_ = v___y_3568_;
v___y_3536_ = v___y_3572_;
v___y_3537_ = v___y_3573_;
v___y_3538_ = v___y_3574_;
v___y_3539_ = v___x_3610_;
goto v___jp_3534_;
}
}
}
}
else
{
lean_object* v___x_3614_; lean_object* v_env_3615_; lean_object* v_scopes_3616_; lean_object* v_usedQuotCtxts_3617_; lean_object* v_nextMacroScope_3618_; lean_object* v_maxRecDepth_3619_; lean_object* v_ngen_3620_; lean_object* v_auxDeclNGen_3621_; lean_object* v_infoState_3622_; lean_object* v_traceState_3623_; lean_object* v_snapshotTasks_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3634_; 
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3567_);
v___x_3614_ = lean_st_ref_take(v___y_3568_);
v_env_3615_ = lean_ctor_get(v___x_3614_, 0);
v_scopes_3616_ = lean_ctor_get(v___x_3614_, 2);
v_usedQuotCtxts_3617_ = lean_ctor_get(v___x_3614_, 3);
v_nextMacroScope_3618_ = lean_ctor_get(v___x_3614_, 4);
v_maxRecDepth_3619_ = lean_ctor_get(v___x_3614_, 5);
v_ngen_3620_ = lean_ctor_get(v___x_3614_, 6);
v_auxDeclNGen_3621_ = lean_ctor_get(v___x_3614_, 7);
v_infoState_3622_ = lean_ctor_get(v___x_3614_, 8);
v_traceState_3623_ = lean_ctor_get(v___x_3614_, 9);
v_snapshotTasks_3624_ = lean_ctor_get(v___x_3614_, 10);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3634_ == 0)
{
lean_object* v_unused_3635_; 
v_unused_3635_ = lean_ctor_get(v___x_3614_, 1);
lean_dec(v_unused_3635_);
v___x_3626_ = v___x_3614_;
v_isShared_3627_ = v_isSharedCheck_3634_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_snapshotTasks_3624_);
lean_inc(v_traceState_3623_);
lean_inc(v_infoState_3622_);
lean_inc(v_auxDeclNGen_3621_);
lean_inc(v_ngen_3620_);
lean_inc(v_maxRecDepth_3619_);
lean_inc(v_nextMacroScope_3618_);
lean_inc(v_usedQuotCtxts_3617_);
lean_inc(v_scopes_3616_);
lean_inc(v_env_3615_);
lean_dec(v___x_3614_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3634_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 1, v___y_3571_);
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_env_3615_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v___y_3571_);
lean_ctor_set(v_reuseFailAlloc_3633_, 2, v_scopes_3616_);
lean_ctor_set(v_reuseFailAlloc_3633_, 3, v_usedQuotCtxts_3617_);
lean_ctor_set(v_reuseFailAlloc_3633_, 4, v_nextMacroScope_3618_);
lean_ctor_set(v_reuseFailAlloc_3633_, 5, v_maxRecDepth_3619_);
lean_ctor_set(v_reuseFailAlloc_3633_, 6, v_ngen_3620_);
lean_ctor_set(v_reuseFailAlloc_3633_, 7, v_auxDeclNGen_3621_);
lean_ctor_set(v_reuseFailAlloc_3633_, 8, v_infoState_3622_);
lean_ctor_set(v_reuseFailAlloc_3633_, 9, v_traceState_3623_);
lean_ctor_set(v_reuseFailAlloc_3633_, 10, v_snapshotTasks_3624_);
v___x_3629_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3630_ = lean_st_ref_set(v___y_3568_, v___x_3629_);
v___x_3631_ = lean_box(0);
v___x_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
return v___x_3632_;
}
}
}
}
v___jp_3636_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v_a_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v_str_3659_; lean_object* v_startInclusive_3660_; lean_object* v_endExclusive_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3676_; 
v___x_3649_ = l_Lean_MessageLog_toList(v___y_3645_);
lean_dec(v___y_3645_);
v___x_3650_ = lean_box(0);
v___x_3651_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3648_, v___x_3649_, v___x_3650_);
lean_dec(v___y_3648_);
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref(v___x_3651_);
v___x_3653_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3637_, v_a_3652_);
v___x_3654_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3655_ = l_String_intercalate(v___x_3654_, v___x_3653_);
v___x_3656_ = lean_string_utf8_byte_size(v___x_3655_);
lean_inc(v___y_3638_);
v___x_3657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___y_3638_);
lean_ctor_set(v___x_3657_, 2, v___x_3656_);
v___x_3658_ = l_String_Slice_trimAscii(v___x_3657_);
v_str_3659_ = lean_ctor_get(v___x_3658_, 0);
v_startInclusive_3660_ = lean_ctor_get(v___x_3658_, 1);
v_endExclusive_3661_ = lean_ctor_get(v___x_3658_, 2);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3663_ = v___x_3658_;
v_isShared_3664_ = v_isSharedCheck_3676_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_endExclusive_3661_);
lean_inc(v_startInclusive_3660_);
lean_inc(v_str_3659_);
lean_dec(v___x_3658_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3676_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3665_; 
v___x_3665_ = lean_string_utf8_extract(v_str_3659_, v_startInclusive_3660_, v_endExclusive_3661_);
lean_dec(v_endExclusive_3661_);
lean_dec(v_startInclusive_3660_);
lean_dec_ref(v_str_3659_);
if (v___y_3646_ == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; uint8_t v___x_3668_; 
lean_del_object(v___x_3663_);
lean_inc_ref(v___y_3641_);
v___x_3666_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3643_, v___y_3641_);
lean_inc_ref(v___x_3665_);
v___x_3667_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3643_, v___x_3665_);
v___x_3668_ = lean_string_dec_eq(v___x_3666_, v___x_3667_);
lean_dec_ref(v___x_3667_);
lean_dec_ref(v___x_3666_);
v___y_3567_ = v___y_3638_;
v___y_3568_ = v___y_3639_;
v___y_3569_ = v___y_3640_;
v___y_3570_ = v___y_3641_;
v___y_3571_ = v___y_3642_;
v___y_3572_ = v___x_3665_;
v___y_3573_ = v___y_3644_;
v___y_3574_ = v___y_3647_;
v___y_3575_ = v___x_3668_;
goto v___jp_3566_;
}
else
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
lean_inc_ref(v___x_3665_);
v___x_3669_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3643_, v___x_3665_);
lean_inc_ref(v___y_3641_);
v___x_3670_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3643_, v___y_3641_);
v___x_3671_ = lean_string_utf8_byte_size(v___x_3669_);
lean_inc(v___y_3638_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 2, v___x_3671_);
lean_ctor_set(v___x_3663_, 1, v___y_3638_);
lean_ctor_set(v___x_3663_, 0, v___x_3669_);
v___x_3673_ = v___x_3663_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v___y_3638_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
uint8_t v___x_3674_; 
v___x_3674_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3670_, v___x_3673_);
lean_dec_ref(v___x_3673_);
v___y_3567_ = v___y_3638_;
v___y_3568_ = v___y_3639_;
v___y_3569_ = v___y_3640_;
v___y_3570_ = v___y_3641_;
v___y_3571_ = v___y_3642_;
v___y_3572_ = v___x_3665_;
v___y_3573_ = v___y_3644_;
v___y_3574_ = v___y_3647_;
v___y_3575_ = v___x_3674_;
goto v___jp_3566_;
}
}
}
}
v___jp_3677_:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3681_, v___y_3680_, v___y_3678_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v_filterFn_3686_; uint8_t v_whitespace_3687_; uint8_t v_ordering_3688_; uint8_t v_reportPositions_3689_; uint8_t v_substring_3690_; lean_object* v___x_3691_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
lean_dec_ref_known(v___x_3684_, 1);
v_filterFn_3686_ = lean_ctor_get(v_a_3685_, 0);
lean_inc_ref(v_filterFn_3686_);
v_whitespace_3687_ = lean_ctor_get_uint8(v_a_3685_, sizeof(void*)*1);
v_ordering_3688_ = lean_ctor_get_uint8(v_a_3685_, sizeof(void*)*1 + 1);
v_reportPositions_3689_ = lean_ctor_get_uint8(v_a_3685_, sizeof(void*)*1 + 2);
v_substring_3690_ = lean_ctor_get_uint8(v_a_3685_, sizeof(void*)*1 + 3);
lean_dec(v_a_3685_);
v___x_3691_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3682_, v___y_3680_, v___y_3678_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v_a_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v_str_3701_; lean_object* v_startInclusive_3702_; lean_object* v_endExclusive_3703_; lean_object* v_fst_3704_; lean_object* v_snd_3705_; lean_object* v_fileMap_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref_known(v___x_3691_, 1);
v___x_3693_ = l_Lean_MessageLog_toList(v_a_3692_);
v___x_3694_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3695_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3686_, v___x_3693_, v___x_3694_);
lean_dec(v___x_3693_);
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref(v___x_3695_);
v___x_3697_ = lean_unsigned_to_nat(0u);
v___x_3698_ = lean_string_utf8_byte_size(v___y_3683_);
v___x_3699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3699_, 0, v___y_3683_);
lean_ctor_set(v___x_3699_, 1, v___x_3697_);
lean_ctor_set(v___x_3699_, 2, v___x_3698_);
v___x_3700_ = l_String_Slice_trimAscii(v___x_3699_);
v_str_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc_ref(v_str_3701_);
v_startInclusive_3702_ = lean_ctor_get(v___x_3700_, 1);
lean_inc(v_startInclusive_3702_);
v_endExclusive_3703_ = lean_ctor_get(v___x_3700_, 2);
lean_inc(v_endExclusive_3703_);
lean_dec_ref(v___x_3700_);
v_fst_3704_ = lean_ctor_get(v_a_3696_, 0);
lean_inc(v_fst_3704_);
v_snd_3705_ = lean_ctor_get(v_a_3696_, 1);
lean_inc(v_snd_3705_);
lean_dec(v_a_3696_);
v_fileMap_3706_ = lean_ctor_get(v___y_3680_, 1);
v___x_3707_ = lean_string_utf8_extract(v_str_3701_, v_startInclusive_3702_, v_endExclusive_3703_);
lean_dec(v_endExclusive_3703_);
lean_dec(v_startInclusive_3702_);
lean_dec_ref(v_str_3701_);
v___x_3708_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3707_);
if (v_reportPositions_3689_ == 0)
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_box(0);
v___y_3637_ = v_ordering_3688_;
v___y_3638_ = v___x_3697_;
v___y_3639_ = v___y_3678_;
v___y_3640_ = v_a_3692_;
v___y_3641_ = v___x_3708_;
v___y_3642_ = v_snd_3705_;
v___y_3643_ = v_whitespace_3687_;
v___y_3644_ = v___y_3679_;
v___y_3645_ = v_fst_3704_;
v___y_3646_ = v_substring_3690_;
v___y_3647_ = v___y_3680_;
v___y_3648_ = v___x_3709_;
goto v___jp_3636_;
}
else
{
uint8_t v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = 0;
v___x_3711_ = l_Lean_Syntax_getPos_x3f(v___y_3679_, v___x_3710_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_box(0);
v___y_3637_ = v_ordering_3688_;
v___y_3638_ = v___x_3697_;
v___y_3639_ = v___y_3678_;
v___y_3640_ = v_a_3692_;
v___y_3641_ = v___x_3708_;
v___y_3642_ = v_snd_3705_;
v___y_3643_ = v_whitespace_3687_;
v___y_3644_ = v___y_3679_;
v___y_3645_ = v_fst_3704_;
v___y_3646_ = v_substring_3690_;
v___y_3647_ = v___y_3680_;
v___y_3648_ = v___x_3712_;
goto v___jp_3636_;
}
else
{
lean_object* v_val_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3722_; 
v_val_3713_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3715_ = v___x_3711_;
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_val_3713_);
lean_dec(v___x_3711_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; lean_object* v_line_3718_; lean_object* v___x_3720_; 
lean_inc_ref(v_fileMap_3706_);
v___x_3717_ = l_Lean_FileMap_toPosition(v_fileMap_3706_, v_val_3713_);
lean_dec(v_val_3713_);
v_line_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_line_3718_);
lean_dec_ref(v___x_3717_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v_line_3718_);
v___x_3720_ = v___x_3715_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_line_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
v___y_3637_ = v_ordering_3688_;
v___y_3638_ = v___x_3697_;
v___y_3639_ = v___y_3678_;
v___y_3640_ = v_a_3692_;
v___y_3641_ = v___x_3708_;
v___y_3642_ = v_snd_3705_;
v___y_3643_ = v_whitespace_3687_;
v___y_3644_ = v___y_3679_;
v___y_3645_ = v_fst_3704_;
v___y_3646_ = v_substring_3690_;
v___y_3647_ = v___y_3680_;
v___y_3648_ = v___x_3720_;
goto v___jp_3636_;
}
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec_ref(v_filterFn_3686_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3679_);
v_a_3723_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3691_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3691_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
lean_dec(v___y_3679_);
v_a_3731_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3684_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3684_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
v___jp_3739_:
{
if (lean_obj_tag(v___y_3741_) == 0)
{
lean_object* v___x_3746_; 
v___x_3746_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_3678_ = v___y_3740_;
v___y_3679_ = v___y_3742_;
v___y_3680_ = v___y_3743_;
v___y_3681_ = v___y_3745_;
v___y_3682_ = v___y_3744_;
v___y_3683_ = v___x_3746_;
goto v___jp_3677_;
}
else
{
lean_object* v_val_3747_; lean_object* v___x_3748_; 
v_val_3747_ = lean_ctor_get(v___y_3741_, 0);
lean_inc(v_val_3747_);
lean_dec_ref_known(v___y_3741_, 1);
v___x_3748_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3747_, v___y_3743_, v___y_3740_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3748_, 1);
v___y_3678_ = v___y_3740_;
v___y_3679_ = v___y_3742_;
v___y_3680_ = v___y_3743_;
v___y_3681_ = v___y_3745_;
v___y_3682_ = v___y_3744_;
v___y_3683_ = v_a_3749_;
goto v___jp_3677_;
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec(v___y_3742_);
v_a_3750_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3748_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
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
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
v___jp_3758_:
{
lean_object* v___x_3762_; lean_object* v_tk_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3762_ = lean_unsigned_to_nat(1u);
v_tk_3763_ = l_Lean_Syntax_getArg(v_x_3530_, v___x_3762_);
v___x_3764_ = lean_unsigned_to_nat(2u);
v___x_3765_ = l_Lean_Syntax_getArg(v_x_3530_, v___x_3764_);
v___x_3766_ = lean_unsigned_to_nat(4u);
v___x_3767_ = l_Lean_Syntax_getArg(v_x_3530_, v___x_3766_);
lean_dec(v_x_3530_);
v___x_3768_ = l_Lean_Syntax_getOptional_x3f(v___x_3765_);
lean_dec(v___x_3765_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v___x_3769_; 
v___x_3769_ = lean_box(0);
v___y_3740_ = v___y_3761_;
v___y_3741_ = v_dc_x3f_3759_;
v___y_3742_ = v_tk_3763_;
v___y_3743_ = v___y_3760_;
v___y_3744_ = v___x_3767_;
v___y_3745_ = v___x_3769_;
goto v___jp_3739_;
}
else
{
lean_object* v_val_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
v_val_3770_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3768_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_val_3770_);
lean_dec(v___x_3768_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_val_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
v___y_3740_ = v___y_3761_;
v___y_3741_ = v_dc_x3f_3759_;
v___y_3742_ = v_tk_3763_;
v___y_3743_ = v___y_3760_;
v___y_3744_ = v___x_3767_;
v___y_3745_ = v___x_3775_;
goto v___jp_3739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3793_, v_a_3794_, v_a_3795_);
lean_dec(v_a_3795_);
lean_dec_ref(v_a_3794_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3798_, lean_object* v_as_3799_, lean_object* v_as_x27_3800_, lean_object* v_b_3801_, lean_object* v_a_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3798_, v_as_x27_3800_, v_b_3801_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3807_, lean_object* v_as_3808_, lean_object* v_as_x27_3809_, lean_object* v_b_3810_, lean_object* v_a_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3807_, v_as_3808_, v_as_x27_3809_, v_b_3810_, v_a_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v_as_x27_3809_);
lean_dec(v_as_3808_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3816_, lean_object* v_x_3817_, lean_object* v_x_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3816_, v_x_3817_, v_x_3818_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3823_, lean_object* v_x_3824_, lean_object* v_x_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3823_, v_x_3824_, v_x_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3823_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3830_, v___y_3832_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3840_, lean_object* v___x_3841_, lean_object* v___x_3842_, lean_object* v_inst_3843_, lean_object* v_R_3844_, lean_object* v_a_3845_, lean_object* v_b_3846_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3840_, v___x_3841_, v___x_3842_, v_a_3845_, v_b_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3848_, lean_object* v___x_3849_, lean_object* v___x_3850_, lean_object* v_inst_3851_, lean_object* v_R_3852_, lean_object* v_a_3853_, lean_object* v_b_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3848_, v___x_3849_, v___x_3850_, v_inst_3851_, v_R_3852_, v_a_3853_, v_b_3854_);
lean_dec_ref(v___x_3849_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3856_, v___y_3858_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3866_, lean_object* v___x_3867_, lean_object* v___x_3868_, lean_object* v_inst_3869_, lean_object* v_R_3870_, lean_object* v_a_3871_, lean_object* v_b_3872_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3866_, v___x_3867_, v___x_3868_, v_a_3871_, v_b_3872_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3874_, lean_object* v___x_3875_, lean_object* v___x_3876_, lean_object* v_inst_3877_, lean_object* v_R_3878_, lean_object* v_a_3879_, lean_object* v_b_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3874_, v___x_3875_, v___x_3876_, v_inst_3877_, v_R_3878_, v_a_3879_, v_b_3880_);
lean_dec_ref(v___x_3875_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v_original_3882_, lean_object* v___x_3883_, lean_object* v_a_3884_, lean_object* v_inst_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_3882_, v___x_3883_, v_a_3884_, v_a_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v_original_3888_, lean_object* v___x_3889_, lean_object* v_a_3890_, lean_object* v_inst_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_original_3888_, v___x_3889_, v_a_3890_, v_inst_3891_, v_a_3892_);
lean_dec_ref(v_a_3890_);
lean_dec(v___x_3889_);
lean_dec_ref(v_original_3888_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_edited_3894_, lean_object* v___x_3895_, lean_object* v_a_3896_, lean_object* v_inst_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_3894_, v___x_3895_, v_a_3896_, v_a_3898_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object* v_edited_3900_, lean_object* v___x_3901_, lean_object* v_a_3902_, lean_object* v_inst_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_edited_3900_, v___x_3901_, v_a_3902_, v_inst_3903_, v_a_3904_);
lean_dec_ref(v_a_3902_);
lean_dec(v___x_3901_);
lean_dec_ref(v_edited_3900_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3906_, lean_object* v_original_3907_, lean_object* v_inst_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3906_, v_original_3907_, v_a_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3911_, lean_object* v_original_3912_, lean_object* v_inst_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3911_, v_original_3912_, v_inst_3913_, v_a_3914_);
lean_dec_ref(v_original_3912_);
lean_dec(v___x_3911_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3916_, lean_object* v_edited_3917_, lean_object* v_inst_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3916_, v_edited_3917_, v_a_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3921_, lean_object* v_edited_3922_, lean_object* v_inst_3923_, lean_object* v_a_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3921_, v_edited_3922_, v_inst_3923_, v_a_3924_);
lean_dec_ref(v_edited_3922_);
lean_dec(v___x_3921_);
return v_res_3925_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3926_, lean_object* v_inst_3927_, lean_object* v_R_3928_, lean_object* v_a_3929_, uint8_t v_b_3930_, lean_object* v_c_3931_){
_start:
{
uint8_t v___x_3932_; 
v___x_3932_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3926_, v_a_3929_, v_b_3930_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3933_, lean_object* v_inst_3934_, lean_object* v_R_3935_, lean_object* v_a_3936_, lean_object* v_b_3937_, lean_object* v_c_3938_){
_start:
{
uint8_t v_b_boxed_3939_; uint8_t v_res_3940_; lean_object* v_r_3941_; 
v_b_boxed_3939_ = lean_unbox(v_b_3937_);
v_res_3940_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3933_, v_inst_3934_, v_R_3935_, v_a_3936_, v_b_boxed_3939_, v_c_3938_);
lean_dec_ref(v_s_3933_);
v_r_3941_ = lean_box(v_res_3940_);
return v_r_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3942_, lean_object* v_ref_3943_, lean_object* v_msg_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3943_, v_msg_3944_, v___y_3945_, v___y_3946_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3949_, lean_object* v_ref_3950_, lean_object* v_msg_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3949_, v_ref_3950_, v_msg_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v_ref_3950_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(lean_object* v_as_3956_, lean_object* v_as_x27_3957_, lean_object* v_b_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3957_, v_b_3958_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___boxed(lean_object* v_as_3961_, lean_object* v_as_x27_3962_, lean_object* v_b_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(v_as_3961_, v_as_x27_3962_, v_b_3963_, v_a_3964_);
lean_dec(v_as_x27_3962_);
lean_dec(v_as_3961_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(lean_object* v_lsize_3966_, lean_object* v_rsize_3967_, lean_object* v_histogram_3968_, lean_object* v_index_3969_, lean_object* v_val_3970_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_histogram_3968_, v_index_3969_, v_val_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___boxed(lean_object* v_lsize_3972_, lean_object* v_rsize_3973_, lean_object* v_histogram_3974_, lean_object* v_index_3975_, lean_object* v_val_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(v_lsize_3972_, v_rsize_3973_, v_histogram_3974_, v_index_3975_, v_val_3976_);
lean_dec(v_rsize_3973_);
lean_dec(v_lsize_3972_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(lean_object* v_upperBound_3978_, lean_object* v___x_3979_, lean_object* v_fst_3980_, lean_object* v___x_3981_, lean_object* v_inst_3982_, lean_object* v_R_3983_, lean_object* v_a_3984_, lean_object* v_b_3985_, lean_object* v_c_3986_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3978_, v___x_3979_, v_fst_3980_, v___x_3981_, v_a_3984_, v_b_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___boxed(lean_object* v_upperBound_3988_, lean_object* v___x_3989_, lean_object* v_fst_3990_, lean_object* v___x_3991_, lean_object* v_inst_3992_, lean_object* v_R_3993_, lean_object* v_a_3994_, lean_object* v_b_3995_, lean_object* v_c_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(v_upperBound_3988_, v___x_3989_, v_fst_3990_, v___x_3991_, v_inst_3992_, v_R_3993_, v_a_3994_, v_b_3995_, v_c_3996_);
lean_dec(v___x_3991_);
lean_dec_ref(v_fst_3990_);
lean_dec(v___x_3989_);
lean_dec(v_upperBound_3988_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(lean_object* v_lsize_3998_, lean_object* v_rsize_3999_, lean_object* v_histogram_4000_, lean_object* v_index_4001_, lean_object* v_val_4002_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_histogram_4000_, v_index_4001_, v_val_4002_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___boxed(lean_object* v_lsize_4004_, lean_object* v_rsize_4005_, lean_object* v_histogram_4006_, lean_object* v_index_4007_, lean_object* v_val_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(v_lsize_4004_, v_rsize_4005_, v_histogram_4006_, v_index_4007_, v_val_4008_);
lean_dec(v_rsize_4005_);
lean_dec(v_lsize_4004_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(lean_object* v_upperBound_4010_, lean_object* v_fst_4011_, lean_object* v___x_4012_, lean_object* v_fst_4013_, lean_object* v_inst_4014_, lean_object* v_R_4015_, lean_object* v_a_4016_, lean_object* v_b_4017_, lean_object* v_c_4018_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_4010_, v_fst_4011_, v___x_4012_, v_fst_4013_, v_a_4016_, v_b_4017_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___boxed(lean_object* v_upperBound_4020_, lean_object* v_fst_4021_, lean_object* v___x_4022_, lean_object* v_fst_4023_, lean_object* v_inst_4024_, lean_object* v_R_4025_, lean_object* v_a_4026_, lean_object* v_b_4027_, lean_object* v_c_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(v_upperBound_4020_, v_fst_4021_, v___x_4022_, v_fst_4023_, v_inst_4024_, v_R_4025_, v_a_4026_, v_b_4027_, v_c_4028_);
lean_dec_ref(v_fst_4023_);
lean_dec(v___x_4022_);
lean_dec_ref(v_fst_4021_);
lean_dec(v_upperBound_4020_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_4030_, lean_object* v_msg_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v___x_4035_; 
v___x_4035_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_4031_, v___y_4032_, v___y_4033_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_4036_, lean_object* v_msg_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_4036_, v_msg_4037_, v___y_4038_, v___y_4039_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(lean_object* v_00_u03b2_4042_, lean_object* v_m_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_4043_, v_a_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b2_4046_, lean_object* v_m_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(v_00_u03b2_4046_, v_m_4047_, v_a_4048_);
lean_dec_ref(v_a_4048_);
lean_dec_ref(v_m_4047_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24(lean_object* v_00_u03b2_4050_, lean_object* v_m_4051_, lean_object* v_a_4052_, lean_object* v_b_4053_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_m_4051_, v_a_4052_, v_b_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_4055_, lean_object* v_macroStack_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_4055_, v_macroStack_4056_, v___y_4058_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4061_, lean_object* v_macroStack_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4061_, v_macroStack_4062_, v___y_4063_, v___y_4064_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29(lean_object* v_inst_4067_, lean_object* v_R_4068_, lean_object* v_a_4069_, lean_object* v_b_4070_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v_a_4069_, v_b_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(lean_object* v_00_u03b2_4072_, lean_object* v_a_4073_, lean_object* v_x_4074_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_4073_, v_x_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___boxed(lean_object* v_00_u03b2_4076_, lean_object* v_a_4077_, lean_object* v_x_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(v_00_u03b2_4076_, v_a_4077_, v_x_4078_);
lean_dec(v_x_4078_);
lean_dec_ref(v_a_4077_);
return v_res_4079_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(lean_object* v_00_u03b2_4080_, lean_object* v_a_4081_, lean_object* v_x_4082_){
_start:
{
uint8_t v___x_4083_; 
v___x_4083_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_4081_, v_x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___boxed(lean_object* v_00_u03b2_4084_, lean_object* v_a_4085_, lean_object* v_x_4086_){
_start:
{
uint8_t v_res_4087_; lean_object* v_r_4088_; 
v_res_4087_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(v_00_u03b2_4084_, v_a_4085_, v_x_4086_);
lean_dec(v_x_4086_);
lean_dec_ref(v_a_4085_);
v_r_4088_ = lean_box(v_res_4087_);
return v_r_4088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38(lean_object* v_00_u03b2_4089_, lean_object* v_data_4090_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_data_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39(lean_object* v_00_u03b2_4092_, lean_object* v_a_4093_, lean_object* v_b_4094_, lean_object* v_x_4095_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_4093_, v_b_4094_, v_x_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44(lean_object* v_00_u03b2_4097_, lean_object* v_i_4098_, lean_object* v_source_4099_, lean_object* v_target_4100_){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v_i_4098_, v_source_4099_, v_target_4100_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4102_, lean_object* v_x_4103_, lean_object* v_x_4104_){
_start:
{
lean_object* v___x_4105_; 
v___x_4105_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_x_4103_, v_x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4114_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4115_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
v___x_4116_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4117_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4118_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4114_, v___x_4115_, v___x_4116_, v___x_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4147_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4148_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4149_ = l_Lean_addBuiltinDeclarationRanges(v___x_4147_, v___x_4148_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4152_){
_start:
{
lean_object* v_doc_4154_; lean_object* v___x_4155_; 
v_doc_4154_ = lean_ctor_get(v___y_4152_, 1);
lean_inc_ref(v_doc_4154_);
v___x_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4155_, 0, v_doc_4154_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4156_);
lean_dec_ref(v___y_4156_);
return v_res_4158_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4159_, lean_object* v_a_4160_, uint8_t v_b_4161_){
_start:
{
lean_object* v_str_4162_; lean_object* v_startInclusive_4163_; lean_object* v_endExclusive_4164_; lean_object* v___x_4165_; uint8_t v___x_4166_; 
v_str_4162_ = lean_ctor_get(v_s_4159_, 0);
v_startInclusive_4163_ = lean_ctor_get(v_s_4159_, 1);
v_endExclusive_4164_ = lean_ctor_get(v_s_4159_, 2);
v___x_4165_ = lean_nat_sub(v_endExclusive_4164_, v_startInclusive_4163_);
v___x_4166_ = lean_nat_dec_eq(v_a_4160_, v___x_4165_);
lean_dec(v___x_4165_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4167_; uint32_t v___x_4168_; uint32_t v___x_4169_; uint8_t v___x_4170_; 
v___x_4167_ = lean_nat_add(v_startInclusive_4163_, v_a_4160_);
lean_dec(v_a_4160_);
v___x_4168_ = lean_string_utf8_get_fast(v_str_4162_, v___x_4167_);
v___x_4169_ = 10;
v___x_4170_ = lean_uint32_dec_eq(v___x_4168_, v___x_4169_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4171_ = lean_string_utf8_next_fast(v_str_4162_, v___x_4167_);
lean_dec(v___x_4167_);
v___x_4172_ = lean_nat_sub(v___x_4171_, v_startInclusive_4163_);
v_a_4160_ = v___x_4172_;
v_b_4161_ = v___x_4170_;
goto _start;
}
else
{
lean_dec(v___x_4167_);
return v___x_4170_;
}
}
else
{
lean_dec(v_a_4160_);
return v_b_4161_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4174_, lean_object* v_a_4175_, lean_object* v_b_4176_){
_start:
{
uint8_t v_b_boxed_4177_; uint8_t v_res_4178_; lean_object* v_r_4179_; 
v_b_boxed_4177_ = lean_unbox(v_b_4176_);
v_res_4178_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4174_, v_a_4175_, v_b_boxed_4177_);
lean_dec_ref(v_s_4174_);
v_r_4179_ = lean_box(v_res_4178_);
return v_r_4179_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4180_){
_start:
{
lean_object* v_searcher_4181_; uint8_t v___x_4182_; uint8_t v___x_4183_; 
v_searcher_4181_ = lean_unsigned_to_nat(0u);
v___x_4182_ = 0;
v___x_4183_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4180_, v_searcher_4181_, v___x_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4184_){
_start:
{
uint8_t v_res_4185_; lean_object* v_r_4186_; 
v_res_4185_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4184_);
lean_dec_ref(v_s_4184_);
v_r_4186_ = lean_box(v_res_4185_);
return v_r_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4198_, lean_object* v_fst_4199_, uint8_t v___x_4200_, lean_object* v_a_4201_, lean_object* v___x_4202_, lean_object* v___x_4203_, lean_object* v___x_4204_, lean_object* v___x_4205_, lean_object* v___x_4206_, lean_object* v___x_4207_, lean_object* v___x_4208_, lean_object* v___x_4209_, lean_object* v_snd_4210_, lean_object* v___x_4211_){
_start:
{
if (lean_obj_tag(v___x_4198_) == 1)
{
lean_object* v_val_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4276_; 
v_val_4213_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4215_ = v___x_4198_;
v_isShared_4216_ = v_isSharedCheck_4276_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_val_4213_);
lean_dec(v___x_4198_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4276_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4217_ = lean_unsigned_to_nat(0u);
v___x_4218_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4219_ = l_Lean_Syntax_setArg(v_fst_4199_, v___x_4217_, v___x_4218_);
v___x_4220_ = l_Lean_Syntax_getPos_x3f(v___x_4219_, v___x_4200_);
lean_dec(v___x_4219_);
if (lean_obj_tag(v___x_4220_) == 1)
{
lean_object* v_val_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4272_; 
lean_dec_ref(v___x_4211_);
v_val_4221_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4223_ = v___x_4220_;
v_isShared_4224_ = v_isSharedCheck_4272_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_val_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4272_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___y_4226_; lean_object* v___x_4252_; uint8_t v___y_4254_; lean_object* v___x_4263_; uint8_t v___x_4264_; 
v___x_4252_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4210_);
v___x_4263_ = lean_string_utf8_byte_size(v___x_4252_);
v___x_4264_ = lean_nat_dec_eq(v___x_4263_, v___x_4217_);
if (v___x_4264_ == 0)
{
lean_object* v___x_4265_; lean_object* v___x_4266_; uint8_t v___x_4267_; 
v___x_4265_ = lean_string_length(v___x_4252_);
v___x_4266_ = lean_unsigned_to_nat(93u);
v___x_4267_ = lean_nat_dec_le(v___x_4265_, v___x_4266_);
if (v___x_4267_ == 0)
{
v___y_4254_ = v___x_4267_;
goto v___jp_4253_;
}
else
{
lean_object* v___x_4268_; uint8_t v___x_4269_; uint8_t v___x_4270_; 
lean_inc_ref(v___x_4252_);
v___x_4268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4252_);
lean_ctor_set(v___x_4268_, 1, v___x_4217_);
lean_ctor_set(v___x_4268_, 2, v___x_4263_);
v___x_4269_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4268_);
lean_dec_ref_known(v___x_4268_, 3);
v___x_4270_ = lean_bool_not(v___x_4269_);
v___y_4254_ = v___x_4270_;
goto v___jp_4253_;
}
}
else
{
lean_object* v___x_4271_; 
lean_dec_ref(v___x_4252_);
v___x_4271_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_4226_ = v___x_4271_;
goto v___jp_4225_;
}
v___jp_4225_:
{
lean_object* v_toEditableDocumentCore_4227_; lean_object* v_meta_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4248_; 
v_toEditableDocumentCore_4227_ = lean_ctor_get(v_a_4201_, 0);
lean_inc_ref(v_toEditableDocumentCore_4227_);
v_meta_4228_ = lean_ctor_get(v_toEditableDocumentCore_4227_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v_toEditableDocumentCore_4227_);
if (v_isSharedCheck_4248_ == 0)
{
lean_object* v_unused_4249_; lean_object* v_unused_4250_; lean_object* v_unused_4251_; 
v_unused_4249_ = lean_ctor_get(v_toEditableDocumentCore_4227_, 3);
lean_dec(v_unused_4249_);
v_unused_4250_ = lean_ctor_get(v_toEditableDocumentCore_4227_, 2);
lean_dec(v_unused_4250_);
v_unused_4251_ = lean_ctor_get(v_toEditableDocumentCore_4227_, 1);
lean_dec(v_unused_4251_);
v___x_4230_ = v_toEditableDocumentCore_4227_;
v_isShared_4231_ = v_isSharedCheck_4248_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_meta_4228_);
lean_dec(v_toEditableDocumentCore_4227_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4248_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v_text_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4238_; 
v_text_4232_ = lean_ctor_get(v_meta_4228_, 3);
lean_inc_ref(v_text_4232_);
lean_dec_ref(v_meta_4228_);
v___x_4233_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4201_);
v___x_4234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4234_, 0, v_val_4213_);
lean_ctor_set(v___x_4234_, 1, v_val_4221_);
v___x_4235_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4232_, v___x_4234_);
v___x_4236_ = lean_box(0);
lean_inc(v___x_4202_);
if (v_isShared_4231_ == 0)
{
lean_ctor_set(v___x_4230_, 3, v___x_4202_);
lean_ctor_set(v___x_4230_, 2, v___x_4236_);
lean_ctor_set(v___x_4230_, 1, v___y_4226_);
lean_ctor_set(v___x_4230_, 0, v___x_4235_);
v___x_4238_ = v___x_4230_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4247_, 1, v___y_4226_);
lean_ctor_set(v_reuseFailAlloc_4247_, 2, v___x_4236_);
lean_ctor_set(v_reuseFailAlloc_4247_, 3, v___x_4202_);
v___x_4238_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
lean_object* v___x_4239_; lean_object* v___x_4241_; 
v___x_4239_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4233_, v___x_4238_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v___x_4239_);
v___x_4241_ = v___x_4223_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4239_);
v___x_4241_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
lean_object* v___x_4242_; lean_object* v___x_4244_; 
lean_inc(v___x_4202_);
v___x_4242_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4202_);
lean_ctor_set(v___x_4242_, 1, v___x_4202_);
lean_ctor_set(v___x_4242_, 2, v___x_4203_);
lean_ctor_set(v___x_4242_, 3, v___x_4204_);
lean_ctor_set(v___x_4242_, 4, v___x_4205_);
lean_ctor_set(v___x_4242_, 5, v___x_4206_);
lean_ctor_set(v___x_4242_, 6, v___x_4207_);
lean_ctor_set(v___x_4242_, 7, v___x_4241_);
lean_ctor_set(v___x_4242_, 8, v___x_4208_);
lean_ctor_set(v___x_4242_, 9, v___x_4209_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set_tag(v___x_4215_, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4242_);
v___x_4244_ = v___x_4215_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4242_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
}
v___jp_4253_:
{
if (v___y_4254_ == 0)
{
lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4255_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4256_ = lean_string_append(v___x_4255_, v___x_4252_);
lean_dec_ref(v___x_4252_);
v___x_4257_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4258_ = lean_string_append(v___x_4256_, v___x_4257_);
v___y_4226_ = v___x_4258_;
goto v___jp_4225_;
}
else
{
lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4259_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4260_ = lean_string_append(v___x_4259_, v___x_4252_);
lean_dec_ref(v___x_4252_);
v___x_4261_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4262_ = lean_string_append(v___x_4260_, v___x_4261_);
v___y_4226_ = v___x_4262_;
goto v___jp_4225_;
}
}
}
}
else
{
lean_object* v___x_4274_; 
lean_dec(v___x_4220_);
lean_dec(v_val_4213_);
lean_dec_ref(v_snd_4210_);
lean_dec(v___x_4209_);
lean_dec(v___x_4208_);
lean_dec(v___x_4207_);
lean_dec(v___x_4206_);
lean_dec(v___x_4205_);
lean_dec(v___x_4204_);
lean_dec_ref(v___x_4203_);
lean_dec(v___x_4202_);
lean_dec_ref(v_a_4201_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set_tag(v___x_4215_, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4211_);
v___x_4274_ = v___x_4215_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4211_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
else
{
lean_object* v___x_4277_; 
lean_dec_ref(v_snd_4210_);
lean_dec(v___x_4209_);
lean_dec(v___x_4208_);
lean_dec(v___x_4207_);
lean_dec(v___x_4206_);
lean_dec(v___x_4205_);
lean_dec(v___x_4204_);
lean_dec_ref(v___x_4203_);
lean_dec(v___x_4202_);
lean_dec_ref(v_a_4201_);
lean_dec(v_fst_4199_);
lean_dec(v___x_4198_);
v___x_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4211_);
return v___x_4277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4278_, lean_object* v_fst_4279_, lean_object* v___x_4280_, lean_object* v_a_4281_, lean_object* v___x_4282_, lean_object* v___x_4283_, lean_object* v___x_4284_, lean_object* v___x_4285_, lean_object* v___x_4286_, lean_object* v___x_4287_, lean_object* v___x_4288_, lean_object* v___x_4289_, lean_object* v_snd_4290_, lean_object* v___x_4291_, lean_object* v___y_4292_){
_start:
{
uint8_t v___x_4528__boxed_4293_; lean_object* v_res_4294_; 
v___x_4528__boxed_4293_ = lean_unbox(v___x_4280_);
v_res_4294_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4278_, v_fst_4279_, v___x_4528__boxed_4293_, v_a_4281_, v___x_4282_, v___x_4283_, v___x_4284_, v___x_4285_, v___x_4286_, v___x_4287_, v___x_4288_, v___x_4289_, v_snd_4290_, v___x_4291_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4298_, size_t v_sz_4299_, size_t v_i_4300_, lean_object* v_b_4301_){
_start:
{
lean_object* v_a_4303_; uint8_t v___x_4307_; 
v___x_4307_ = lean_usize_dec_lt(v_i_4300_, v_sz_4299_);
if (v___x_4307_ == 0)
{
lean_inc_ref(v_b_4301_);
return v_b_4301_;
}
else
{
lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v_a_4310_; 
v___x_4308_ = lean_box(0);
v___x_4309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4310_ = lean_array_uget(v_as_4298_, v_i_4300_);
if (lean_obj_tag(v_a_4310_) == 1)
{
lean_object* v_i_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4345_; 
v_i_4311_ = lean_ctor_get(v_a_4310_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v_a_4310_);
if (v_isSharedCheck_4345_ == 0)
{
lean_object* v_unused_4346_; 
v_unused_4346_ = lean_ctor_get(v_a_4310_, 1);
lean_dec(v_unused_4346_);
v___x_4313_ = v_a_4310_;
v_isShared_4314_ = v_isSharedCheck_4345_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_i_4311_);
lean_dec(v_a_4310_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4345_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
if (lean_obj_tag(v_i_4311_) == 10)
{
lean_object* v_i_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4344_; 
v_i_4315_ = lean_ctor_get(v_i_4311_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v_i_4311_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4317_ = v_i_4311_;
v_isShared_4318_ = v_isSharedCheck_4344_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_i_4315_);
lean_dec(v_i_4311_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4344_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v_stx_4319_; lean_object* v_value_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4343_; 
v_stx_4319_ = lean_ctor_get(v_i_4315_, 0);
v_value_4320_ = lean_ctor_get(v_i_4315_, 1);
v_isSharedCheck_4343_ = !lean_is_exclusive(v_i_4315_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4322_ = v_i_4315_;
v_isShared_4323_ = v_isSharedCheck_4343_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_value_4320_);
lean_inc(v_stx_4319_);
lean_dec(v_i_4315_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4343_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4325_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4320_, v___x_4324_);
lean_dec(v_value_4320_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_del_object(v___x_4322_);
lean_dec(v_stx_4319_);
lean_del_object(v___x_4317_);
lean_del_object(v___x_4313_);
v_a_4303_ = v___x_4309_;
goto v___jp_4302_;
}
else
{
lean_object* v_val_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4342_; 
v_val_4326_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4328_ = v___x_4325_;
v_isShared_4329_ = v_isSharedCheck_4342_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_val_4326_);
lean_dec(v___x_4325_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4342_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4323_ == 0)
{
lean_ctor_set(v___x_4322_, 1, v_val_4326_);
v___x_4331_ = v___x_4322_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_stx_4319_);
lean_ctor_set(v_reuseFailAlloc_4341_, 1, v_val_4326_);
v___x_4331_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
lean_object* v___x_4333_; 
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v___x_4331_);
v___x_4333_ = v___x_4328_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4331_);
v___x_4333_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
lean_object* v___x_4335_; 
if (v_isShared_4318_ == 0)
{
lean_ctor_set_tag(v___x_4317_, 1);
lean_ctor_set(v___x_4317_, 0, v___x_4333_);
v___x_4335_ = v___x_4317_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4333_);
v___x_4335_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4337_; 
if (v_isShared_4314_ == 0)
{
lean_ctor_set_tag(v___x_4313_, 0);
lean_ctor_set(v___x_4313_, 1, v___x_4308_);
lean_ctor_set(v___x_4313_, 0, v___x_4335_);
v___x_4337_ = v___x_4313_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4335_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v___x_4308_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
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
lean_del_object(v___x_4313_);
lean_dec_ref(v_i_4311_);
v_a_4303_ = v___x_4309_;
goto v___jp_4302_;
}
}
}
else
{
lean_dec(v_a_4310_);
v_a_4303_ = v___x_4309_;
goto v___jp_4302_;
}
}
v___jp_4302_:
{
size_t v___x_4304_; size_t v___x_4305_; 
v___x_4304_ = ((size_t)1ULL);
v___x_4305_ = lean_usize_add(v_i_4300_, v___x_4304_);
v_i_4300_ = v___x_4305_;
v_b_4301_ = v_a_4303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4347_, lean_object* v_sz_4348_, lean_object* v_i_4349_, lean_object* v_b_4350_){
_start:
{
size_t v_sz_boxed_4351_; size_t v_i_boxed_4352_; lean_object* v_res_4353_; 
v_sz_boxed_4351_ = lean_unbox_usize(v_sz_4348_);
lean_dec(v_sz_4348_);
v_i_boxed_4352_ = lean_unbox_usize(v_i_4349_);
lean_dec(v_i_4349_);
v_res_4353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4347_, v_sz_boxed_4351_, v_i_boxed_4352_, v_b_4350_);
lean_dec_ref(v_b_4350_);
lean_dec_ref(v_as_4347_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4354_, size_t v_sz_4355_, size_t v_i_4356_, lean_object* v_b_4357_){
_start:
{
lean_object* v_a_4359_; uint8_t v___x_4363_; 
v___x_4363_ = lean_usize_dec_lt(v_i_4356_, v_sz_4355_);
if (v___x_4363_ == 0)
{
lean_inc_ref(v_b_4357_);
return v_b_4357_;
}
else
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v_a_4366_; 
v___x_4364_ = lean_box(0);
v___x_4365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4366_ = lean_array_uget(v_as_4354_, v_i_4356_);
if (lean_obj_tag(v_a_4366_) == 1)
{
lean_object* v_i_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4401_; 
v_i_4367_ = lean_ctor_get(v_a_4366_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v_a_4366_);
if (v_isSharedCheck_4401_ == 0)
{
lean_object* v_unused_4402_; 
v_unused_4402_ = lean_ctor_get(v_a_4366_, 1);
lean_dec(v_unused_4402_);
v___x_4369_ = v_a_4366_;
v_isShared_4370_ = v_isSharedCheck_4401_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_i_4367_);
lean_dec(v_a_4366_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4401_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
if (lean_obj_tag(v_i_4367_) == 10)
{
lean_object* v_i_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4400_; 
v_i_4371_ = lean_ctor_get(v_i_4367_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v_i_4367_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4373_ = v_i_4367_;
v_isShared_4374_ = v_isSharedCheck_4400_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_i_4371_);
lean_dec(v_i_4367_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4400_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v_stx_4375_; lean_object* v_value_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4399_; 
v_stx_4375_ = lean_ctor_get(v_i_4371_, 0);
v_value_4376_ = lean_ctor_get(v_i_4371_, 1);
v_isSharedCheck_4399_ = !lean_is_exclusive(v_i_4371_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4378_ = v_i_4371_;
v_isShared_4379_ = v_isSharedCheck_4399_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_value_4376_);
lean_inc(v_stx_4375_);
lean_dec(v_i_4371_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4399_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4380_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4381_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4376_, v___x_4380_);
lean_dec(v_value_4376_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_del_object(v___x_4378_);
lean_dec(v_stx_4375_);
lean_del_object(v___x_4373_);
lean_del_object(v___x_4369_);
v_a_4359_ = v___x_4365_;
goto v___jp_4358_;
}
else
{
lean_object* v_val_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4398_; 
v_val_4382_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4384_ = v___x_4381_;
v_isShared_4385_ = v_isSharedCheck_4398_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_val_4382_);
lean_dec(v___x_4381_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4398_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 1, v_val_4382_);
v___x_4387_ = v___x_4378_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_stx_4375_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v_val_4382_);
v___x_4387_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
lean_object* v___x_4389_; 
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 0, v___x_4387_);
v___x_4389_ = v___x_4384_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4387_);
v___x_4389_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
lean_object* v___x_4391_; 
if (v_isShared_4374_ == 0)
{
lean_ctor_set_tag(v___x_4373_, 1);
lean_ctor_set(v___x_4373_, 0, v___x_4389_);
v___x_4391_ = v___x_4373_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v___x_4389_);
v___x_4391_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
lean_object* v___x_4393_; 
if (v_isShared_4370_ == 0)
{
lean_ctor_set_tag(v___x_4369_, 0);
lean_ctor_set(v___x_4369_, 1, v___x_4364_);
lean_ctor_set(v___x_4369_, 0, v___x_4391_);
v___x_4393_ = v___x_4369_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4391_);
lean_ctor_set(v_reuseFailAlloc_4394_, 1, v___x_4364_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
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
lean_del_object(v___x_4369_);
lean_dec_ref(v_i_4367_);
v_a_4359_ = v___x_4365_;
goto v___jp_4358_;
}
}
}
else
{
lean_dec(v_a_4366_);
v_a_4359_ = v___x_4365_;
goto v___jp_4358_;
}
}
v___jp_4358_:
{
size_t v___x_4360_; size_t v___x_4361_; lean_object* v___x_4362_; 
v___x_4360_ = ((size_t)1ULL);
v___x_4361_ = lean_usize_add(v_i_4356_, v___x_4360_);
v___x_4362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4354_, v_sz_4355_, v___x_4361_, v_a_4359_);
return v___x_4362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4403_, lean_object* v_sz_4404_, lean_object* v_i_4405_, lean_object* v_b_4406_){
_start:
{
size_t v_sz_boxed_4407_; size_t v_i_boxed_4408_; lean_object* v_res_4409_; 
v_sz_boxed_4407_ = lean_unbox_usize(v_sz_4404_);
lean_dec(v_sz_4404_);
v_i_boxed_4408_ = lean_unbox_usize(v_i_4405_);
lean_dec(v_i_4405_);
v_res_4409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4403_, v_sz_boxed_4407_, v_i_boxed_4408_, v_b_4406_);
lean_dec_ref(v_b_4406_);
lean_dec_ref(v_as_4403_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4410_){
_start:
{
if (lean_obj_tag(v_x_4410_) == 0)
{
lean_object* v_cs_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; size_t v_sz_4414_; size_t v___x_4415_; lean_object* v___x_4416_; lean_object* v_fst_4417_; 
v_cs_4411_ = lean_ctor_get(v_x_4410_, 0);
v___x_4412_ = lean_box(0);
v___x_4413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4414_ = lean_array_size(v_cs_4411_);
v___x_4415_ = ((size_t)0ULL);
v___x_4416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4411_, v_sz_4414_, v___x_4415_, v___x_4413_);
v_fst_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_fst_4417_);
lean_dec_ref(v___x_4416_);
if (lean_obj_tag(v_fst_4417_) == 0)
{
return v___x_4412_;
}
else
{
lean_object* v_val_4418_; 
v_val_4418_ = lean_ctor_get(v_fst_4417_, 0);
lean_inc(v_val_4418_);
lean_dec_ref_known(v_fst_4417_, 1);
return v_val_4418_;
}
}
else
{
lean_object* v_vs_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; size_t v_sz_4422_; size_t v___x_4423_; lean_object* v___x_4424_; lean_object* v_fst_4425_; 
v_vs_4419_ = lean_ctor_get(v_x_4410_, 0);
v___x_4420_ = lean_box(0);
v___x_4421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4422_ = lean_array_size(v_vs_4419_);
v___x_4423_ = ((size_t)0ULL);
v___x_4424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4419_, v_sz_4422_, v___x_4423_, v___x_4421_);
v_fst_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_fst_4425_);
lean_dec_ref(v___x_4424_);
if (lean_obj_tag(v_fst_4425_) == 0)
{
return v___x_4420_;
}
else
{
lean_object* v_val_4426_; 
v_val_4426_ = lean_ctor_get(v_fst_4425_, 0);
lean_inc(v_val_4426_);
lean_dec_ref_known(v_fst_4425_, 1);
return v_val_4426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4427_, size_t v_sz_4428_, size_t v_i_4429_, lean_object* v_b_4430_){
_start:
{
uint8_t v___x_4431_; 
v___x_4431_ = lean_usize_dec_lt(v_i_4429_, v_sz_4428_);
if (v___x_4431_ == 0)
{
lean_inc_ref(v_b_4430_);
return v_b_4430_;
}
else
{
lean_object* v___x_4432_; lean_object* v_a_4433_; lean_object* v___x_4434_; 
v___x_4432_ = lean_box(0);
v_a_4433_ = lean_array_uget_borrowed(v_as_4427_, v_i_4429_);
v___x_4434_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4433_);
if (lean_obj_tag(v___x_4434_) == 1)
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
v___x_4436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
lean_ctor_set(v___x_4436_, 1, v___x_4432_);
return v___x_4436_;
}
else
{
lean_object* v___x_4437_; size_t v___x_4438_; size_t v___x_4439_; 
lean_dec(v___x_4434_);
v___x_4437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4438_ = ((size_t)1ULL);
v___x_4439_ = lean_usize_add(v_i_4429_, v___x_4438_);
v_i_4429_ = v___x_4439_;
v_b_4430_ = v___x_4437_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4441_, lean_object* v_sz_4442_, lean_object* v_i_4443_, lean_object* v_b_4444_){
_start:
{
size_t v_sz_boxed_4445_; size_t v_i_boxed_4446_; lean_object* v_res_4447_; 
v_sz_boxed_4445_ = lean_unbox_usize(v_sz_4442_);
lean_dec(v_sz_4442_);
v_i_boxed_4446_ = lean_unbox_usize(v_i_4443_);
lean_dec(v_i_4443_);
v_res_4447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4441_, v_sz_boxed_4445_, v_i_boxed_4446_, v_b_4444_);
lean_dec_ref(v_b_4444_);
lean_dec_ref(v_as_4441_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4448_);
lean_dec_ref(v_x_4448_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4450_){
_start:
{
lean_object* v_root_4451_; lean_object* v_tail_4452_; lean_object* v___x_4453_; 
v_root_4451_ = lean_ctor_get(v_t_4450_, 0);
v_tail_4452_ = lean_ctor_get(v_t_4450_, 1);
v___x_4453_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4451_);
if (lean_obj_tag(v___x_4453_) == 0)
{
lean_object* v___x_4454_; size_t v_sz_4455_; size_t v___x_4456_; lean_object* v___x_4457_; lean_object* v_fst_4458_; 
v___x_4454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4455_ = lean_array_size(v_tail_4452_);
v___x_4456_ = ((size_t)0ULL);
v___x_4457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4452_, v_sz_4455_, v___x_4456_, v___x_4454_);
v_fst_4458_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_fst_4458_);
lean_dec_ref(v___x_4457_);
if (lean_obj_tag(v_fst_4458_) == 0)
{
return v___x_4453_;
}
else
{
lean_object* v_val_4459_; 
v_val_4459_ = lean_ctor_get(v_fst_4458_, 0);
lean_inc(v_val_4459_);
lean_dec_ref_known(v_fst_4458_, 1);
return v_val_4459_;
}
}
else
{
return v___x_4453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4460_);
lean_dec_ref(v_t_4460_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4476_, lean_object* v_a_4477_){
_start:
{
if (lean_obj_tag(v_node_4476_) == 1)
{
lean_object* v_children_4479_; lean_object* v_res_4480_; 
v_children_4479_ = lean_ctor_get(v_node_4476_, 1);
v_res_4480_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4479_);
if (lean_obj_tag(v_res_4480_) == 1)
{
lean_object* v_val_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4518_; 
v_val_4481_ = lean_ctor_get(v_res_4480_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v_res_4480_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4483_ = v_res_4480_;
v_isShared_4484_ = v_isSharedCheck_4518_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_val_4481_);
lean_dec(v_res_4480_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4518_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v_fst_4485_; lean_object* v_snd_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4517_; 
v_fst_4485_ = lean_ctor_get(v_val_4481_, 0);
v_snd_4486_ = lean_ctor_get(v_val_4481_, 1);
v_isSharedCheck_4517_ = !lean_is_exclusive(v_val_4481_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4488_ = v_val_4481_;
v_isShared_4489_ = v_isSharedCheck_4517_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_snd_4486_);
lean_inc(v_fst_4485_);
lean_dec(v_val_4481_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4517_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4490_; lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4516_; 
v___x_4490_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4477_);
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4493_ = v___x_4490_;
v_isShared_4494_ = v_isSharedCheck_4516_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4490_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4516_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; uint8_t v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___y_4503_; lean_object* v___x_4505_; 
v___x_4495_ = lean_box(0);
v___x_4496_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4497_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4498_ = 1;
v___x_4499_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4500_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4501_ = l_Lean_Syntax_getPos_x3f(v_fst_4485_, v___x_4498_);
v___x_4502_ = lean_box(v___x_4498_);
v___y_4503_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4503_, 0, v___x_4501_);
lean_closure_set(v___y_4503_, 1, v_fst_4485_);
lean_closure_set(v___y_4503_, 2, v___x_4502_);
lean_closure_set(v___y_4503_, 3, v_a_4491_);
lean_closure_set(v___y_4503_, 4, v___x_4495_);
lean_closure_set(v___y_4503_, 5, v___x_4496_);
lean_closure_set(v___y_4503_, 6, v___x_4497_);
lean_closure_set(v___y_4503_, 7, v___x_4495_);
lean_closure_set(v___y_4503_, 8, v___x_4499_);
lean_closure_set(v___y_4503_, 9, v___x_4495_);
lean_closure_set(v___y_4503_, 10, v___x_4495_);
lean_closure_set(v___y_4503_, 11, v___x_4495_);
lean_closure_set(v___y_4503_, 12, v_snd_4486_);
lean_closure_set(v___y_4503_, 13, v___x_4500_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v___y_4503_);
v___x_4505_ = v___x_4483_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___y_4503_);
v___x_4505_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4507_; 
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 1, v___x_4505_);
lean_ctor_set(v___x_4488_, 0, v___x_4500_);
v___x_4507_ = v___x_4488_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4500_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v___x_4505_);
v___x_4507_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4512_; 
v___x_4508_ = lean_unsigned_to_nat(1u);
v___x_4509_ = lean_mk_empty_array_with_capacity(v___x_4508_);
v___x_4510_ = lean_array_push(v___x_4509_, v___x_4507_);
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 0, v___x_4510_);
v___x_4512_ = v___x_4493_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
lean_dec(v_res_4480_);
v___x_4519_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4519_);
return v___x_4520_;
}
}
else
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4521_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
return v___x_4522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4523_, v_a_4524_);
lean_dec_ref(v_a_4524_);
lean_dec_ref(v_node_4523_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4527_, lean_object* v_x_4528_, lean_object* v_x_4529_, lean_object* v_node_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v___x_4533_; 
v___x_4533_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4530_, v_a_4531_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4534_, lean_object* v_x_4535_, lean_object* v_x_4536_, lean_object* v_node_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4534_, v_x_4535_, v_x_4536_, v_node_4537_, v_a_4538_);
lean_dec_ref(v_a_4538_);
lean_dec_ref(v_node_4537_);
lean_dec_ref(v_x_4536_);
lean_dec_ref(v_x_4535_);
lean_dec_ref(v_x_4534_);
return v_res_4540_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4541_, lean_object* v_inst_4542_, lean_object* v_R_4543_, lean_object* v_a_4544_, uint8_t v_b_4545_, lean_object* v_c_4546_){
_start:
{
uint8_t v___x_4547_; 
v___x_4547_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4541_, v_a_4544_, v_b_4545_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4548_, lean_object* v_inst_4549_, lean_object* v_R_4550_, lean_object* v_a_4551_, lean_object* v_b_4552_, lean_object* v_c_4553_){
_start:
{
uint8_t v_b_boxed_4554_; uint8_t v_res_4555_; lean_object* v_r_4556_; 
v_b_boxed_4554_ = lean_unbox(v_b_4552_);
v_res_4555_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4548_, v_inst_4549_, v_R_4550_, v_a_4551_, v_b_boxed_4554_, v_c_4553_);
lean_dec_ref(v_s_4548_);
v_r_4556_ = lean_box(v_res_4555_);
return v_r_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_(){
_start:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4562_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_));
v___x_4563_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4564_ = l_Lean_CodeAction_insertBuiltin(v___x_4562_, v___x_4563_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365____boxed(lean_object* v_a_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_();
return v_res_4566_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4569_ = lean_string_utf8_byte_size(v___x_4568_);
return v___x_4569_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; uint8_t v___x_4572_; 
v___x_4570_ = lean_unsigned_to_nat(0u);
v___x_4571_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4572_ = lean_nat_dec_eq(v___x_4571_, v___x_4570_);
return v___x_4572_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4573_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4575_);
lean_ctor_set(v___x_4576_, 1, v___x_4574_);
lean_ctor_set(v___x_4576_, 2, v___x_4573_);
return v___x_4576_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4(void){
_start:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4577_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4578_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4577_);
return v___x_4578_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4579_ = lean_unsigned_to_nat(0u);
v___x_4580_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4);
v___x_4581_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4582_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
lean_ctor_set(v___x_4582_, 1, v___x_4580_);
lean_ctor_set(v___x_4582_, 2, v___x_4579_);
lean_ctor_set(v___x_4582_, 3, v___x_4579_);
return v___x_4582_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4583_){
_start:
{
lean_object* v___y_4585_; uint8_t v___x_4588_; 
v___x_4588_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
if (v___x_4588_ == 0)
{
lean_object* v___x_4589_; 
v___x_4589_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5);
v___y_4585_ = v___x_4589_;
goto v___jp_4584_;
}
else
{
lean_object* v___x_4590_; 
v___x_4590_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_4585_ = v___x_4590_;
goto v___jp_4584_;
}
v___jp_4584_:
{
uint8_t v___x_4586_; uint8_t v___x_4587_; 
v___x_4586_ = 0;
lean_inc(v___y_4585_);
v___x_4587_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4583_, v___y_4585_, v___x_4586_);
return v___x_4587_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4591_){
_start:
{
uint8_t v_res_4592_; lean_object* v_r_4593_; 
v_res_4592_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4591_);
lean_dec_ref(v_s_4591_);
v_r_4593_ = lean_box(v_res_4592_);
return v_r_4593_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4594_, lean_object* v_as_x27_4595_, uint8_t v_b_4596_){
_start:
{
if (lean_obj_tag(v_as_x27_4595_) == 0)
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = lean_box(v_b_4596_);
v___x_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
return v___x_4599_;
}
else
{
lean_object* v_head_4600_; uint8_t v_isSilent_4601_; 
v_head_4600_ = lean_ctor_get(v_as_x27_4595_, 0);
v_isSilent_4601_ = lean_ctor_get_uint8(v_head_4600_, sizeof(void*)*5 + 2);
if (v_isSilent_4601_ == 0)
{
lean_object* v_tail_4602_; lean_object* v_data_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; uint8_t v___x_4608_; 
v_tail_4602_ = lean_ctor_get(v_as_x27_4595_, 1);
v_data_4603_ = lean_ctor_get(v_head_4600_, 4);
lean_inc(v_data_4603_);
v___x_4604_ = l_Lean_MessageData_toString(v_data_4603_);
v___x_4605_ = lean_unsigned_to_nat(0u);
v___x_4606_ = lean_string_utf8_byte_size(v___x_4604_);
v___x_4607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4604_);
lean_ctor_set(v___x_4607_, 1, v___x_4605_);
lean_ctor_set(v___x_4607_, 2, v___x_4606_);
v___x_4608_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4607_);
lean_dec_ref_known(v___x_4607_, 3);
if (v___x_4608_ == 0)
{
v_as_x27_4595_ = v_tail_4602_;
goto _start;
}
else
{
lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4610_ = lean_box(v_foundPanic_4594_);
v___x_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4610_);
return v___x_4611_;
}
}
else
{
lean_object* v_tail_4612_; 
v_tail_4612_ = lean_ctor_get(v_as_x27_4595_, 1);
v_as_x27_4595_ = v_tail_4612_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4614_, lean_object* v_as_x27_4615_, lean_object* v_b_4616_, lean_object* v___y_4617_){
_start:
{
uint8_t v_foundPanic_boxed_4618_; uint8_t v_b_boxed_4619_; lean_object* v_res_4620_; 
v_foundPanic_boxed_4618_ = lean_unbox(v_foundPanic_4614_);
v_b_boxed_4619_ = lean_unbox(v_b_4616_);
v_res_4620_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4618_, v_as_x27_4615_, v_b_boxed_4619_);
lean_dec(v_as_x27_4615_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4621_, uint8_t v_severity_4622_, uint8_t v_isSilent_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
lean_object* v___x_4627_; 
v___x_4627_ = l_Lean_Elab_Command_getRef___redArg(v___y_4624_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v_a_4628_; lean_object* v___x_4629_; 
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
lean_inc(v_a_4628_);
lean_dec_ref_known(v___x_4627_, 1);
v___x_4629_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4628_, v_msgData_4621_, v_severity_4622_, v_isSilent_4623_, v___y_4624_, v___y_4625_);
lean_dec(v_a_4628_);
return v___x_4629_;
}
else
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4637_; 
lean_dec_ref(v_msgData_4621_);
v_a_4630_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4632_ = v___x_4627_;
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4627_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
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
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4638_, lean_object* v_severity_4639_, lean_object* v_isSilent_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
uint8_t v_severity_boxed_4644_; uint8_t v_isSilent_boxed_4645_; lean_object* v_res_4646_; 
v_severity_boxed_4644_ = lean_unbox(v_severity_4639_);
v_isSilent_boxed_4645_ = lean_unbox(v_isSilent_4640_);
v_res_4646_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4638_, v_severity_boxed_4644_, v_isSilent_boxed_4645_, v___y_4641_, v___y_4642_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
uint8_t v___x_4651_; uint8_t v___x_4652_; lean_object* v___x_4653_; 
v___x_4651_ = 2;
v___x_4652_ = 0;
v___x_4653_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4647_, v___x_4651_, v___x_4652_, v___y_4648_, v___y_4649_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4654_, v___y_4655_, v___y_4656_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
return v_res_4658_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4666_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4667_ = l_Lean_MessageData_ofFormat(v___x_4666_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_){
_start:
{
lean_object* v___x_4672_; uint8_t v_foundPanic_4673_; 
v___x_4672_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4668_);
v_foundPanic_4673_ = l_Lean_Syntax_isOfKind(v_x_4668_, v___x_4672_);
if (v_foundPanic_4673_ == 0)
{
lean_object* v___x_4674_; 
lean_dec(v_x_4668_);
v___x_4674_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4674_;
}
else
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4675_ = lean_unsigned_to_nat(2u);
v___x_4676_ = l_Lean_Syntax_getArg(v_x_4668_, v___x_4675_);
lean_dec(v_x_4668_);
v___x_4677_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4676_, v_a_4669_, v_a_4670_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; uint8_t v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4734_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref_known(v___x_4677_, 1);
v___x_4679_ = 0;
v___x_4680_ = l_Lean_MessageLog_toList(v_a_4678_);
v___x_4681_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4673_, v___x_4680_, v___x_4679_);
lean_dec(v___x_4680_);
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4684_ = v___x_4681_;
v_isShared_4685_ = v_isSharedCheck_4734_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4681_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4734_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
uint8_t v___x_4686_; 
v___x_4686_ = lean_unbox(v_a_4682_);
lean_dec(v_a_4682_);
if (v___x_4686_ == 0)
{
lean_object* v___x_4687_; lean_object* v_env_4688_; lean_object* v_scopes_4689_; lean_object* v_usedQuotCtxts_4690_; lean_object* v_nextMacroScope_4691_; lean_object* v_maxRecDepth_4692_; lean_object* v_ngen_4693_; lean_object* v_auxDeclNGen_4694_; lean_object* v_infoState_4695_; lean_object* v_traceState_4696_; lean_object* v_snapshotTasks_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4707_; 
lean_del_object(v___x_4684_);
v___x_4687_ = lean_st_ref_take(v_a_4670_);
v_env_4688_ = lean_ctor_get(v___x_4687_, 0);
v_scopes_4689_ = lean_ctor_get(v___x_4687_, 2);
v_usedQuotCtxts_4690_ = lean_ctor_get(v___x_4687_, 3);
v_nextMacroScope_4691_ = lean_ctor_get(v___x_4687_, 4);
v_maxRecDepth_4692_ = lean_ctor_get(v___x_4687_, 5);
v_ngen_4693_ = lean_ctor_get(v___x_4687_, 6);
v_auxDeclNGen_4694_ = lean_ctor_get(v___x_4687_, 7);
v_infoState_4695_ = lean_ctor_get(v___x_4687_, 8);
v_traceState_4696_ = lean_ctor_get(v___x_4687_, 9);
v_snapshotTasks_4697_ = lean_ctor_get(v___x_4687_, 10);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4707_ == 0)
{
lean_object* v_unused_4708_; 
v_unused_4708_ = lean_ctor_get(v___x_4687_, 1);
lean_dec(v_unused_4708_);
v___x_4699_ = v___x_4687_;
v_isShared_4700_ = v_isSharedCheck_4707_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_snapshotTasks_4697_);
lean_inc(v_traceState_4696_);
lean_inc(v_infoState_4695_);
lean_inc(v_auxDeclNGen_4694_);
lean_inc(v_ngen_4693_);
lean_inc(v_maxRecDepth_4692_);
lean_inc(v_nextMacroScope_4691_);
lean_inc(v_usedQuotCtxts_4690_);
lean_inc(v_scopes_4689_);
lean_inc(v_env_4688_);
lean_dec(v___x_4687_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4707_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 1, v_a_4678_);
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_env_4688_);
lean_ctor_set(v_reuseFailAlloc_4706_, 1, v_a_4678_);
lean_ctor_set(v_reuseFailAlloc_4706_, 2, v_scopes_4689_);
lean_ctor_set(v_reuseFailAlloc_4706_, 3, v_usedQuotCtxts_4690_);
lean_ctor_set(v_reuseFailAlloc_4706_, 4, v_nextMacroScope_4691_);
lean_ctor_set(v_reuseFailAlloc_4706_, 5, v_maxRecDepth_4692_);
lean_ctor_set(v_reuseFailAlloc_4706_, 6, v_ngen_4693_);
lean_ctor_set(v_reuseFailAlloc_4706_, 7, v_auxDeclNGen_4694_);
lean_ctor_set(v_reuseFailAlloc_4706_, 8, v_infoState_4695_);
lean_ctor_set(v_reuseFailAlloc_4706_, 9, v_traceState_4696_);
lean_ctor_set(v_reuseFailAlloc_4706_, 10, v_snapshotTasks_4697_);
v___x_4702_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4703_ = lean_st_ref_set(v_a_4670_, v___x_4702_);
v___x_4704_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4705_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4704_, v_a_4669_, v_a_4670_);
return v___x_4705_;
}
}
}
else
{
lean_object* v___x_4709_; lean_object* v_env_4710_; lean_object* v_scopes_4711_; lean_object* v_usedQuotCtxts_4712_; lean_object* v_nextMacroScope_4713_; lean_object* v_maxRecDepth_4714_; lean_object* v_ngen_4715_; lean_object* v_auxDeclNGen_4716_; lean_object* v_infoState_4717_; lean_object* v_traceState_4718_; lean_object* v_snapshotTasks_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4732_; 
lean_dec(v_a_4678_);
v___x_4709_ = lean_st_ref_take(v_a_4670_);
v_env_4710_ = lean_ctor_get(v___x_4709_, 0);
v_scopes_4711_ = lean_ctor_get(v___x_4709_, 2);
v_usedQuotCtxts_4712_ = lean_ctor_get(v___x_4709_, 3);
v_nextMacroScope_4713_ = lean_ctor_get(v___x_4709_, 4);
v_maxRecDepth_4714_ = lean_ctor_get(v___x_4709_, 5);
v_ngen_4715_ = lean_ctor_get(v___x_4709_, 6);
v_auxDeclNGen_4716_ = lean_ctor_get(v___x_4709_, 7);
v_infoState_4717_ = lean_ctor_get(v___x_4709_, 8);
v_traceState_4718_ = lean_ctor_get(v___x_4709_, 9);
v_snapshotTasks_4719_ = lean_ctor_get(v___x_4709_, 10);
v_isSharedCheck_4732_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4732_ == 0)
{
lean_object* v_unused_4733_; 
v_unused_4733_ = lean_ctor_get(v___x_4709_, 1);
lean_dec(v_unused_4733_);
v___x_4721_ = v___x_4709_;
v_isShared_4722_ = v_isSharedCheck_4732_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_snapshotTasks_4719_);
lean_inc(v_traceState_4718_);
lean_inc(v_infoState_4717_);
lean_inc(v_auxDeclNGen_4716_);
lean_inc(v_ngen_4715_);
lean_inc(v_maxRecDepth_4714_);
lean_inc(v_nextMacroScope_4713_);
lean_inc(v_usedQuotCtxts_4712_);
lean_inc(v_scopes_4711_);
lean_inc(v_env_4710_);
lean_dec(v___x_4709_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4732_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4723_; lean_object* v___x_4725_; 
v___x_4723_ = l_Lean_MessageLog_empty;
if (v_isShared_4722_ == 0)
{
lean_ctor_set(v___x_4721_, 1, v___x_4723_);
v___x_4725_ = v___x_4721_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_env_4710_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4731_, 2, v_scopes_4711_);
lean_ctor_set(v_reuseFailAlloc_4731_, 3, v_usedQuotCtxts_4712_);
lean_ctor_set(v_reuseFailAlloc_4731_, 4, v_nextMacroScope_4713_);
lean_ctor_set(v_reuseFailAlloc_4731_, 5, v_maxRecDepth_4714_);
lean_ctor_set(v_reuseFailAlloc_4731_, 6, v_ngen_4715_);
lean_ctor_set(v_reuseFailAlloc_4731_, 7, v_auxDeclNGen_4716_);
lean_ctor_set(v_reuseFailAlloc_4731_, 8, v_infoState_4717_);
lean_ctor_set(v_reuseFailAlloc_4731_, 9, v_traceState_4718_);
lean_ctor_set(v_reuseFailAlloc_4731_, 10, v_snapshotTasks_4719_);
v___x_4725_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4729_; 
v___x_4726_ = lean_st_ref_set(v_a_4670_, v___x_4725_);
v___x_4727_ = lean_box(0);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v___x_4727_);
v___x_4729_ = v___x_4684_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4727_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
}
}
else
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
v_a_4735_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___x_4677_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4677_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4743_, v_a_4744_, v_a_4745_);
lean_dec(v_a_4745_);
lean_dec_ref(v_a_4744_);
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4748_, lean_object* v_as_4749_, lean_object* v_as_x27_4750_, uint8_t v_b_4751_, lean_object* v_a_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4748_, v_as_x27_4750_, v_b_4751_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4757_, lean_object* v_as_4758_, lean_object* v_as_x27_4759_, lean_object* v_b_4760_, lean_object* v_a_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
uint8_t v_foundPanic_boxed_4765_; uint8_t v_b_boxed_4766_; lean_object* v_res_4767_; 
v_foundPanic_boxed_4765_ = lean_unbox(v_foundPanic_4757_);
v_b_boxed_4766_ = lean_unbox(v_b_4760_);
v_res_4767_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4765_, v_as_4758_, v_as_x27_4759_, v_b_boxed_4766_, v_a_4761_, v___y_4762_, v___y_4763_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec(v_as_x27_4759_);
lean_dec(v_as_4758_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4776_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4777_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4778_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4779_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4780_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4776_, v___x_4777_, v___x_4778_, v___x_4779_);
return v___x_4780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4782_;
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
