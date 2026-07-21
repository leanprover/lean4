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
uint8_t v___x_1582__boxed_446_; uint8_t v_res_447_; lean_object* v_r_448_; 
v___x_1582__boxed_446_ = lean_unbox(v___x_444_);
v_res_447_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_1582__boxed_446_, v_x_445_);
lean_dec_ref(v_x_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(uint8_t v___x_449_, lean_object* v_msg_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = l_Lean_Message_isTrace(v_msg_450_);
if (v___x_451_ == 0)
{
uint8_t v_severity_452_; uint8_t v___x_453_; uint8_t v___x_454_; 
v_severity_452_ = lean_ctor_get_uint8(v_msg_450_, sizeof(void*)*5 + 1);
v___x_453_ = 2;
v___x_454_ = l_Lean_instBEqMessageSeverity_beq(v_severity_452_, v___x_453_);
return v___x_454_;
}
else
{
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object* v___x_455_, lean_object* v_msg_456_){
_start:
{
uint8_t v___x_1588__boxed_457_; uint8_t v_res_458_; lean_object* v_r_459_; 
v___x_1588__boxed_457_ = lean_unbox(v___x_455_);
v_res_458_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_1588__boxed_457_, v_msg_456_);
lean_dec_ref(v_msg_456_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(uint8_t v___x_460_, lean_object* v_msg_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_Lean_Message_isTrace(v_msg_461_);
if (v___x_462_ == 0)
{
uint8_t v_severity_463_; uint8_t v___x_464_; uint8_t v___x_465_; 
v_severity_463_ = lean_ctor_get_uint8(v_msg_461_, sizeof(void*)*5 + 1);
v___x_464_ = 1;
v___x_465_ = l_Lean_instBEqMessageSeverity_beq(v_severity_463_, v___x_464_);
return v___x_465_;
}
else
{
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object* v___x_466_, lean_object* v_msg_467_){
_start:
{
uint8_t v___x_1597__boxed_468_; uint8_t v_res_469_; lean_object* v_r_470_; 
v___x_1597__boxed_468_ = lean_unbox(v___x_466_);
v_res_469_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_1597__boxed_468_, v_msg_467_);
lean_dec_ref(v_msg_467_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(uint8_t v___x_471_, lean_object* v_msg_472_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = l_Lean_Message_isTrace(v_msg_472_);
if (v___x_473_ == 0)
{
uint8_t v_severity_474_; uint8_t v___x_475_; uint8_t v___x_476_; 
v_severity_474_ = lean_ctor_get_uint8(v_msg_472_, sizeof(void*)*5 + 1);
v___x_475_ = 0;
v___x_476_ = l_Lean_instBEqMessageSeverity_beq(v_severity_474_, v___x_475_);
return v___x_476_;
}
else
{
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object* v___x_477_, lean_object* v_msg_478_){
_start:
{
uint8_t v___x_1606__boxed_479_; uint8_t v_res_480_; lean_object* v_r_481_; 
v___x_1606__boxed_479_ = lean_unbox(v___x_477_);
v_res_480_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_1606__boxed_479_, v_msg_478_);
lean_dec_ref(v_msg_478_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(lean_object* v_x_507_){
_start:
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1));
lean_inc(v_x_507_);
v___x_510_ = l_Lean_Syntax_isOfKind(v_x_507_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec(v_x_507_);
v___x_511_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = l_Lean_Syntax_getArg(v_x_507_, v___x_512_);
lean_dec(v_x_507_);
v___x_514_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3));
lean_inc(v___x_513_);
v___x_515_ = l_Lean_Syntax_isOfKind(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5));
lean_inc(v___x_513_);
v___x_517_ = l_Lean_Syntax_isOfKind(v___x_513_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7));
lean_inc(v___x_513_);
v___x_519_ = l_Lean_Syntax_isOfKind(v___x_513_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9));
lean_inc(v___x_513_);
v___x_521_ = l_Lean_Syntax_isOfKind(v___x_513_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11));
v___x_523_ = l_Lean_Syntax_isOfKind(v___x_513_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v___f_526_; lean_object* v___x_527_; 
v___x_525_ = lean_box(v___x_523_);
v___f_526_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_526_, 0, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___f_526_);
return v___x_527_;
}
}
else
{
lean_object* v___x_528_; lean_object* v___f_529_; lean_object* v___x_530_; 
lean_dec(v___x_513_);
v___x_528_ = lean_box(v___x_519_);
v___f_529_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_529_, 0, v___x_528_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___f_529_);
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___f_532_; lean_object* v___x_533_; 
lean_dec(v___x_513_);
v___x_531_ = lean_box(v___x_517_);
v___f_532_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_532_, 0, v___x_531_);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___f_532_);
return v___x_533_;
}
}
else
{
lean_object* v___x_534_; lean_object* v___f_535_; lean_object* v___x_536_; 
lean_dec(v___x_513_);
v___x_534_ = lean_box(v___x_515_);
v___f_535_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_535_, 0, v___x_534_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___f_535_);
return v___x_536_;
}
}
else
{
lean_object* v___f_537_; lean_object* v___x_538_; 
lean_dec(v___x_513_);
v___f_537_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12));
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___f_537_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___boxed(lean_object* v_x_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(lean_object* v_x_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_542_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___boxed(lean_object* v_x_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(v_x_547_, v_a_548_, v_a_549_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
return v_res_551_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object* v_x_552_){
_start:
{
uint8_t v___x_553_; 
v___x_553_ = 0;
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object* v_x_554_){
_start:
{
uint8_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(v_x_554_);
lean_dec_ref(v_x_554_);
v_r_556_ = lean_box(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(lean_object* v_snd_557_, lean_object* v___y_558_){
_start:
{
if (lean_obj_tag(v_snd_557_) == 0)
{
uint8_t v___x_559_; 
lean_dec_ref(v___y_558_);
v___x_559_ = 0;
return v___x_559_;
}
else
{
lean_object* v_val_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_val_560_ = lean_ctor_get(v_snd_557_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v_snd_557_, 1);
v___x_561_ = lean_apply_1(v_val_560_, v___y_558_);
v___x_562_ = lean_unbox(v___x_561_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed(lean_object* v_snd_563_, lean_object* v___y_564_){
_start:
{
uint8_t v_res_565_; lean_object* v_r_566_; 
v_res_565_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(v_snd_563_, v___y_564_);
v_r_566_ = lean_box(v_res_565_);
return v_r_566_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(lean_object* v_a_567_, lean_object* v_snd_568_, uint8_t v_a_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
lean_inc_ref(v___y_570_);
v___x_571_ = lean_apply_1(v_a_567_, v___y_570_);
v___x_572_ = lean_unbox(v___x_571_);
if (v___x_572_ == 0)
{
if (lean_obj_tag(v_snd_568_) == 0)
{
uint8_t v___x_573_; 
lean_dec_ref(v___y_570_);
v___x_573_ = 2;
return v___x_573_;
}
else
{
lean_object* v_val_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_val_574_ = lean_ctor_get(v_snd_568_, 0);
lean_inc(v_val_574_);
lean_dec_ref_known(v_snd_568_, 1);
v___x_575_ = lean_apply_1(v_val_574_, v___y_570_);
v___x_576_ = lean_unbox(v___x_575_);
return v___x_576_;
}
}
else
{
lean_dec_ref(v___y_570_);
lean_dec(v_snd_568_);
return v_a_569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed(lean_object* v_a_577_, lean_object* v_snd_578_, lean_object* v_a_579_, lean_object* v___y_580_){
_start:
{
uint8_t v_a_11568__boxed_581_; uint8_t v_res_582_; lean_object* v_r_583_; 
v_a_11568__boxed_581_ = lean_unbox(v_a_579_);
v_res_582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_577_, v_snd_578_, v_a_11568__boxed_581_, v___y_580_);
v_r_583_ = lean_box(v_res_582_);
return v_r_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object* v_as_644_, size_t v_sz_645_, size_t v_i_646_, lean_object* v_b_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_a_652_; uint8_t v___x_656_; 
v___x_656_ = lean_usize_dec_lt(v_i_646_, v_sz_645_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v_b_647_);
return v___x_657_;
}
else
{
lean_object* v_snd_658_; lean_object* v_snd_659_; lean_object* v_snd_660_; lean_object* v_fst_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_968_; 
v_snd_658_ = lean_ctor_get(v_b_647_, 1);
lean_inc(v_snd_658_);
v_snd_659_ = lean_ctor_get(v_snd_658_, 1);
lean_inc(v_snd_659_);
v_snd_660_ = lean_ctor_get(v_snd_659_, 1);
lean_inc(v_snd_660_);
v_fst_661_ = lean_ctor_get(v_b_647_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v_b_647_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v_b_647_, 1);
lean_dec(v_unused_969_);
v___x_663_ = v_b_647_;
v_isShared_664_ = v_isSharedCheck_968_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_fst_661_);
lean_dec(v_b_647_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_968_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_fst_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_966_; 
v_fst_665_ = lean_ctor_get(v_snd_658_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v_snd_658_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v_snd_658_, 1);
lean_dec(v_unused_967_);
v___x_667_ = v_snd_658_;
v_isShared_668_ = v_isSharedCheck_966_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_fst_665_);
lean_dec(v_snd_658_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_966_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_fst_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_964_; 
v_fst_669_ = lean_ctor_get(v_snd_659_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_snd_659_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v_snd_659_, 1);
lean_dec(v_unused_965_);
v___x_671_ = v_snd_659_;
v_isShared_672_ = v_isSharedCheck_964_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_fst_669_);
lean_dec(v_snd_659_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_964_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_963_; 
v_fst_673_ = lean_ctor_get(v_snd_660_, 0);
v_snd_674_ = lean_ctor_get(v_snd_660_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_snd_660_);
if (v_isSharedCheck_963_ == 0)
{
v___x_676_ = v_snd_660_;
v_isShared_677_ = v_isSharedCheck_963_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_snd_674_);
lean_inc(v_fst_673_);
lean_dec(v_snd_660_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_963_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_a_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_a_678_ = lean_array_uget_borrowed(v_as_644_, v_i_646_);
v___x_679_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_a_678_);
v___x_680_ = l_Lean_Syntax_isOfKind(v_a_678_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_683_; 
lean_dec_ref_known(v___x_681_, 1);
if (v_isShared_677_ == 0)
{
v___x_683_ = v___x_676_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_fst_673_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_snd_674_);
v___x_683_ = v_reuseFailAlloc_693_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_685_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___x_683_);
v___x_685_ = v___x_671_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fst_669_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_683_);
v___x_685_ = v_reuseFailAlloc_692_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_687_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_685_);
v___x_687_ = v___x_667_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_fst_665_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_685_);
v___x_687_ = v_reuseFailAlloc_691_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_687_);
v___x_689_ = v___x_663_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_fst_661_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
v_a_652_ = v___x_689_;
goto v___jp_651_;
}
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_del_object(v___x_676_);
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_del_object(v___x_671_);
lean_dec(v_fst_669_);
lean_del_object(v___x_667_);
lean_dec(v_fst_665_);
lean_del_object(v___x_663_);
lean_dec(v_fst_661_);
v_a_694_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_681_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_681_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_action_x3f_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = l_Lean_Syntax_getArg(v_a_678_, v___x_702_);
v___x_744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3));
lean_inc(v___x_703_);
v___x_745_ = l_Lean_Syntax_isOfKind(v___x_703_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; uint8_t v___x_747_; 
lean_del_object(v___x_676_);
lean_del_object(v___x_671_);
lean_del_object(v___x_667_);
lean_del_object(v___x_663_);
v___x_746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5));
lean_inc(v___x_703_);
v___x_747_ = l_Lean_Syntax_isOfKind(v___x_703_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; uint8_t v_reportPositions_749_; 
v___x_748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7));
lean_inc(v___x_703_);
v_reportPositions_749_ = l_Lean_Syntax_isOfKind(v___x_703_, v___x_748_);
if (v_reportPositions_749_ == 0)
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9));
lean_inc(v___x_703_);
v___x_751_ = l_Lean_Syntax_isOfKind(v___x_703_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11));
lean_inc(v___x_703_);
v___x_753_ = l_Lean_Syntax_isOfKind(v___x_703_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
lean_dec(v___x_703_);
v___x_754_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec_ref_known(v___x_754_, 1);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_fst_673_);
lean_ctor_set(v___x_755_, 1, v_snd_674_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_fst_669_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_fst_665_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_fst_661_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v_a_652_ = v___x_758_;
goto v___jp_651_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
v_a_759_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_754_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_754_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_767_ = lean_unsigned_to_nat(2u);
v___x_768_ = l_Lean_Syntax_getArg(v___x_703_, v___x_767_);
lean_dec(v___x_703_);
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_768_);
v___x_770_ = l_Lean_Syntax_isOfKind(v___x_768_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_772_ = l_Lean_Syntax_isOfKind(v___x_768_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec_ref_known(v___x_773_, 1);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_fst_673_);
lean_ctor_set(v___x_774_, 1, v_snd_674_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_fst_669_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_fst_665_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_fst_661_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v_a_652_ = v___x_777_;
goto v___jp_651_;
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
v_a_778_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_773_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_773_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v_fst_673_);
v___x_786_ = lean_box(v_reportPositions_749_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v_snd_674_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_fst_669_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_fst_665_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_fst_661_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v_a_652_ = v___x_790_;
goto v___jp_651_;
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v___x_768_);
lean_dec(v_fst_673_);
v___x_791_ = lean_box(v___x_680_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v_snd_674_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_fst_669_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v_fst_665_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_fst_661_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v_a_652_ = v___x_795_;
goto v___jp_651_;
}
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_796_ = lean_unsigned_to_nat(2u);
v___x_797_ = l_Lean_Syntax_getArg(v___x_703_, v___x_796_);
lean_dec(v___x_703_);
v___x_798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17));
lean_inc(v___x_797_);
v___x_799_ = l_Lean_Syntax_isOfKind(v___x_797_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
lean_dec(v___x_797_);
v___x_800_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec_ref_known(v___x_800_, 1);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_fst_673_);
lean_ctor_set(v___x_801_, 1, v_snd_674_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_fst_669_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_fst_665_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_fst_661_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v_a_652_ = v___x_804_;
goto v___jp_651_;
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
v_a_805_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_800_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_800_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_813_ = l_Lean_Syntax_getArg(v___x_797_, v___x_702_);
lean_dec(v___x_797_);
v___x_814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_813_);
v___x_815_ = l_Lean_Syntax_isOfKind(v___x_813_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_817_ = l_Lean_Syntax_isOfKind(v___x_813_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec_ref_known(v___x_818_, 1);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_fst_673_);
lean_ctor_set(v___x_819_, 1, v_snd_674_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_fst_669_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_fst_665_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v_fst_661_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v_a_652_ = v___x_822_;
goto v___jp_651_;
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
v_a_823_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_818_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_818_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec(v_fst_669_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_fst_673_);
lean_ctor_set(v___x_831_, 1, v_snd_674_);
v___x_832_ = lean_box(v_reportPositions_749_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_831_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_fst_665_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_fst_661_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v_a_652_ = v___x_835_;
goto v___jp_651_;
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v___x_813_);
lean_dec(v_fst_669_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_fst_673_);
lean_ctor_set(v___x_836_, 1, v_snd_674_);
v___x_837_ = lean_box(v___x_680_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___x_836_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v_fst_665_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v_fst_661_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v_a_652_ = v___x_840_;
goto v___jp_651_;
}
}
}
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_841_ = lean_unsigned_to_nat(2u);
v___x_842_ = l_Lean_Syntax_getArg(v___x_703_, v___x_841_);
lean_dec(v___x_703_);
v___x_843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19));
lean_inc(v___x_842_);
v___x_844_ = l_Lean_Syntax_isOfKind(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
lean_dec(v___x_842_);
v___x_845_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref_known(v___x_845_, 1);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v_fst_673_);
lean_ctor_set(v___x_846_, 1, v_snd_674_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_fst_669_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_fst_665_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_fst_661_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v_a_652_ = v___x_849_;
goto v___jp_651_;
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
v_a_850_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_845_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_845_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_858_ = l_Lean_Syntax_getArg(v___x_842_, v___x_702_);
lean_dec(v___x_842_);
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_858_);
v___x_860_ = l_Lean_Syntax_isOfKind(v___x_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23));
v___x_862_ = l_Lean_Syntax_isOfKind(v___x_858_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec_ref_known(v___x_863_, 1);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v_fst_673_);
lean_ctor_set(v___x_864_, 1, v_snd_674_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v_fst_669_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v_fst_665_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v_fst_661_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v_a_652_ = v___x_867_;
goto v___jp_651_;
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
v_a_868_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_863_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_863_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec(v_fst_665_);
v___x_876_ = 1;
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_fst_673_);
lean_ctor_set(v___x_877_, 1, v_snd_674_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_fst_669_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_box(v___x_876_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v___x_878_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v_fst_661_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v_a_652_ = v___x_881_;
goto v___jp_651_;
}
}
else
{
uint8_t v_ordering_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec(v___x_858_);
lean_dec(v_fst_665_);
v_ordering_882_ = 0;
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v_fst_673_);
lean_ctor_set(v___x_883_, 1, v_snd_674_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v_fst_669_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = lean_box(v_ordering_882_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v_fst_661_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v_a_652_ = v___x_887_;
goto v___jp_651_;
}
}
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_888_ = lean_unsigned_to_nat(2u);
v___x_889_ = l_Lean_Syntax_getArg(v___x_703_, v___x_888_);
lean_dec(v___x_703_);
v___x_890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25));
lean_inc(v___x_889_);
v___x_891_ = l_Lean_Syntax_isOfKind(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_dec(v___x_889_);
v___x_892_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref_known(v___x_892_, 1);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_fst_673_);
lean_ctor_set(v___x_893_, 1, v_snd_674_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v_fst_669_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v_fst_665_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v_fst_661_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v_a_652_ = v___x_896_;
goto v___jp_651_;
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
v_a_897_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_892_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_892_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_905_ = l_Lean_Syntax_getArg(v___x_889_, v___x_702_);
lean_dec(v___x_889_);
v___x_906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_905_);
v___x_907_ = l_Lean_Syntax_isOfKind(v___x_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27));
lean_inc(v___x_905_);
v___x_909_ = l_Lean_Syntax_isOfKind(v___x_905_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29));
v___x_911_ = l_Lean_Syntax_isOfKind(v___x_905_, v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec_ref_known(v___x_912_, 1);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_fst_673_);
lean_ctor_set(v___x_913_, 1, v_snd_674_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_fst_669_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v_fst_665_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_fst_661_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v_a_652_ = v___x_916_;
goto v___jp_651_;
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
v_a_917_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_912_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_912_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec(v_fst_661_);
v___x_925_ = 2;
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_fst_673_);
lean_ctor_set(v___x_926_, 1, v_snd_674_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_fst_669_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_fst_665_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = lean_box(v___x_925_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_928_);
v_a_652_ = v___x_930_;
goto v___jp_651_;
}
}
else
{
uint8_t v_whitespace_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec(v___x_905_);
lean_dec(v_fst_661_);
v_whitespace_931_ = 1;
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_fst_673_);
lean_ctor_set(v___x_932_, 1, v_snd_674_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_fst_669_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_fst_665_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_box(v_whitespace_931_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_934_);
v_a_652_ = v___x_936_;
goto v___jp_651_;
}
}
else
{
uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v___x_905_);
lean_dec(v_fst_661_);
v___x_937_ = 0;
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_fst_673_);
lean_ctor_set(v___x_938_, 1, v_snd_674_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_fst_669_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v_fst_665_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_box(v___x_937_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
v_a_652_ = v___x_942_;
goto v___jp_651_;
}
}
}
}
else
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = l_Lean_Syntax_getArg(v___x_703_, v___x_702_);
v___x_944_ = l_Lean_Syntax_isNone(v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_945_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_943_);
v___x_946_ = l_Lean_Syntax_matchesNull(v___x_943_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
lean_dec(v___x_943_);
lean_dec(v___x_703_);
lean_del_object(v___x_676_);
lean_del_object(v___x_671_);
lean_del_object(v___x_667_);
lean_del_object(v___x_663_);
v___x_947_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec_ref_known(v___x_947_, 1);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v_fst_673_);
lean_ctor_set(v___x_948_, 1, v_snd_674_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_fst_669_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v_fst_665_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v_fst_661_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v_a_652_ = v___x_951_;
goto v___jp_651_;
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
v_a_952_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_947_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_947_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = l_Lean_Syntax_getArg(v___x_943_, v___x_702_);
lean_dec(v___x_943_);
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
v_action_x3f_705_ = v___x_961_;
v___y_706_ = v___y_648_;
v___y_707_ = v___y_649_;
goto v___jp_704_;
}
}
else
{
lean_object* v___x_962_; 
lean_dec(v___x_943_);
v___x_962_ = lean_box(0);
v_action_x3f_705_ = v___x_962_;
v___y_706_ = v___y_648_;
v___y_707_ = v___y_649_;
goto v___jp_704_;
}
}
v___jp_704_:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_705_, v___y_706_, v___y_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = l_Lean_Syntax_getArg(v___x_703_, v___x_710_);
lean_dec(v___x_703_);
v___x_712_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v___x_711_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___f_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v___f_714_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_714_, 0, v_a_713_);
lean_closure_set(v___f_714_, 1, v_snd_674_);
lean_closure_set(v___f_714_, 2, v_a_709_);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v___f_714_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v___x_715_);
v___x_717_ = v___x_676_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_fst_673_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_727_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___x_717_);
v___x_719_ = v___x_671_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_fst_669_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_726_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_719_);
v___x_721_ = v___x_667_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_fst_665_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_719_);
v___x_721_ = v_reuseFailAlloc_725_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_721_);
v___x_723_ = v___x_663_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_fst_661_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
v_a_652_ = v___x_723_;
goto v___jp_651_;
}
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_a_709_);
lean_del_object(v___x_676_);
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_del_object(v___x_671_);
lean_dec(v_fst_669_);
lean_del_object(v___x_667_);
lean_dec(v_fst_665_);
lean_del_object(v___x_663_);
lean_dec(v_fst_661_);
v_a_728_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_712_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_712_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v___x_703_);
lean_del_object(v___x_676_);
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_del_object(v___x_671_);
lean_dec(v_fst_669_);
lean_del_object(v___x_667_);
lean_dec(v_fst_665_);
lean_del_object(v___x_663_);
lean_dec(v_fst_661_);
v_a_736_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_708_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_708_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
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
v___jp_651_:
{
size_t v___x_653_; size_t v___x_654_; 
v___x_653_ = ((size_t)1ULL);
v___x_654_ = lean_usize_add(v_i_646_, v___x_653_);
v_i_646_ = v___x_654_;
v_b_647_ = v_a_652_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object* v_as_970_, lean_object* v_sz_971_, lean_object* v_i_972_, lean_object* v_b_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
size_t v_sz_boxed_977_; size_t v_i_boxed_978_; lean_object* v_res_979_; 
v_sz_boxed_977_ = lean_unbox_usize(v_sz_971_);
lean_dec(v_sz_971_);
v_i_boxed_978_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_res_979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v_as_970_, v_sz_boxed_977_, v_i_boxed_978_, v_b_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec_ref(v_as_970_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(size_t v_sz_980_, size_t v_i_981_, lean_object* v_bs_982_){
_start:
{
uint8_t v___x_983_; 
v___x_983_ = lean_usize_dec_lt(v_i_981_, v_sz_980_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v_bs_982_);
return v___x_984_;
}
else
{
lean_object* v_v_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_v_985_ = lean_array_uget(v_bs_982_, v_i_981_);
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_v_985_);
v___x_987_ = l_Lean_Syntax_isOfKind(v_v_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
lean_dec(v_v_985_);
lean_dec_ref(v_bs_982_);
v___x_988_ = lean_box(0);
return v___x_988_;
}
else
{
lean_object* v___x_989_; lean_object* v_bs_x27_990_; size_t v___x_991_; size_t v___x_992_; lean_object* v___x_993_; 
v___x_989_ = lean_unsigned_to_nat(0u);
v_bs_x27_990_ = lean_array_uset(v_bs_982_, v_i_981_, v___x_989_);
v___x_991_ = ((size_t)1ULL);
v___x_992_ = lean_usize_add(v_i_981_, v___x_991_);
v___x_993_ = lean_array_uset(v_bs_x27_990_, v_i_981_, v_v_985_);
v_i_981_ = v___x_992_;
v_bs_982_ = v___x_993_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1___boxed(lean_object* v_sz_995_, lean_object* v_i_996_, lean_object* v_bs_997_){
_start:
{
size_t v_sz_boxed_998_; size_t v_i_boxed_999_; lean_object* v_res_1000_; 
v_sz_boxed_998_ = lean_unbox_usize(v_sz_995_);
lean_dec(v_sz_995_);
v_i_boxed_999_ = lean_unbox_usize(v_i_996_);
lean_dec(v_i_996_);
v_res_1000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_boxed_998_, v_i_boxed_999_, v_bs_997_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(uint8_t v___x_1001_, lean_object* v_as_1002_, size_t v_i_1003_, size_t v_stop_1004_, lean_object* v_b_1005_){
_start:
{
lean_object* v___y_1007_; uint8_t v___x_1011_; 
v___x_1011_ = lean_usize_dec_eq(v_i_1003_, v_stop_1004_);
if (v___x_1011_ == 0)
{
lean_object* v_fst_1012_; uint8_t v___x_1013_; 
v_fst_1012_ = lean_ctor_get(v_b_1005_, 0);
v___x_1013_ = lean_unbox(v_fst_1012_);
if (v___x_1013_ == 0)
{
lean_object* v_snd_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
v_snd_1014_ = lean_ctor_get(v_b_1005_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_b_1005_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_b_1005_, 0);
lean_dec(v_unused_1023_);
v___x_1016_ = v_b_1005_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_snd_1014_);
lean_dec(v_b_1005_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_box(v___x_1001_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_snd_1014_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
v___y_1007_ = v___x_1020_;
goto v___jp_1006_;
}
}
}
else
{
lean_object* v_snd_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1034_; 
v_snd_1024_ = lean_ctor_get(v_b_1005_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_b_1005_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v_b_1005_, 0);
lean_dec(v_unused_1035_);
v___x_1026_ = v_b_1005_;
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_snd_1024_);
lean_dec(v_b_1005_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1028_ = lean_array_uget_borrowed(v_as_1002_, v_i_1003_);
lean_inc(v___x_1028_);
v___x_1029_ = lean_array_push(v_snd_1024_, v___x_1028_);
v___x_1030_ = lean_box(v___x_1011_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v___x_1029_);
lean_ctor_set(v___x_1026_, 0, v___x_1030_);
v___x_1032_ = v___x_1026_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_1029_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
v___y_1007_ = v___x_1032_;
goto v___jp_1006_;
}
}
}
}
else
{
return v_b_1005_;
}
v___jp_1006_:
{
size_t v___x_1008_; size_t v___x_1009_; 
v___x_1008_ = ((size_t)1ULL);
v___x_1009_ = lean_usize_add(v_i_1003_, v___x_1008_);
v_i_1003_ = v___x_1009_;
v_b_1005_ = v___y_1007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object* v___x_1036_, lean_object* v_as_1037_, lean_object* v_i_1038_, lean_object* v_stop_1039_, lean_object* v_b_1040_){
_start:
{
uint8_t v___x_12443__boxed_1041_; size_t v_i_boxed_1042_; size_t v_stop_boxed_1043_; lean_object* v_res_1044_; 
v___x_12443__boxed_1041_ = lean_unbox(v___x_1036_);
v_i_boxed_1042_ = lean_unbox_usize(v_i_1038_);
lean_dec(v_i_1038_);
v_stop_boxed_1043_ = lean_unbox_usize(v_stop_1039_);
lean_dec(v_stop_1039_);
v_res_1044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_12443__boxed_1041_, v_as_1037_, v_i_boxed_1042_, v_stop_boxed_1043_, v_b_1040_);
lean_dec_ref(v_as_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object* v_spec_x3f_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_elts_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1117_; lean_object* v_cfg_1131_; 
v_cfg_1131_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5));
if (lean_obj_tag(v_spec_x3f_1073_) == 1)
{
lean_object* v_val_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_val_1132_ = lean_ctor_get(v_spec_x3f_1073_, 0);
lean_inc_n(v_val_1132_, 2);
lean_dec_ref_known(v_spec_x3f_1073_, 1);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7));
v___x_1134_ = l_Lean_Syntax_isOfKind(v_val_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_val_1132_);
v___x_1135_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = l_Lean_Syntax_getArg(v_val_1132_, v___x_1144_);
lean_dec(v_val_1132_);
v___x_1146_ = l_Lean_Syntax_getArgs(v___x_1145_);
lean_dec(v___x_1145_);
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8));
v___x_1149_ = lean_array_get_size(v___x_1146_);
v___x_1150_ = lean_nat_dec_lt(v___x_1147_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_dec_ref(v___x_1146_);
v___y_1117_ = v___x_1148_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1151_ = lean_box(v___x_1134_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
lean_ctor_set(v___x_1152_, 1, v___x_1148_);
v___x_1153_ = lean_nat_dec_le(v___x_1149_, v___x_1149_);
if (v___x_1153_ == 0)
{
if (v___x_1150_ == 0)
{
lean_dec_ref_known(v___x_1152_, 2);
lean_dec_ref(v___x_1146_);
v___y_1117_ = v___x_1148_;
goto v___jp_1116_;
}
else
{
size_t v___x_1154_; size_t v___x_1155_; lean_object* v___x_1156_; lean_object* v_snd_1157_; 
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = lean_usize_of_nat(v___x_1149_);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1134_, v___x_1146_, v___x_1154_, v___x_1155_, v___x_1152_);
lean_dec_ref(v___x_1146_);
v_snd_1157_ = lean_ctor_get(v___x_1156_, 1);
lean_inc(v_snd_1157_);
lean_dec_ref(v___x_1156_);
v___y_1117_ = v_snd_1157_;
goto v___jp_1116_;
}
}
else
{
size_t v___x_1158_; size_t v___x_1159_; lean_object* v___x_1160_; lean_object* v_snd_1161_; 
v___x_1158_ = ((size_t)0ULL);
v___x_1159_ = lean_usize_of_nat(v___x_1149_);
v___x_1160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1134_, v___x_1146_, v___x_1158_, v___x_1159_, v___x_1152_);
lean_dec_ref(v___x_1146_);
v_snd_1161_ = lean_ctor_get(v___x_1160_, 1);
lean_inc(v_snd_1161_);
lean_dec_ref(v___x_1160_);
v___y_1117_ = v_snd_1161_;
goto v___jp_1116_;
}
}
}
}
else
{
lean_object* v___x_1162_; 
lean_dec(v_spec_x3f_1073_);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_cfg_1131_);
return v___x_1162_;
}
v___jp_1077_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; size_t v_sz_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1081_ = l_Array_reverse___redArg(v_elts_1078_);
v___x_1082_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4));
v_sz_1083_ = lean_array_size(v___x_1081_);
v___x_1084_ = ((size_t)0ULL);
v___x_1085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v___x_1081_, v_sz_1083_, v___x_1084_, v___x_1082_, v___y_1079_, v___y_1080_);
lean_dec_ref(v___x_1081_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1107_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1107_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1107_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_snd_1090_; lean_object* v_snd_1091_; lean_object* v_snd_1092_; lean_object* v_fst_1093_; lean_object* v_fst_1094_; lean_object* v_fst_1095_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___y_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; uint8_t v___x_1101_; uint8_t v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1105_; 
v_snd_1090_ = lean_ctor_get(v_a_1086_, 1);
lean_inc(v_snd_1090_);
v_snd_1091_ = lean_ctor_get(v_snd_1090_, 1);
lean_inc(v_snd_1091_);
v_snd_1092_ = lean_ctor_get(v_snd_1091_, 1);
lean_inc(v_snd_1092_);
v_fst_1093_ = lean_ctor_get(v_a_1086_, 0);
lean_inc(v_fst_1093_);
lean_dec(v_a_1086_);
v_fst_1094_ = lean_ctor_get(v_snd_1090_, 0);
lean_inc(v_fst_1094_);
lean_dec(v_snd_1090_);
v_fst_1095_ = lean_ctor_get(v_snd_1091_, 0);
lean_inc(v_fst_1095_);
lean_dec(v_snd_1091_);
v_fst_1096_ = lean_ctor_get(v_snd_1092_, 0);
lean_inc(v_fst_1096_);
v_snd_1097_ = lean_ctor_get(v_snd_1092_, 1);
lean_inc(v_snd_1097_);
lean_dec(v_snd_1092_);
v___y_1098_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___y_1098_, 0, v_snd_1097_);
v___x_1099_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1099_, 0, v___y_1098_);
v___x_1100_ = lean_unbox(v_fst_1093_);
lean_dec(v_fst_1093_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*1, v___x_1100_);
v___x_1101_ = lean_unbox(v_fst_1094_);
lean_dec(v_fst_1094_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*1 + 1, v___x_1101_);
v___x_1102_ = lean_unbox(v_fst_1095_);
lean_dec(v_fst_1095_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*1 + 2, v___x_1102_);
v___x_1103_ = lean_unbox(v_fst_1096_);
lean_dec(v_fst_1096_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*1 + 3, v___x_1103_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1099_);
v___x_1105_ = v___x_1088_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1099_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1085_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1085_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
v___jp_1116_:
{
size_t v_sz_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
v_sz_1118_ = lean_array_size(v___y_1117_);
v___x_1119_ = ((size_t)0ULL);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_1118_, v___x_1119_, v___y_1117_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v___x_1121_; lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v___x_1121_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
else
{
lean_object* v_val_1130_; 
v_val_1130_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_val_1130_);
lean_dec_ref_known(v___x_1120_, 1);
v_elts_1078_ = v_val_1130_;
v___y_1079_ = v_a_1074_;
v___y_1080_ = v_a_1075_;
goto v___jp_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object* v_spec_x3f_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v_spec_x3f_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(lean_object* v_s_1180_, lean_object* v_replacement_1181_, lean_object* v_a_1182_, lean_object* v_b_1183_){
_start:
{
lean_object* v_it_1185_; lean_object* v_startPos_1186_; lean_object* v_endPos_1187_; lean_object* v_it_1196_; 
switch(lean_obj_tag(v_a_1182_))
{
case 0:
{
lean_object* v_pos_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1214_; 
v_pos_1202_ = lean_ctor_get(v_a_1182_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_a_1182_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1204_ = v_a_1182_;
v_isShared_1205_ = v_isSharedCheck_1214_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_pos_1202_);
lean_dec(v_a_1182_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1214_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_startInclusive_1206_; lean_object* v_endExclusive_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v_startInclusive_1206_ = lean_ctor_get(v_s_1180_, 1);
v_endExclusive_1207_ = lean_ctor_get(v_s_1180_, 2);
v___x_1208_ = lean_nat_sub(v_endExclusive_1207_, v_startInclusive_1206_);
v___x_1209_ = lean_nat_dec_eq(v_pos_1202_, v___x_1208_);
lean_dec(v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1211_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set_tag(v___x_1204_, 1);
v___x_1211_ = v___x_1204_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_pos_1202_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
v_it_1196_ = v___x_1211_;
goto v___jp_1195_;
}
}
else
{
lean_object* v___x_1213_; 
lean_del_object(v___x_1204_);
lean_dec(v_pos_1202_);
v___x_1213_ = lean_box(3);
v_it_1196_ = v___x_1213_;
goto v___jp_1195_;
}
}
}
case 1:
{
lean_object* v_pos_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1227_; 
v_pos_1215_ = lean_ctor_get(v_a_1182_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_a_1182_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1217_ = v_a_1182_;
v_isShared_1218_ = v_isSharedCheck_1227_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_pos_1215_);
lean_dec(v_a_1182_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1227_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_str_1219_; lean_object* v_startInclusive_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v_str_1219_ = lean_ctor_get(v_s_1180_, 0);
v_startInclusive_1220_ = lean_ctor_get(v_s_1180_, 1);
v___x_1221_ = lean_nat_add(v_startInclusive_1220_, v_pos_1215_);
v___x_1222_ = lean_string_utf8_next_fast(v_str_1219_, v___x_1221_);
lean_dec(v___x_1221_);
v___x_1223_ = lean_nat_sub(v___x_1222_, v_startInclusive_1220_);
lean_inc(v___x_1223_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set_tag(v___x_1217_, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1223_);
v___x_1225_ = v___x_1217_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
v_it_1185_ = v___x_1225_;
v_startPos_1186_ = v_pos_1215_;
v_endPos_1187_ = v___x_1223_;
goto v___jp_1184_;
}
}
}
case 2:
{
lean_object* v_needle_1228_; lean_object* v_table_1229_; lean_object* v_stackPos_1230_; lean_object* v_needlePos_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1290_; 
v_needle_1228_ = lean_ctor_get(v_a_1182_, 0);
v_table_1229_ = lean_ctor_get(v_a_1182_, 1);
v_stackPos_1230_ = lean_ctor_get(v_a_1182_, 2);
v_needlePos_1231_ = lean_ctor_get(v_a_1182_, 3);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_a_1182_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1233_ = v_a_1182_;
v_isShared_1234_ = v_isSharedCheck_1290_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_needlePos_1231_);
lean_inc(v_stackPos_1230_);
lean_inc(v_table_1229_);
lean_inc(v_needle_1228_);
lean_dec(v_a_1182_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1290_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v_str_1235_; lean_object* v_startInclusive_1236_; lean_object* v_endExclusive_1237_; lean_object* v_str_1238_; lean_object* v_startInclusive_1239_; lean_object* v_endExclusive_1240_; lean_object* v_basePos_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_str_1235_ = lean_ctor_get(v_needle_1228_, 0);
v_startInclusive_1236_ = lean_ctor_get(v_needle_1228_, 1);
v_endExclusive_1237_ = lean_ctor_get(v_needle_1228_, 2);
v_str_1238_ = lean_ctor_get(v_s_1180_, 0);
v_startInclusive_1239_ = lean_ctor_get(v_s_1180_, 1);
v_endExclusive_1240_ = lean_ctor_get(v_s_1180_, 2);
v_basePos_1241_ = lean_nat_sub(v_stackPos_1230_, v_needlePos_1231_);
v___x_1242_ = lean_nat_sub(v_endExclusive_1237_, v_startInclusive_1236_);
v___x_1243_ = lean_nat_add(v_basePos_1241_, v___x_1242_);
v___x_1244_ = lean_nat_sub(v_endExclusive_1240_, v_startInclusive_1239_);
v___x_1245_ = lean_nat_dec_le(v___x_1243_, v___x_1244_);
lean_dec(v___x_1243_);
if (v___x_1245_ == 0)
{
uint8_t v___x_1246_; 
lean_dec(v___x_1242_);
lean_del_object(v___x_1233_);
lean_dec(v_needlePos_1231_);
lean_dec(v_stackPos_1230_);
lean_dec_ref(v_table_1229_);
lean_dec_ref(v_needle_1228_);
v___x_1246_ = lean_nat_dec_lt(v_basePos_1241_, v___x_1244_);
if (v___x_1246_ == 0)
{
lean_dec(v___x_1244_);
lean_dec(v_basePos_1241_);
lean_dec_ref(v_s_1180_);
return v_b_1183_;
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = l_String_Slice_pos_x21(v_s_1180_, v_basePos_1241_);
lean_dec(v_basePos_1241_);
v___x_1248_ = lean_box(3);
v_it_1185_ = v___x_1248_;
v_startPos_1186_ = v___x_1247_;
v_endPos_1187_ = v___x_1244_;
goto v___jp_1184_;
}
}
else
{
lean_object* v___x_1249_; uint8_t v_stackByte_1250_; lean_object* v___x_1251_; uint8_t v_patByte_1252_; uint8_t v___x_1253_; 
lean_dec(v___x_1244_);
v___x_1249_ = lean_nat_add(v_startInclusive_1239_, v_stackPos_1230_);
v_stackByte_1250_ = lean_string_get_byte_fast(v_str_1238_, v___x_1249_);
v___x_1251_ = lean_nat_add(v_startInclusive_1236_, v_needlePos_1231_);
v_patByte_1252_ = lean_string_get_byte_fast(v_str_1235_, v___x_1251_);
v___x_1253_ = lean_uint8_dec_eq(v_stackByte_1250_, v_patByte_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
lean_dec(v___x_1242_);
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = lean_nat_dec_eq(v_needlePos_1231_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v_newNeedlePos_1258_; uint8_t v___x_1259_; 
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_sub(v_needlePos_1231_, v___x_1256_);
lean_dec(v_needlePos_1231_);
v_newNeedlePos_1258_ = lean_array_fget_borrowed(v_table_1229_, v___x_1257_);
lean_dec(v___x_1257_);
v___x_1259_ = lean_nat_dec_eq(v_newNeedlePos_1258_, v___x_1254_);
if (v___x_1259_ == 0)
{
lean_object* v_oldBasePos_1260_; lean_object* v___x_1261_; lean_object* v_newBasePos_1262_; lean_object* v___x_1264_; 
lean_inc(v_newNeedlePos_1258_);
v_oldBasePos_1260_ = l_String_Slice_pos_x21(v_s_1180_, v_basePos_1241_);
lean_dec(v_basePos_1241_);
v___x_1261_ = lean_nat_sub(v_stackPos_1230_, v_newNeedlePos_1258_);
v_newBasePos_1262_ = l_String_Slice_pos_x21(v_s_1180_, v___x_1261_);
lean_dec(v___x_1261_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 3, v_newNeedlePos_1258_);
v___x_1264_ = v___x_1233_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_needle_1228_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_table_1229_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_stackPos_1230_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_newNeedlePos_1258_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
v_it_1185_ = v___x_1264_;
v_startPos_1186_ = v_oldBasePos_1260_;
v_endPos_1187_ = v_newBasePos_1262_;
goto v___jp_1184_;
}
}
else
{
lean_object* v_basePos_1266_; lean_object* v_nextStackPos_1267_; lean_object* v___x_1269_; 
v_basePos_1266_ = l_String_Slice_pos_x21(v_s_1180_, v_basePos_1241_);
lean_dec(v_basePos_1241_);
v_nextStackPos_1267_ = l_String_Slice_posGE___redArg(v_s_1180_, v_stackPos_1230_);
lean_inc(v_nextStackPos_1267_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 3, v___x_1254_);
lean_ctor_set(v___x_1233_, 2, v_nextStackPos_1267_);
v___x_1269_ = v___x_1233_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_needle_1228_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_table_1229_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_nextStackPos_1267_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v___x_1254_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
v_it_1185_ = v___x_1269_;
v_startPos_1186_ = v_basePos_1266_;
v_endPos_1187_ = v_nextStackPos_1267_;
goto v___jp_1184_;
}
}
}
else
{
lean_object* v_basePos_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_nextStackPos_1274_; lean_object* v___x_1276_; 
lean_dec(v_basePos_1241_);
lean_dec(v_needlePos_1231_);
v_basePos_1271_ = l_String_Slice_pos_x21(v_s_1180_, v_stackPos_1230_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_add(v_stackPos_1230_, v___x_1272_);
lean_dec(v_stackPos_1230_);
v_nextStackPos_1274_ = l_String_Slice_posGE___redArg(v_s_1180_, v___x_1273_);
lean_inc(v_nextStackPos_1274_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 3, v___x_1254_);
lean_ctor_set(v___x_1233_, 2, v_nextStackPos_1274_);
v___x_1276_ = v___x_1233_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_needle_1228_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_table_1229_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_nextStackPos_1274_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v___x_1254_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
v_it_1185_ = v___x_1276_;
v_startPos_1186_ = v_basePos_1271_;
v_endPos_1187_ = v_nextStackPos_1274_;
goto v___jp_1184_;
}
}
}
else
{
lean_object* v___x_1278_; lean_object* v_nextStackPos_1279_; lean_object* v_nextNeedlePos_1280_; uint8_t v___x_1281_; 
lean_dec(v_basePos_1241_);
v___x_1278_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1279_ = lean_nat_add(v_stackPos_1230_, v___x_1278_);
lean_dec(v_stackPos_1230_);
v_nextNeedlePos_1280_ = lean_nat_add(v_needlePos_1231_, v___x_1278_);
lean_dec(v_needlePos_1231_);
v___x_1281_ = lean_nat_dec_eq(v_nextNeedlePos_1280_, v___x_1242_);
lean_dec(v___x_1242_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1283_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 3, v_nextNeedlePos_1280_);
lean_ctor_set(v___x_1233_, 2, v_nextStackPos_1279_);
v___x_1283_ = v___x_1233_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_needle_1228_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_table_1229_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_nextStackPos_1279_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v_nextNeedlePos_1280_);
v___x_1283_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
v_a_1182_ = v___x_1283_;
goto _start;
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
lean_dec(v_nextNeedlePos_1280_);
v___x_1286_ = lean_unsigned_to_nat(0u);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 3, v___x_1286_);
lean_ctor_set(v___x_1233_, 2, v_nextStackPos_1279_);
v___x_1288_ = v___x_1233_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_needle_1228_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_table_1229_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_nextStackPos_1279_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
v_it_1196_ = v___x_1288_;
goto v___jp_1195_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1180_);
return v_b_1183_;
}
}
v___jp_1184_:
{
lean_object* v___x_1188_; lean_object* v_str_1189_; lean_object* v_startInclusive_1190_; lean_object* v_endExclusive_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_inc_ref(v_s_1180_);
v___x_1188_ = l_String_Slice_slice_x21(v_s_1180_, v_startPos_1186_, v_endPos_1187_);
lean_dec(v_endPos_1187_);
lean_dec(v_startPos_1186_);
v_str_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc_ref(v_str_1189_);
v_startInclusive_1190_ = lean_ctor_get(v___x_1188_, 1);
lean_inc(v_startInclusive_1190_);
v_endExclusive_1191_ = lean_ctor_get(v___x_1188_, 2);
lean_inc(v_endExclusive_1191_);
lean_dec_ref(v___x_1188_);
v___x_1192_ = lean_string_utf8_extract(v_str_1189_, v_startInclusive_1190_, v_endExclusive_1191_);
lean_dec(v_endExclusive_1191_);
lean_dec(v_startInclusive_1190_);
lean_dec_ref(v_str_1189_);
v___x_1193_ = lean_string_append(v_b_1183_, v___x_1192_);
lean_dec_ref(v___x_1192_);
v_a_1182_ = v_it_1185_;
v_b_1183_ = v___x_1193_;
goto _start;
}
v___jp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_string_utf8_byte_size(v_replacement_1181_);
v___x_1199_ = lean_string_utf8_extract(v_replacement_1181_, v___x_1197_, v___x_1198_);
v___x_1200_ = lean_string_append(v_b_1183_, v___x_1199_);
lean_dec_ref(v___x_1199_);
v_a_1182_ = v_it_1196_;
v_b_1183_ = v___x_1200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg___boxed(lean_object* v_s_1291_, lean_object* v_replacement_1292_, lean_object* v_a_1293_, lean_object* v_b_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1291_, v_replacement_1292_, v_a_1293_, v_b_1294_);
lean_dec_ref(v_replacement_1292_);
return v_res_1295_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1298_ = lean_string_utf8_byte_size(v___x_1297_);
return v___x_1298_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1301_ = lean_nat_dec_eq(v___x_1300_, v___x_1299_);
return v___x_1301_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1302_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1);
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__0));
v___x_1305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
lean_ctor_set(v___x_1305_, 2, v___x_1302_);
return v___x_1305_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1307_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1306_);
return v___x_1307_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__4);
v___x_1310_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1311_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v___x_1309_);
lean_ctor_set(v___x_1311_, 2, v___x_1308_);
lean_ctor_set(v___x_1311_, 3, v___x_1308_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object* v_s_1314_, lean_object* v_replacement_1315_){
_start:
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1317_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__5);
v___x_1319_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1314_, v_replacement_1315_, v___x_1318_, v___x_1316_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1321_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1314_, v_replacement_1315_, v___x_1320_, v___x_1316_);
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___boxed(lean_object* v_s_1322_, lean_object* v_replacement_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1322_, v_replacement_1323_);
lean_dec_ref(v_replacement_1323_);
return v_res_1324_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1327_ = lean_string_utf8_byte_size(v___x_1326_);
return v___x_1327_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1330_ = lean_nat_dec_eq(v___x_1329_, v___x_1328_);
return v___x_1330_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1331_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__0));
v___x_1334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1332_);
lean_ctor_set(v___x_1334_, 2, v___x_1331_);
return v___x_1334_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1336_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1335_);
return v___x_1336_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__4);
v___x_1339_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1340_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v___x_1338_);
lean_ctor_set(v___x_1340_, 2, v___x_1337_);
lean_ctor_set(v___x_1340_, 3, v___x_1337_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object* v_s_1341_, lean_object* v_replacement_1342_){
_start:
{
lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1343_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1344_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__5);
v___x_1346_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1341_, v_replacement_1342_, v___x_1345_, v___x_1343_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1348_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1341_, v_replacement_1342_, v___x_1347_, v___x_1343_);
return v___x_1348_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object* v_s_1349_, lean_object* v_replacement_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1349_, v_replacement_1350_);
lean_dec_ref(v_replacement_1350_);
return v_res_1351_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1354_ = lean_string_utf8_byte_size(v___x_1353_);
return v___x_1354_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1357_ = lean_nat_dec_eq(v___x_1356_, v___x_1355_);
return v___x_1357_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1358_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1);
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__0));
v___x_1361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v___x_1359_);
lean_ctor_set(v___x_1361_, 2, v___x_1358_);
return v___x_1361_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1363_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1362_);
return v___x_1363_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__4);
v___x_1366_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1367_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v___x_1365_);
lean_ctor_set(v___x_1367_, 2, v___x_1364_);
lean_ctor_set(v___x_1367_, 3, v___x_1364_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(lean_object* v_s_1368_, lean_object* v_replacement_1369_){
_start:
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1371_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__5);
v___x_1373_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1368_, v_replacement_1369_, v___x_1372_, v___x_1370_);
return v___x_1373_;
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1375_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1368_, v_replacement_1369_, v___x_1374_, v___x_1370_);
return v___x_1375_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___boxed(lean_object* v_s_1376_, lean_object* v_replacement_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1376_, v_replacement_1377_);
lean_dec_ref(v_replacement_1377_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object* v_s_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1383_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0));
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = lean_string_utf8_byte_size(v_s_1382_);
v___x_1386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1386_, 0, v_s_1382_);
lean_ctor_set(v___x_1386_, 1, v___x_1384_);
lean_ctor_set(v___x_1386_, 2, v___x_1385_);
v___x_1387_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1386_, v___x_1383_);
v___x_1388_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1));
v___x_1389_ = lean_string_utf8_byte_size(v___x_1387_);
v___x_1390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1387_);
lean_ctor_set(v___x_1390_, 1, v___x_1384_);
lean_ctor_set(v___x_1390_, 2, v___x_1389_);
v___x_1391_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v___x_1390_, v___x_1388_);
v___x_1392_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2));
v___x_1393_ = lean_string_utf8_byte_size(v___x_1391_);
v___x_1394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1391_);
lean_ctor_set(v___x_1394_, 1, v___x_1384_);
lean_ctor_set(v___x_1394_, 2, v___x_1393_);
v___x_1395_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v___x_1394_, v___x_1392_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(lean_object* v_s_1396_, lean_object* v_pattern_1397_, lean_object* v_replacement_1398_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1396_, v_replacement_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___boxed(lean_object* v_s_1400_, lean_object* v_pattern_1401_, lean_object* v_replacement_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(v_s_1400_, v_pattern_1401_, v_replacement_1402_);
lean_dec_ref(v_replacement_1402_);
lean_dec_ref(v_pattern_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(lean_object* v_s_1404_, lean_object* v_pattern_1405_, lean_object* v_replacement_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1404_, v_replacement_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___boxed(lean_object* v_s_1408_, lean_object* v_pattern_1409_, lean_object* v_replacement_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(v_s_1408_, v_pattern_1409_, v_replacement_1410_);
lean_dec_ref(v_replacement_1410_);
lean_dec_ref(v_pattern_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(lean_object* v_s_1412_, lean_object* v_pattern_1413_, lean_object* v_replacement_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1412_, v_replacement_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___boxed(lean_object* v_s_1416_, lean_object* v_pattern_1417_, lean_object* v_replacement_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(v_s_1416_, v_pattern_1417_, v_replacement_1418_);
lean_dec_ref(v_replacement_1418_);
lean_dec_ref(v_pattern_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(lean_object* v_s_1420_, lean_object* v_replacement_1421_, lean_object* v_inst_1422_, lean_object* v_R_1423_, lean_object* v_a_1424_, lean_object* v_b_1425_, lean_object* v_c_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1420_, v_replacement_1421_, v_a_1424_, v_b_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___boxed(lean_object* v_s_1428_, lean_object* v_replacement_1429_, lean_object* v_inst_1430_, lean_object* v_R_1431_, lean_object* v_a_1432_, lean_object* v_b_1433_, lean_object* v_c_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(v_s_1428_, v_replacement_1429_, v_inst_1430_, v_R_1431_, v_a_1432_, v_b_1433_, v_c_1434_);
lean_dec_ref(v_replacement_1429_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object* v_s_1436_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1437_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = lean_string_utf8_byte_size(v_s_1436_);
v___x_1440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1440_, 0, v_s_1436_);
lean_ctor_set(v___x_1440_, 1, v___x_1438_);
lean_ctor_set(v___x_1440_, 2, v___x_1439_);
v___x_1441_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1440_, v___x_1437_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object* v_s_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0));
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object* v_s_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v_s_1446_);
lean_dec_ref(v_s_1446_);
return v_res_1447_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1450_ = lean_nat_dec_eq(v___x_1449_, v___x_1448_);
return v___x_1450_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1451_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v___x_1452_);
lean_ctor_set(v___x_1454_, 2, v___x_1451_);
return v___x_1454_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1456_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1455_);
return v___x_1456_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2);
v___x_1459_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1460_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v___x_1458_);
lean_ctor_set(v___x_1460_, 2, v___x_1457_);
lean_ctor_set(v___x_1460_, 3, v___x_1457_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object* v_s_1461_, lean_object* v_replacement_1462_){
_start:
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1464_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3);
v___x_1466_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1461_, v_replacement_1462_, v___x_1465_, v___x_1463_);
return v___x_1466_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1468_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1461_, v_replacement_1462_, v___x_1467_, v___x_1463_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object* v_s_1469_, lean_object* v_replacement_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1469_, v_replacement_1470_);
lean_dec_ref(v_replacement_1470_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object* v_s_1472_, lean_object* v___x_1473_, lean_object* v___x_1474_, lean_object* v_a_1475_, lean_object* v_b_1476_){
_start:
{
lean_object* v_it_1478_; lean_object* v_startInclusive_1479_; lean_object* v_endExclusive_1480_; 
if (lean_obj_tag(v_a_1475_) == 0)
{
lean_object* v_currPos_1488_; lean_object* v_searcher_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1524_; 
v_currPos_1488_ = lean_ctor_get(v_a_1475_, 0);
v_searcher_1489_ = lean_ctor_get(v_a_1475_, 1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_a_1475_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1491_ = v_a_1475_;
v_isShared_1492_ = v_isSharedCheck_1524_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_searcher_1489_);
lean_inc(v_currPos_1488_);
lean_dec(v_a_1475_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1524_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
uint8_t v___y_1504_; lean_object* v_startInclusive_1508_; lean_object* v_endExclusive_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v_startInclusive_1508_ = lean_ctor_get(v___x_1473_, 1);
v_endExclusive_1509_ = lean_ctor_get(v___x_1473_, 2);
v___x_1510_ = lean_nat_sub(v_endExclusive_1509_, v_startInclusive_1508_);
v___x_1511_ = lean_nat_dec_eq(v_searcher_1489_, v___x_1510_);
lean_dec(v___x_1510_);
if (v___x_1511_ == 0)
{
uint32_t v___x_1512_; uint8_t v___y_1514_; uint32_t v___x_1519_; uint8_t v___x_1520_; 
v___x_1512_ = lean_string_utf8_get_fast(v_s_1472_, v_searcher_1489_);
v___x_1519_ = 32;
v___x_1520_ = lean_uint32_dec_eq(v___x_1512_, v___x_1519_);
if (v___x_1520_ == 0)
{
uint32_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = 9;
v___x_1522_ = lean_uint32_dec_eq(v___x_1512_, v___x_1521_);
v___y_1514_ = v___x_1522_;
goto v___jp_1513_;
}
else
{
v___y_1514_ = v___x_1520_;
goto v___jp_1513_;
}
v___jp_1513_:
{
if (v___y_1514_ == 0)
{
uint32_t v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = 13;
v___x_1516_ = lean_uint32_dec_eq(v___x_1512_, v___x_1515_);
if (v___x_1516_ == 0)
{
uint32_t v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = 10;
v___x_1518_ = lean_uint32_dec_eq(v___x_1512_, v___x_1517_);
v___y_1504_ = v___x_1518_;
goto v___jp_1503_;
}
else
{
v___y_1504_ = v___x_1516_;
goto v___jp_1503_;
}
}
else
{
goto v___jp_1493_;
}
}
}
else
{
lean_object* v___x_1523_; 
lean_del_object(v___x_1491_);
lean_dec(v_searcher_1489_);
v___x_1523_ = lean_box(1);
lean_inc(v___x_1474_);
v_it_1478_ = v___x_1523_;
v_startInclusive_1479_ = v_currPos_1488_;
v_endExclusive_1480_ = v___x_1474_;
goto v___jp_1477_;
}
v___jp_1493_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v_slice_1497_; lean_object* v_nextIt_1499_; 
v___x_1494_ = lean_string_utf8_next_fast(v_s_1472_, v_searcher_1489_);
v___x_1495_ = lean_nat_sub(v___x_1494_, v_searcher_1489_);
v___x_1496_ = lean_nat_add(v_searcher_1489_, v___x_1495_);
lean_dec(v___x_1495_);
v_slice_1497_ = l_String_Slice_subslice_x21(v___x_1473_, v_currPos_1488_, v_searcher_1489_);
lean_inc(v___x_1496_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v___x_1496_);
lean_ctor_set(v___x_1491_, 0, v___x_1496_);
v_nextIt_1499_ = v___x_1491_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___x_1496_);
v_nextIt_1499_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v_startInclusive_1500_; lean_object* v_endExclusive_1501_; 
v_startInclusive_1500_ = lean_ctor_get(v_slice_1497_, 0);
lean_inc(v_startInclusive_1500_);
v_endExclusive_1501_ = lean_ctor_get(v_slice_1497_, 1);
lean_inc(v_endExclusive_1501_);
lean_dec_ref(v_slice_1497_);
v_it_1478_ = v_nextIt_1499_;
v_startInclusive_1479_ = v_startInclusive_1500_;
v_endExclusive_1480_ = v_endExclusive_1501_;
goto v___jp_1477_;
}
}
v___jp_1503_:
{
if (v___y_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_del_object(v___x_1491_);
v___x_1505_ = lean_string_utf8_next_fast(v_s_1472_, v_searcher_1489_);
lean_dec(v_searcher_1489_);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v_currPos_1488_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v_a_1475_ = v___x_1506_;
goto _start;
}
else
{
goto v___jp_1493_;
}
}
}
}
else
{
lean_dec(v___x_1474_);
lean_dec_ref(v_s_1472_);
return v_b_1476_;
}
v___jp_1477_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1481_ = lean_nat_sub(v_endExclusive_1480_, v_startInclusive_1479_);
v___x_1482_ = lean_unsigned_to_nat(0u);
v___x_1483_ = lean_nat_dec_eq(v___x_1481_, v___x_1482_);
lean_dec(v___x_1481_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_inc_ref(v_s_1472_);
v___x_1484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1484_, 0, v_s_1472_);
lean_ctor_set(v___x_1484_, 1, v_startInclusive_1479_);
lean_ctor_set(v___x_1484_, 2, v_endExclusive_1480_);
v___x_1485_ = lean_array_push(v_b_1476_, v___x_1484_);
v_a_1475_ = v_it_1478_;
v_b_1476_ = v___x_1485_;
goto _start;
}
else
{
lean_dec(v_endExclusive_1480_);
lean_dec(v_startInclusive_1479_);
v_a_1475_ = v_it_1478_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object* v_s_1525_, lean_object* v___x_1526_, lean_object* v___x_1527_, lean_object* v_a_1528_, lean_object* v_b_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1525_, v___x_1526_, v___x_1527_, v_a_1528_, v_b_1529_);
lean_dec_ref(v___x_1526_);
return v_res_1530_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1532_ = lean_string_utf8_byte_size(v___x_1531_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1533_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0);
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v___x_1534_);
lean_ctor_set(v___x_1536_, 2, v___x_1533_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t v_mode_1539_, lean_object* v_s_1540_){
_start:
{
switch(v_mode_1539_)
{
case 0:
{
return v_s_1540_;
}
case 1:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1541_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1542_ = lean_unsigned_to_nat(0u);
v___x_1543_ = lean_string_utf8_byte_size(v_s_1540_);
v___x_1544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1544_, 0, v_s_1540_);
lean_ctor_set(v___x_1544_, 1, v___x_1542_);
lean_ctor_set(v___x_1544_, 2, v___x_1543_);
v___x_1545_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v___x_1544_, v___x_1541_);
return v___x_1545_;
}
default: 
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1);
v___x_1548_ = lean_string_utf8_byte_size(v_s_1540_);
lean_inc_ref(v_s_1540_);
v___x_1549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1549_, 0, v_s_1540_);
lean_ctor_set(v___x_1549_, 1, v___x_1546_);
lean_ctor_set(v___x_1549_, 2, v___x_1548_);
v___x_1550_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v___x_1549_);
v___x_1551_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__2));
v___x_1552_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1540_, v___x_1549_, v___x_1548_, v___x_1550_, v___x_1551_);
lean_dec_ref_known(v___x_1549_, 3);
v___x_1553_ = lean_array_to_list(v___x_1552_);
v___x_1554_ = l_String_Slice_intercalate(v___x_1547_, v___x_1553_);
lean_dec(v___x_1553_);
return v___x_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object* v_mode_1555_, lean_object* v_s_1556_){
_start:
{
uint8_t v_mode_boxed_1557_; lean_object* v_res_1558_; 
v_mode_boxed_1557_ = lean_unbox(v_mode_1555_);
v_res_1558_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v_mode_boxed_1557_, v_s_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object* v_s_1559_, lean_object* v_pattern_1560_, lean_object* v_replacement_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1559_, v_replacement_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object* v_s_1563_, lean_object* v_pattern_1564_, lean_object* v_replacement_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(v_s_1563_, v_pattern_1564_, v_replacement_1565_);
lean_dec_ref(v_replacement_1565_);
lean_dec_ref(v_pattern_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object* v_s_1567_, lean_object* v___x_1568_, lean_object* v___x_1569_, lean_object* v_inst_1570_, lean_object* v_R_1571_, lean_object* v_a_1572_, lean_object* v_b_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1567_, v___x_1568_, v___x_1569_, v_a_1572_, v_b_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___boxed(lean_object* v_s_1575_, lean_object* v___x_1576_, lean_object* v___x_1577_, lean_object* v_inst_1578_, lean_object* v_R_1579_, lean_object* v_a_1580_, lean_object* v_b_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(v_s_1575_, v___x_1576_, v___x_1577_, v_inst_1578_, v_R_1579_, v_a_1580_, v_b_1581_);
lean_dec_ref(v___x_1576_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(lean_object* v_hi_1583_, lean_object* v_pivot_1584_, lean_object* v_as_1585_, lean_object* v_i_1586_, lean_object* v_k_1587_){
_start:
{
uint8_t v___x_1588_; 
v___x_1588_ = lean_nat_dec_lt(v_k_1587_, v_hi_1583_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v_k_1587_);
v___x_1589_ = lean_array_fswap(v_as_1585_, v_i_1586_, v_hi_1583_);
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_i_1586_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
return v___x_1590_;
}
else
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_array_fget_borrowed(v_as_1585_, v_k_1587_);
v___x_1592_ = lean_string_dec_lt(v___x_1591_, v_pivot_1584_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_add(v_k_1587_, v___x_1593_);
lean_dec(v_k_1587_);
v_k_1587_ = v___x_1594_;
goto _start;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1596_ = lean_array_fswap(v_as_1585_, v_i_1586_, v_k_1587_);
v___x_1597_ = lean_unsigned_to_nat(1u);
v___x_1598_ = lean_nat_add(v_i_1586_, v___x_1597_);
lean_dec(v_i_1586_);
v___x_1599_ = lean_nat_add(v_k_1587_, v___x_1597_);
lean_dec(v_k_1587_);
v_as_1585_ = v___x_1596_;
v_i_1586_ = v___x_1598_;
v_k_1587_ = v___x_1599_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg___boxed(lean_object* v_hi_1601_, lean_object* v_pivot_1602_, lean_object* v_as_1603_, lean_object* v_i_1604_, lean_object* v_k_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1601_, v_pivot_1602_, v_as_1603_, v_i_1604_, v_k_1605_);
lean_dec_ref(v_pivot_1602_);
lean_dec(v_hi_1601_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object* v_n_1607_, lean_object* v_as_1608_, lean_object* v_lo_1609_, lean_object* v_hi_1610_){
_start:
{
lean_object* v___y_1612_; uint8_t v___x_1622_; 
v___x_1622_ = lean_nat_dec_lt(v_lo_1609_, v_hi_1610_);
if (v___x_1622_ == 0)
{
lean_dec(v_lo_1609_);
return v_as_1608_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v_mid_1625_; lean_object* v___y_1627_; lean_object* v___y_1633_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1623_ = lean_nat_add(v_lo_1609_, v_hi_1610_);
v___x_1624_ = lean_unsigned_to_nat(1u);
v_mid_1625_ = lean_nat_shiftr(v___x_1623_, v___x_1624_);
lean_dec(v___x_1623_);
v___x_1638_ = lean_array_fget_borrowed(v_as_1608_, v_mid_1625_);
v___x_1639_ = lean_array_fget_borrowed(v_as_1608_, v_lo_1609_);
v___x_1640_ = lean_string_dec_lt(v___x_1638_, v___x_1639_);
if (v___x_1640_ == 0)
{
v___y_1633_ = v_as_1608_;
goto v___jp_1632_;
}
else
{
lean_object* v___x_1641_; 
v___x_1641_ = lean_array_fswap(v_as_1608_, v_lo_1609_, v_mid_1625_);
v___y_1633_ = v___x_1641_;
goto v___jp_1632_;
}
v___jp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1628_ = lean_array_fget_borrowed(v___y_1627_, v_mid_1625_);
v___x_1629_ = lean_array_fget_borrowed(v___y_1627_, v_hi_1610_);
v___x_1630_ = lean_string_dec_lt(v___x_1628_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_dec(v_mid_1625_);
v___y_1612_ = v___y_1627_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_array_fswap(v___y_1627_, v_mid_1625_, v_hi_1610_);
lean_dec(v_mid_1625_);
v___y_1612_ = v___x_1631_;
goto v___jp_1611_;
}
}
v___jp_1632_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = lean_array_fget_borrowed(v___y_1633_, v_hi_1610_);
v___x_1635_ = lean_array_fget_borrowed(v___y_1633_, v_lo_1609_);
v___x_1636_ = lean_string_dec_lt(v___x_1634_, v___x_1635_);
if (v___x_1636_ == 0)
{
v___y_1627_ = v___y_1633_;
goto v___jp_1626_;
}
else
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_array_fswap(v___y_1633_, v_lo_1609_, v_hi_1610_);
v___y_1627_ = v___x_1637_;
goto v___jp_1626_;
}
}
}
v___jp_1611_:
{
lean_object* v_pivot_1613_; lean_object* v___x_1614_; lean_object* v_fst_1615_; lean_object* v_snd_1616_; uint8_t v___x_1617_; 
v_pivot_1613_ = lean_array_fget(v___y_1612_, v_hi_1610_);
lean_inc_n(v_lo_1609_, 2);
v___x_1614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1610_, v_pivot_1613_, v___y_1612_, v_lo_1609_, v_lo_1609_);
lean_dec(v_pivot_1613_);
v_fst_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_fst_1615_);
v_snd_1616_ = lean_ctor_get(v___x_1614_, 1);
lean_inc(v_snd_1616_);
lean_dec_ref(v___x_1614_);
v___x_1617_ = lean_nat_dec_le(v_hi_1610_, v_fst_1615_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1607_, v_snd_1616_, v_lo_1609_, v_fst_1615_);
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_nat_add(v_fst_1615_, v___x_1619_);
lean_dec(v_fst_1615_);
v_as_1608_ = v___x_1618_;
v_lo_1609_ = v___x_1620_;
goto _start;
}
else
{
lean_dec(v_fst_1615_);
lean_dec(v_lo_1609_);
return v_snd_1616_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object* v_n_1642_, lean_object* v_as_1643_, lean_object* v_lo_1644_, lean_object* v_hi_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1642_, v_as_1643_, v_lo_1644_, v_hi_1645_);
lean_dec(v_hi_1645_);
lean_dec(v_n_1642_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t v_mode_1647_, lean_object* v_msgs_1648_){
_start:
{
if (v_mode_1647_ == 0)
{
return v_msgs_1648_;
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1649_ = lean_array_mk(v_msgs_1648_);
v___x_1650_ = lean_array_get_size(v___x_1649_);
v___x_1656_ = lean_unsigned_to_nat(0u);
v___x_1657_ = lean_nat_dec_eq(v___x_1650_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___y_1661_; uint8_t v___x_1663_; 
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = lean_nat_sub(v___x_1650_, v___x_1658_);
v___x_1663_ = lean_nat_dec_le(v___x_1656_, v___x_1659_);
if (v___x_1663_ == 0)
{
lean_inc(v___x_1659_);
v___y_1661_ = v___x_1659_;
goto v___jp_1660_;
}
else
{
v___y_1661_ = v___x_1656_;
goto v___jp_1660_;
}
v___jp_1660_:
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_nat_dec_le(v___y_1661_, v___x_1659_);
if (v___x_1662_ == 0)
{
lean_dec(v___x_1659_);
lean_inc(v___y_1661_);
v___y_1652_ = v___y_1661_;
v___y_1653_ = v___y_1661_;
goto v___jp_1651_;
}
else
{
v___y_1652_ = v___y_1661_;
v___y_1653_ = v___x_1659_;
goto v___jp_1651_;
}
}
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_array_to_list(v___x_1649_);
return v___x_1664_;
}
v___jp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v___x_1650_, v___x_1649_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
v___x_1655_ = lean_array_to_list(v___x_1654_);
return v___x_1655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* v_mode_1665_, lean_object* v_msgs_1666_){
_start:
{
uint8_t v_mode_boxed_1667_; lean_object* v_res_1668_; 
v_mode_boxed_1667_ = lean_unbox(v_mode_1665_);
v_res_1668_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_boxed_1667_, v_msgs_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object* v_n_1669_, lean_object* v_as_1670_, lean_object* v_lo_1671_, lean_object* v_hi_1672_, lean_object* v_w_1673_, lean_object* v_hlo_1674_, lean_object* v_hhi_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1669_, v_as_1670_, v_lo_1671_, v_hi_1672_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object* v_n_1677_, lean_object* v_as_1678_, lean_object* v_lo_1679_, lean_object* v_hi_1680_, lean_object* v_w_1681_, lean_object* v_hlo_1682_, lean_object* v_hhi_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(v_n_1677_, v_as_1678_, v_lo_1679_, v_hi_1680_, v_w_1681_, v_hlo_1682_, v_hhi_1683_);
lean_dec(v_hi_1680_);
lean_dec(v_n_1677_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(lean_object* v_n_1685_, lean_object* v_lo_1686_, lean_object* v_hi_1687_, lean_object* v_hhi_1688_, lean_object* v_pivot_1689_, lean_object* v_as_1690_, lean_object* v_i_1691_, lean_object* v_k_1692_, lean_object* v_ilo_1693_, lean_object* v_ik_1694_, lean_object* v_w_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1687_, v_pivot_1689_, v_as_1690_, v_i_1691_, v_k_1692_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___boxed(lean_object* v_n_1697_, lean_object* v_lo_1698_, lean_object* v_hi_1699_, lean_object* v_hhi_1700_, lean_object* v_pivot_1701_, lean_object* v_as_1702_, lean_object* v_i_1703_, lean_object* v_k_1704_, lean_object* v_ilo_1705_, lean_object* v_ik_1706_, lean_object* v_w_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(v_n_1697_, v_lo_1698_, v_hi_1699_, v_hhi_1700_, v_pivot_1701_, v_as_1702_, v_i_1703_, v_k_1704_, v_ilo_1705_, v_ik_1706_, v_w_1707_);
lean_dec_ref(v_pivot_1701_);
lean_dec(v_hi_1699_);
lean_dec(v_lo_1698_);
lean_dec(v_n_1697_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object* v_as_1709_, size_t v_i_1710_, size_t v_stop_1711_, lean_object* v_b_1712_){
_start:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_usize_dec_eq(v_i_1710_, v_stop_1711_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v_diagnostics_1715_; lean_object* v_msgLog_1716_; lean_object* v___x_1717_; size_t v___x_1718_; size_t v___x_1719_; 
v___x_1714_ = lean_array_uget_borrowed(v_as_1709_, v_i_1710_);
v_diagnostics_1715_ = lean_ctor_get(v___x_1714_, 1);
v_msgLog_1716_ = lean_ctor_get(v_diagnostics_1715_, 0);
lean_inc_ref(v_msgLog_1716_);
v___x_1717_ = l_Lean_MessageLog_append(v_b_1712_, v_msgLog_1716_);
v___x_1718_ = ((size_t)1ULL);
v___x_1719_ = lean_usize_add(v_i_1710_, v___x_1718_);
v_i_1710_ = v___x_1719_;
v_b_1712_ = v___x_1717_;
goto _start;
}
else
{
return v_b_1712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0___boxed(lean_object* v_as_1721_, lean_object* v_i_1722_, lean_object* v_stop_1723_, lean_object* v_b_1724_){
_start:
{
size_t v_i_boxed_1725_; size_t v_stop_boxed_1726_; lean_object* v_res_1727_; 
v_i_boxed_1725_ = lean_unbox_usize(v_i_1722_);
lean_dec(v_i_1722_);
v_stop_boxed_1726_ = lean_unbox_usize(v_stop_1723_);
lean_dec(v_stop_1723_);
v_res_1727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v_as_1721_, v_i_boxed_1725_, v_stop_boxed_1726_, v_b_1724_);
lean_dec_ref(v_as_1721_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object* v_as_1728_, size_t v_i_1729_, size_t v_stop_1730_, lean_object* v_b_1731_){
_start:
{
lean_object* v___y_1733_; uint8_t v___x_1737_; 
v___x_1737_ = lean_usize_dec_eq(v_i_1729_, v_stop_1730_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1738_ = lean_array_uget_borrowed(v_as_1728_, v_i_1729_);
v___x_1739_ = l_Lean_MessageLog_empty;
lean_inc(v___x_1738_);
v___x_1740_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1738_);
v___x_1741_ = l_Lean_Language_SnapshotTree_getAll(v___x_1740_);
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = lean_array_get_size(v___x_1741_);
v___x_1744_ = lean_nat_dec_lt(v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref(v___x_1741_);
v___x_1745_ = l_Lean_MessageLog_append(v_b_1731_, v___x_1739_);
v___y_1733_ = v___x_1745_;
goto v___jp_1732_;
}
else
{
uint8_t v___x_1746_; 
v___x_1746_ = lean_nat_dec_le(v___x_1743_, v___x_1743_);
if (v___x_1746_ == 0)
{
if (v___x_1744_ == 0)
{
lean_object* v___x_1747_; 
lean_dec_ref(v___x_1741_);
v___x_1747_ = l_Lean_MessageLog_append(v_b_1731_, v___x_1739_);
v___y_1733_ = v___x_1747_;
goto v___jp_1732_;
}
else
{
size_t v___x_1748_; size_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1748_ = ((size_t)0ULL);
v___x_1749_ = lean_usize_of_nat(v___x_1743_);
v___x_1750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1741_, v___x_1748_, v___x_1749_, v___x_1739_);
lean_dec_ref(v___x_1741_);
v___x_1751_ = l_Lean_MessageLog_append(v_b_1731_, v___x_1750_);
v___y_1733_ = v___x_1751_;
goto v___jp_1732_;
}
}
else
{
size_t v___x_1752_; size_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = lean_usize_of_nat(v___x_1743_);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1741_, v___x_1752_, v___x_1753_, v___x_1739_);
lean_dec_ref(v___x_1741_);
v___x_1755_ = l_Lean_MessageLog_append(v_b_1731_, v___x_1754_);
v___y_1733_ = v___x_1755_;
goto v___jp_1732_;
}
}
}
else
{
return v_b_1731_;
}
v___jp_1732_:
{
size_t v___x_1734_; size_t v___x_1735_; 
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_add(v_i_1729_, v___x_1734_);
v_i_1729_ = v___x_1735_;
v_b_1731_ = v___y_1733_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1___boxed(lean_object* v_as_1756_, lean_object* v_i_1757_, lean_object* v_stop_1758_, lean_object* v_b_1759_){
_start:
{
size_t v_i_boxed_1760_; size_t v_stop_boxed_1761_; lean_object* v_res_1762_; 
v_i_boxed_1760_ = lean_unbox_usize(v_i_1757_);
lean_dec(v_i_1757_);
v_stop_boxed_1761_ = lean_unbox_usize(v_stop_1758_);
lean_dec(v_stop_1758_);
v_res_1762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_as_1756_, v_i_boxed_1760_, v_stop_boxed_1761_, v_b_1759_);
lean_dec_ref(v_as_1756_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object* v_cmd_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_fileName_1769_; lean_object* v_fileMap_1770_; lean_object* v_currRecDepth_1771_; lean_object* v_cmdPos_1772_; lean_object* v_macroStack_1773_; lean_object* v_quotContext_x3f_1774_; lean_object* v_currMacroScope_1775_; lean_object* v_ref_1776_; lean_object* v_cancelTk_x3f_1777_; uint8_t v_suppressElabErrors_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_fileName_1769_ = lean_ctor_get(v_a_1766_, 0);
v_fileMap_1770_ = lean_ctor_get(v_a_1766_, 1);
v_currRecDepth_1771_ = lean_ctor_get(v_a_1766_, 2);
v_cmdPos_1772_ = lean_ctor_get(v_a_1766_, 3);
v_macroStack_1773_ = lean_ctor_get(v_a_1766_, 4);
v_quotContext_x3f_1774_ = lean_ctor_get(v_a_1766_, 5);
v_currMacroScope_1775_ = lean_ctor_get(v_a_1766_, 6);
v_ref_1776_ = lean_ctor_get(v_a_1766_, 7);
v_cancelTk_x3f_1777_ = lean_ctor_get(v_a_1766_, 9);
v_suppressElabErrors_1778_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*10);
v___x_1779_ = lean_unsigned_to_nat(0u);
v___x_1780_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
v___x_1781_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1777_);
lean_inc(v_ref_1776_);
lean_inc(v_currMacroScope_1775_);
lean_inc(v_quotContext_x3f_1774_);
lean_inc(v_macroStack_1773_);
lean_inc(v_cmdPos_1772_);
lean_inc(v_currRecDepth_1771_);
lean_inc_ref(v_fileMap_1770_);
lean_inc_ref(v_fileName_1769_);
v___x_1782_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1782_, 0, v_fileName_1769_);
lean_ctor_set(v___x_1782_, 1, v_fileMap_1770_);
lean_ctor_set(v___x_1782_, 2, v_currRecDepth_1771_);
lean_ctor_set(v___x_1782_, 3, v_cmdPos_1772_);
lean_ctor_set(v___x_1782_, 4, v_macroStack_1773_);
lean_ctor_set(v___x_1782_, 5, v_quotContext_x3f_1774_);
lean_ctor_set(v___x_1782_, 6, v_currMacroScope_1775_);
lean_ctor_set(v___x_1782_, 7, v_ref_1776_);
lean_ctor_set(v___x_1782_, 8, v___x_1781_);
lean_ctor_set(v___x_1782_, 9, v_cancelTk_x3f_1777_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*10, v_suppressElabErrors_1778_);
v___x_1783_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1765_, v___x_1780_, v___x_1782_, v_a_1767_);
lean_dec_ref_known(v___x_1782_, 10);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1828_; 
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v___x_1783_, 0);
lean_dec(v_unused_1829_);
v___x_1785_ = v___x_1783_;
v_isShared_1786_ = v_isSharedCheck_1828_;
goto v_resetjp_1784_;
}
else
{
lean_dec(v___x_1783_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1828_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v_messages_1789_; lean_object* v___y_1791_; lean_object* v_snapshotTasks_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1787_ = lean_st_ref_get(v_a_1767_);
v___x_1788_ = lean_st_ref_get(v_a_1767_);
v_messages_1789_ = lean_ctor_get(v___x_1787_, 1);
lean_inc_ref(v_messages_1789_);
lean_dec(v___x_1787_);
v_snapshotTasks_1817_ = lean_ctor_get(v___x_1788_, 10);
lean_inc_ref(v_snapshotTasks_1817_);
lean_dec(v___x_1788_);
v___x_1818_ = l_Lean_MessageLog_empty;
v___x_1819_ = lean_array_get_size(v_snapshotTasks_1817_);
v___x_1820_ = lean_nat_dec_lt(v___x_1779_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_dec_ref(v_snapshotTasks_1817_);
v___y_1791_ = v___x_1818_;
goto v___jp_1790_;
}
else
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_nat_dec_le(v___x_1819_, v___x_1819_);
if (v___x_1821_ == 0)
{
if (v___x_1820_ == 0)
{
lean_dec_ref(v_snapshotTasks_1817_);
v___y_1791_ = v___x_1818_;
goto v___jp_1790_;
}
else
{
size_t v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = ((size_t)0ULL);
v___x_1823_ = lean_usize_of_nat(v___x_1819_);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1817_, v___x_1822_, v___x_1823_, v___x_1818_);
lean_dec_ref(v_snapshotTasks_1817_);
v___y_1791_ = v___x_1824_;
goto v___jp_1790_;
}
}
else
{
size_t v___x_1825_; size_t v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = ((size_t)0ULL);
v___x_1826_ = lean_usize_of_nat(v___x_1819_);
v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1817_, v___x_1825_, v___x_1826_, v___x_1818_);
lean_dec_ref(v_snapshotTasks_1817_);
v___y_1791_ = v___x_1827_;
goto v___jp_1790_;
}
}
v___jp_1790_:
{
lean_object* v___x_1792_; lean_object* v_env_1793_; lean_object* v_messages_1794_; lean_object* v_scopes_1795_; lean_object* v_usedQuotCtxts_1796_; lean_object* v_nextMacroScope_1797_; lean_object* v_maxRecDepth_1798_; lean_object* v_ngen_1799_; lean_object* v_auxDeclNGen_1800_; lean_object* v_infoState_1801_; lean_object* v_traceState_1802_; lean_object* v_prevLinterStates_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1815_; 
v___x_1792_ = lean_st_ref_take(v_a_1767_);
v_env_1793_ = lean_ctor_get(v___x_1792_, 0);
v_messages_1794_ = lean_ctor_get(v___x_1792_, 1);
v_scopes_1795_ = lean_ctor_get(v___x_1792_, 2);
v_usedQuotCtxts_1796_ = lean_ctor_get(v___x_1792_, 3);
v_nextMacroScope_1797_ = lean_ctor_get(v___x_1792_, 4);
v_maxRecDepth_1798_ = lean_ctor_get(v___x_1792_, 5);
v_ngen_1799_ = lean_ctor_get(v___x_1792_, 6);
v_auxDeclNGen_1800_ = lean_ctor_get(v___x_1792_, 7);
v_infoState_1801_ = lean_ctor_get(v___x_1792_, 8);
v_traceState_1802_ = lean_ctor_get(v___x_1792_, 9);
v_prevLinterStates_1803_ = lean_ctor_get(v___x_1792_, 11);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v___x_1792_, 10);
lean_dec(v_unused_1816_);
v___x_1805_ = v___x_1792_;
v_isShared_1806_ = v_isSharedCheck_1815_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_prevLinterStates_1803_);
lean_inc(v_traceState_1802_);
lean_inc(v_infoState_1801_);
lean_inc(v_auxDeclNGen_1800_);
lean_inc(v_ngen_1799_);
lean_inc(v_maxRecDepth_1798_);
lean_inc(v_nextMacroScope_1797_);
lean_inc(v_usedQuotCtxts_1796_);
lean_inc(v_scopes_1795_);
lean_inc(v_messages_1794_);
lean_inc(v_env_1793_);
lean_dec(v___x_1792_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1815_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 10, v___x_1780_);
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_env_1793_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_messages_1794_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_scopes_1795_);
lean_ctor_set(v_reuseFailAlloc_1814_, 3, v_usedQuotCtxts_1796_);
lean_ctor_set(v_reuseFailAlloc_1814_, 4, v_nextMacroScope_1797_);
lean_ctor_set(v_reuseFailAlloc_1814_, 5, v_maxRecDepth_1798_);
lean_ctor_set(v_reuseFailAlloc_1814_, 6, v_ngen_1799_);
lean_ctor_set(v_reuseFailAlloc_1814_, 7, v_auxDeclNGen_1800_);
lean_ctor_set(v_reuseFailAlloc_1814_, 8, v_infoState_1801_);
lean_ctor_set(v_reuseFailAlloc_1814_, 9, v_traceState_1802_);
lean_ctor_set(v_reuseFailAlloc_1814_, 10, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1814_, 11, v_prevLinterStates_1803_);
v___x_1808_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1809_ = lean_st_ref_set(v_a_1767_, v___x_1808_);
v___x_1810_ = l_Lean_MessageLog_append(v_messages_1789_, v___y_1791_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1810_);
v___x_1812_ = v___x_1785_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
v_a_1830_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1783_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1783_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1838_, v_a_1839_, v_a_1840_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
return v_res_1842_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1843_, lean_object* v_opt_1844_){
_start:
{
lean_object* v_name_1845_; lean_object* v_defValue_1846_; lean_object* v_map_1847_; lean_object* v___x_1848_; 
v_name_1845_ = lean_ctor_get(v_opt_1844_, 0);
v_defValue_1846_ = lean_ctor_get(v_opt_1844_, 1);
v_map_1847_ = lean_ctor_get(v_opts_1843_, 0);
v___x_1848_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1847_, v_name_1845_);
if (lean_obj_tag(v___x_1848_) == 0)
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_unbox(v_defValue_1846_);
return v___x_1849_;
}
else
{
lean_object* v_val_1850_; 
v_val_1850_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_val_1850_);
lean_dec_ref_known(v___x_1848_, 1);
if (lean_obj_tag(v_val_1850_) == 1)
{
uint8_t v_v_1851_; 
v_v_1851_ = lean_ctor_get_uint8(v_val_1850_, 0);
lean_dec_ref_known(v_val_1850_, 0);
return v_v_1851_;
}
else
{
uint8_t v___x_1852_; 
lean_dec(v_val_1850_);
v___x_1852_ = lean_unbox(v_defValue_1846_);
return v___x_1852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1853_, lean_object* v_opt_1854_){
_start:
{
uint8_t v_res_1855_; lean_object* v_r_1856_; 
v_res_1855_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1853_, v_opt_1854_);
lean_dec_ref(v_opt_1854_);
lean_dec_ref(v_opts_1853_);
v_r_1856_ = lean_box(v_res_1855_);
return v_r_1856_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0));
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
lean_object* v___x_1905_; lean_object* v_scopes_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v_opts_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1905_ = lean_st_ref_get(v___y_1903_);
v_scopes_1906_ = lean_ctor_get(v___x_1905_, 2);
lean_inc(v_scopes_1906_);
lean_dec(v___x_1905_);
v___x_1907_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1908_ = l_List_head_x21___redArg(v___x_1907_, v_scopes_1906_);
lean_dec(v_scopes_1906_);
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
v___x_1937_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
v___x_1942_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_1959_; lean_object* v_env_1960_; lean_object* v___x_1961_; lean_object* v_scopes_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v_opts_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1959_ = lean_st_ref_get(v___y_1957_);
v_env_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc_ref(v_env_1960_);
lean_dec(v___x_1959_);
v___x_1961_ = lean_st_ref_get(v___y_1957_);
v_scopes_1962_ = lean_ctor_get(v___x_1961_, 2);
lean_inc(v_scopes_1962_);
lean_dec(v___x_1961_);
v___x_1963_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1964_ = l_List_head_x21___redArg(v___x_1963_, v_scopes_1962_);
lean_dec(v_scopes_1962_);
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
lean_object* v_a_1980_; lean_object* v_macroStack_1981_; lean_object* v___x_1982_; lean_object* v_a_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1994_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v_macroStack_1981_ = lean_ctor_get(v___y_1976_, 4);
v___x_1982_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1975_, v___y_1977_);
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref(v___x_1982_);
v___x_1984_ = l_Lean_Elab_getBetterRef(v_a_1980_, v_macroStack_1981_);
lean_dec(v_a_1980_);
lean_inc(v_macroStack_1981_);
v___x_1985_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1983_, v_macroStack_1981_, v___y_1977_);
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
lean_ctor_set(v___x_1990_, 0, v___x_1984_);
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
lean_dec(v_pre_2072_);
lean_dec_ref_known(v_pre_2071_, 2);
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
uint8_t v___x_2191_; 
lean_dec_ref_known(v_a_2188_, 1);
v___x_2191_ = 1;
return v___x_2191_;
}
case 1:
{
lean_object* v_pos_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2205_; 
v_pos_2192_ = lean_ctor_get(v_a_2188_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_a_2188_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2194_ = v_a_2188_;
v_isShared_2195_ = v_isSharedCheck_2205_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_pos_2192_);
lean_dec(v_a_2188_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2205_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_str_2196_; lean_object* v_startInclusive_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
v_str_2196_ = lean_ctor_get(v_s_2187_, 0);
v_startInclusive_2197_ = lean_ctor_get(v_s_2187_, 1);
v___x_2198_ = lean_nat_add(v_startInclusive_2197_, v_pos_2192_);
lean_dec(v_pos_2192_);
v___x_2199_ = lean_string_utf8_next_fast(v_str_2196_, v___x_2198_);
lean_dec(v___x_2198_);
v___x_2200_ = lean_nat_sub(v___x_2199_, v_startInclusive_2197_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set_tag(v___x_2194_, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2200_);
v___x_2202_ = v___x_2194_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
v_a_2188_ = v___x_2202_;
v_b_2189_ = v___x_2190_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2206_; lean_object* v_table_2207_; lean_object* v_stackPos_2208_; lean_object* v_needlePos_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2262_; 
v_needle_2206_ = lean_ctor_get(v_a_2188_, 0);
v_table_2207_ = lean_ctor_get(v_a_2188_, 1);
v_stackPos_2208_ = lean_ctor_get(v_a_2188_, 2);
v_needlePos_2209_ = lean_ctor_get(v_a_2188_, 3);
v_isSharedCheck_2262_ = !lean_is_exclusive(v_a_2188_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2211_ = v_a_2188_;
v_isShared_2212_ = v_isSharedCheck_2262_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_needlePos_2209_);
lean_inc(v_stackPos_2208_);
lean_inc(v_table_2207_);
lean_inc(v_needle_2206_);
lean_dec(v_a_2188_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2262_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v_str_2213_; lean_object* v_startInclusive_2214_; lean_object* v_endExclusive_2215_; lean_object* v_str_2216_; lean_object* v_startInclusive_2217_; lean_object* v_endExclusive_2218_; lean_object* v_basePos_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v_str_2213_ = lean_ctor_get(v_needle_2206_, 0);
v_startInclusive_2214_ = lean_ctor_get(v_needle_2206_, 1);
v_endExclusive_2215_ = lean_ctor_get(v_needle_2206_, 2);
v_str_2216_ = lean_ctor_get(v_s_2187_, 0);
v_startInclusive_2217_ = lean_ctor_get(v_s_2187_, 1);
v_endExclusive_2218_ = lean_ctor_get(v_s_2187_, 2);
v_basePos_2219_ = lean_nat_sub(v_stackPos_2208_, v_needlePos_2209_);
v___x_2220_ = lean_nat_sub(v_endExclusive_2215_, v_startInclusive_2214_);
v___x_2221_ = lean_nat_add(v_basePos_2219_, v___x_2220_);
v___x_2222_ = lean_nat_sub(v_endExclusive_2218_, v_startInclusive_2217_);
v___x_2223_ = lean_nat_dec_le(v___x_2221_, v___x_2222_);
lean_dec(v___x_2221_);
if (v___x_2223_ == 0)
{
uint8_t v___x_2224_; 
lean_dec(v___x_2220_);
lean_del_object(v___x_2211_);
lean_dec(v_needlePos_2209_);
lean_dec(v_stackPos_2208_);
lean_dec_ref(v_table_2207_);
lean_dec_ref(v_needle_2206_);
v___x_2224_ = lean_nat_dec_lt(v_basePos_2219_, v___x_2222_);
lean_dec(v___x_2222_);
lean_dec(v_basePos_2219_);
if (v___x_2224_ == 0)
{
return v_b_2189_;
}
else
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_box(3);
v_a_2188_ = v___x_2225_;
v_b_2189_ = v___x_2190_;
goto _start;
}
}
else
{
lean_object* v___x_2227_; uint8_t v_stackByte_2228_; lean_object* v___x_2229_; uint8_t v_patByte_2230_; uint8_t v___x_2231_; 
lean_dec(v___x_2222_);
lean_dec(v_basePos_2219_);
v___x_2227_ = lean_nat_add(v_startInclusive_2217_, v_stackPos_2208_);
v_stackByte_2228_ = lean_string_get_byte_fast(v_str_2216_, v___x_2227_);
v___x_2229_ = lean_nat_add(v_startInclusive_2214_, v_needlePos_2209_);
v_patByte_2230_ = lean_string_get_byte_fast(v_str_2213_, v___x_2229_);
v___x_2231_ = lean_uint8_dec_eq(v_stackByte_2228_, v_patByte_2230_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; uint8_t v___x_2233_; 
lean_dec(v___x_2220_);
v___x_2232_ = lean_unsigned_to_nat(0u);
v___x_2233_ = lean_nat_dec_eq(v_needlePos_2209_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v_newNeedlePos_2236_; uint8_t v___x_2237_; 
v___x_2234_ = lean_unsigned_to_nat(1u);
v___x_2235_ = lean_nat_sub(v_needlePos_2209_, v___x_2234_);
lean_dec(v_needlePos_2209_);
v_newNeedlePos_2236_ = lean_array_fget_borrowed(v_table_2207_, v___x_2235_);
lean_dec(v___x_2235_);
v___x_2237_ = lean_nat_dec_eq(v_newNeedlePos_2236_, v___x_2232_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2239_; 
lean_inc(v_newNeedlePos_2236_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 3, v_newNeedlePos_2236_);
v___x_2239_ = v___x_2211_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_needle_2206_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_table_2207_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_stackPos_2208_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_newNeedlePos_2236_);
v___x_2239_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
v_a_2188_ = v___x_2239_;
v_b_2189_ = v___x_2190_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2242_; lean_object* v___x_2244_; 
v_nextStackPos_2242_ = l_String_Slice_posGE___redArg(v_s_2187_, v_stackPos_2208_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 3, v___x_2232_);
lean_ctor_set(v___x_2211_, 2, v_nextStackPos_2242_);
v___x_2244_ = v___x_2211_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_needle_2206_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_table_2207_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_nextStackPos_2242_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v___x_2232_);
v___x_2244_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
v_a_2188_ = v___x_2244_;
v_b_2189_ = v___x_2190_;
goto _start;
}
}
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_nextStackPos_2249_; lean_object* v___x_2251_; 
lean_dec(v_needlePos_2209_);
v___x_2247_ = lean_unsigned_to_nat(1u);
v___x_2248_ = lean_nat_add(v_stackPos_2208_, v___x_2247_);
lean_dec(v_stackPos_2208_);
v_nextStackPos_2249_ = l_String_Slice_posGE___redArg(v_s_2187_, v___x_2248_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 3, v___x_2232_);
lean_ctor_set(v___x_2211_, 2, v_nextStackPos_2249_);
v___x_2251_ = v___x_2211_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_needle_2206_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_table_2207_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_nextStackPos_2249_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v___x_2232_);
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
lean_object* v___x_2254_; lean_object* v_nextNeedlePos_2255_; uint8_t v___x_2256_; 
v___x_2254_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2255_ = lean_nat_add(v_needlePos_2209_, v___x_2254_);
lean_dec(v_needlePos_2209_);
v___x_2256_ = lean_nat_dec_eq(v_nextNeedlePos_2255_, v___x_2220_);
lean_dec(v___x_2220_);
if (v___x_2256_ == 0)
{
lean_object* v_nextStackPos_2257_; lean_object* v___x_2259_; 
v_nextStackPos_2257_ = lean_nat_add(v_stackPos_2208_, v___x_2254_);
lean_dec(v_stackPos_2208_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 3, v_nextNeedlePos_2255_);
lean_ctor_set(v___x_2211_, 2, v_nextStackPos_2257_);
v___x_2259_ = v___x_2211_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_needle_2206_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_table_2207_);
lean_ctor_set(v_reuseFailAlloc_2261_, 2, v_nextStackPos_2257_);
lean_ctor_set(v_reuseFailAlloc_2261_, 3, v_nextNeedlePos_2255_);
v___x_2259_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
v_a_2188_ = v___x_2259_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2255_);
lean_del_object(v___x_2211_);
lean_dec(v_stackPos_2208_);
lean_dec_ref(v_table_2207_);
lean_dec_ref(v_needle_2206_);
return v___x_2256_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2263_, lean_object* v_a_2264_, lean_object* v_b_2265_){
_start:
{
uint8_t v_b_boxed_2266_; uint8_t v_res_2267_; lean_object* v_r_2268_; 
v_b_boxed_2266_ = lean_unbox(v_b_2265_);
v_res_2267_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2263_, v_a_2264_, v_b_boxed_2266_);
lean_dec_ref(v_s_2263_);
v_r_2268_ = lean_box(v_res_2267_);
return v_r_2268_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2269_, lean_object* v_s_2270_){
_start:
{
lean_object* v___y_2272_; lean_object* v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2275_ = lean_unsigned_to_nat(0u);
v___x_2276_ = lean_string_utf8_byte_size(v___x_2269_);
v___x_2277_ = lean_nat_dec_eq(v___x_2276_, v___x_2275_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2269_);
lean_ctor_set(v___x_2278_, 1, v___x_2275_);
lean_ctor_set(v___x_2278_, 2, v___x_2276_);
v___x_2279_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2278_);
v___x_2280_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
lean_ctor_set(v___x_2280_, 2, v___x_2275_);
lean_ctor_set(v___x_2280_, 3, v___x_2275_);
v___y_2272_ = v___x_2280_;
goto v___jp_2271_;
}
else
{
lean_object* v___x_2281_; 
lean_dec_ref(v___x_2269_);
v___x_2281_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_2272_ = v___x_2281_;
goto v___jp_2271_;
}
v___jp_2271_:
{
uint8_t v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = 0;
v___x_2274_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2270_, v___y_2272_, v___x_2273_);
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2282_, lean_object* v_s_2283_){
_start:
{
uint8_t v_res_2284_; lean_object* v_r_2285_; 
v_res_2284_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2282_, v_s_2283_);
lean_dec_ref(v_s_2283_);
v_r_2285_ = lean_box(v_res_2284_);
return v_r_2285_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v___y_2286_, uint8_t v_suppressElabErrors_2287_, lean_object* v_x_2288_){
_start:
{
if (lean_obj_tag(v_x_2288_) == 1)
{
lean_object* v_pre_2289_; 
v_pre_2289_ = lean_ctor_get(v_x_2288_, 0);
if (lean_obj_tag(v_pre_2289_) == 0)
{
lean_object* v_str_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v_str_2290_ = lean_ctor_get(v_x_2288_, 1);
v___x_2291_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2292_ = lean_string_dec_eq(v_str_2290_, v___x_2291_);
if (v___x_2292_ == 0)
{
return v___y_2286_;
}
else
{
return v_suppressElabErrors_2287_;
}
}
else
{
return v___y_2286_;
}
}
else
{
return v___y_2286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v___y_2293_, lean_object* v_suppressElabErrors_2294_, lean_object* v_x_2295_){
_start:
{
uint8_t v___y_29379__boxed_2296_; uint8_t v_suppressElabErrors_boxed_2297_; uint8_t v_res_2298_; lean_object* v_r_2299_; 
v___y_29379__boxed_2296_ = lean_unbox(v___y_2293_);
v_suppressElabErrors_boxed_2297_ = lean_unbox(v_suppressElabErrors_2294_);
v_res_2298_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v___y_29379__boxed_2296_, v_suppressElabErrors_boxed_2297_, v_x_2295_);
lean_dec(v_x_2295_);
v_r_2299_ = lean_box(v_res_2298_);
return v_r_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2300_, lean_object* v_msgData_2301_, uint8_t v_severity_2302_, uint8_t v_isSilent_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; uint8_t v___y_2311_; lean_object* v___y_2312_; uint8_t v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; uint8_t v___y_2372_; lean_object* v___y_2373_; uint8_t v___y_2374_; uint8_t v___y_2375_; lean_object* v___y_2376_; uint8_t v___y_2400_; uint8_t v___y_2401_; uint8_t v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; uint8_t v___y_2408_; uint8_t v___y_2409_; uint8_t v___y_2410_; uint8_t v___x_2425_; uint8_t v___y_2427_; uint8_t v___y_2428_; uint8_t v___y_2429_; uint8_t v___y_2431_; uint8_t v___x_2443_; 
v___x_2425_ = 2;
v___x_2443_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2302_, v___x_2425_);
if (v___x_2443_ == 0)
{
v___y_2431_ = v___x_2443_;
goto v___jp_2430_;
}
else
{
uint8_t v___x_2444_; 
lean_inc_ref(v_msgData_2301_);
v___x_2444_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2301_);
v___y_2431_ = v___x_2444_;
goto v___jp_2430_;
}
v___jp_2307_:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Elab_Command_getScope___redArg(v___y_2315_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = l_Lean_Elab_Command_getScope___redArg(v___y_2315_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2354_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2354_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2354_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v_currNamespace_2324_; lean_object* v_openDecls_2325_; lean_object* v_env_2326_; lean_object* v_messages_2327_; lean_object* v_scopes_2328_; lean_object* v_usedQuotCtxts_2329_; lean_object* v_nextMacroScope_2330_; lean_object* v_maxRecDepth_2331_; lean_object* v_ngen_2332_; lean_object* v_auxDeclNGen_2333_; lean_object* v_infoState_2334_; lean_object* v_traceState_2335_; lean_object* v_snapshotTasks_2336_; lean_object* v_prevLinterStates_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2353_; 
v___x_2323_ = lean_st_ref_take(v___y_2315_);
v_currNamespace_2324_ = lean_ctor_get(v_a_2317_, 2);
lean_inc(v_currNamespace_2324_);
lean_dec(v_a_2317_);
v_openDecls_2325_ = lean_ctor_get(v_a_2319_, 3);
lean_inc(v_openDecls_2325_);
lean_dec(v_a_2319_);
v_env_2326_ = lean_ctor_get(v___x_2323_, 0);
v_messages_2327_ = lean_ctor_get(v___x_2323_, 1);
v_scopes_2328_ = lean_ctor_get(v___x_2323_, 2);
v_usedQuotCtxts_2329_ = lean_ctor_get(v___x_2323_, 3);
v_nextMacroScope_2330_ = lean_ctor_get(v___x_2323_, 4);
v_maxRecDepth_2331_ = lean_ctor_get(v___x_2323_, 5);
v_ngen_2332_ = lean_ctor_get(v___x_2323_, 6);
v_auxDeclNGen_2333_ = lean_ctor_get(v___x_2323_, 7);
v_infoState_2334_ = lean_ctor_get(v___x_2323_, 8);
v_traceState_2335_ = lean_ctor_get(v___x_2323_, 9);
v_snapshotTasks_2336_ = lean_ctor_get(v___x_2323_, 10);
v_prevLinterStates_2337_ = lean_ctor_get(v___x_2323_, 11);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2339_ = v___x_2323_;
v_isShared_2340_ = v_isSharedCheck_2353_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_prevLinterStates_2337_);
lean_inc(v_snapshotTasks_2336_);
lean_inc(v_traceState_2335_);
lean_inc(v_infoState_2334_);
lean_inc(v_auxDeclNGen_2333_);
lean_inc(v_ngen_2332_);
lean_inc(v_maxRecDepth_2331_);
lean_inc(v_nextMacroScope_2330_);
lean_inc(v_usedQuotCtxts_2329_);
lean_inc(v_scopes_2328_);
lean_inc(v_messages_2327_);
lean_inc(v_env_2326_);
lean_dec(v___x_2323_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2353_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2341_, 0, v_currNamespace_2324_);
lean_ctor_set(v___x_2341_, 1, v_openDecls_2325_);
v___x_2342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
lean_ctor_set(v___x_2342_, 1, v___y_2308_);
lean_inc_ref(v___y_2309_);
lean_inc_ref(v___y_2314_);
v___x_2343_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2343_, 0, v___y_2314_);
lean_ctor_set(v___x_2343_, 1, v___y_2312_);
lean_ctor_set(v___x_2343_, 2, v___y_2310_);
lean_ctor_set(v___x_2343_, 3, v___y_2309_);
lean_ctor_set(v___x_2343_, 4, v___x_2342_);
lean_ctor_set_uint8(v___x_2343_, sizeof(void*)*5, v___y_2313_);
lean_ctor_set_uint8(v___x_2343_, sizeof(void*)*5 + 1, v___y_2311_);
lean_ctor_set_uint8(v___x_2343_, sizeof(void*)*5 + 2, v_isSilent_2303_);
v___x_2344_ = l_Lean_MessageLog_add(v___x_2343_, v_messages_2327_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 1, v___x_2344_);
v___x_2346_ = v___x_2339_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_env_2326_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_scopes_2328_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v_usedQuotCtxts_2329_);
lean_ctor_set(v_reuseFailAlloc_2352_, 4, v_nextMacroScope_2330_);
lean_ctor_set(v_reuseFailAlloc_2352_, 5, v_maxRecDepth_2331_);
lean_ctor_set(v_reuseFailAlloc_2352_, 6, v_ngen_2332_);
lean_ctor_set(v_reuseFailAlloc_2352_, 7, v_auxDeclNGen_2333_);
lean_ctor_set(v_reuseFailAlloc_2352_, 8, v_infoState_2334_);
lean_ctor_set(v_reuseFailAlloc_2352_, 9, v_traceState_2335_);
lean_ctor_set(v_reuseFailAlloc_2352_, 10, v_snapshotTasks_2336_);
lean_ctor_set(v_reuseFailAlloc_2352_, 11, v_prevLinterStates_2337_);
v___x_2346_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2347_ = lean_st_ref_set(v___y_2315_, v___x_2346_);
v___x_2348_ = lean_box(0);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2348_);
v___x_2350_ = v___x_2321_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v_a_2317_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2308_);
v_a_2355_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2318_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2318_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2308_);
v_a_2363_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2316_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2316_);
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
v___jp_2371_:
{
lean_object* v_fileName_2377_; lean_object* v_fileMap_2378_; uint8_t v_suppressElabErrors_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2398_; 
v_fileName_2377_ = lean_ctor_get(v___y_2304_, 0);
v_fileMap_2378_ = lean_ctor_get(v___y_2304_, 1);
v_suppressElabErrors_2379_ = lean_ctor_get_uint8(v___y_2304_, sizeof(void*)*10);
v___x_2380_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2301_);
v___x_2381_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2380_, v___y_2305_);
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2398_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2398_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_inc_ref_n(v_fileMap_2378_, 2);
v___x_2386_ = l_Lean_FileMap_toPosition(v_fileMap_2378_, v___y_2373_);
lean_dec(v___y_2373_);
v___x_2387_ = l_Lean_FileMap_toPosition(v_fileMap_2378_, v___y_2376_);
lean_dec(v___y_2376_);
v___x_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
v___x_2389_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
if (v_suppressElabErrors_2379_ == 0)
{
lean_del_object(v___x_2384_);
v___y_2308_ = v_a_2382_;
v___y_2309_ = v___x_2389_;
v___y_2310_ = v___x_2388_;
v___y_2311_ = v___y_2374_;
v___y_2312_ = v___x_2386_;
v___y_2313_ = v___y_2375_;
v___y_2314_ = v_fileName_2377_;
v___y_2315_ = v___y_2305_;
goto v___jp_2307_;
}
else
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___f_2392_; uint8_t v___x_2393_; 
v___x_2390_ = lean_box(v___y_2372_);
v___x_2391_ = lean_box(v_suppressElabErrors_2379_);
v___f_2392_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2392_, 0, v___x_2390_);
lean_closure_set(v___f_2392_, 1, v___x_2391_);
lean_inc(v_a_2382_);
v___x_2393_ = l_Lean_MessageData_hasTag(v___f_2392_, v_a_2382_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
lean_dec_ref_known(v___x_2388_, 1);
lean_dec_ref(v___x_2386_);
lean_dec(v_a_2382_);
v___x_2394_ = lean_box(0);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2394_);
v___x_2396_ = v___x_2384_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
else
{
lean_del_object(v___x_2384_);
v___y_2308_ = v_a_2382_;
v___y_2309_ = v___x_2389_;
v___y_2310_ = v___x_2388_;
v___y_2311_ = v___y_2374_;
v___y_2312_ = v___x_2386_;
v___y_2313_ = v___y_2375_;
v___y_2314_ = v_fileName_2377_;
v___y_2315_ = v___y_2305_;
goto v___jp_2307_;
}
}
}
}
v___jp_2399_:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_Syntax_getTailPos_x3f(v___y_2403_, v___y_2402_);
lean_dec(v___y_2403_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_inc(v___y_2404_);
v___y_2372_ = v___y_2400_;
v___y_2373_ = v___y_2404_;
v___y_2374_ = v___y_2401_;
v___y_2375_ = v___y_2402_;
v___y_2376_ = v___y_2404_;
goto v___jp_2371_;
}
else
{
lean_object* v_val_2406_; 
v_val_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_val_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v___y_2372_ = v___y_2400_;
v___y_2373_ = v___y_2404_;
v___y_2374_ = v___y_2401_;
v___y_2375_ = v___y_2402_;
v___y_2376_ = v_val_2406_;
goto v___jp_2371_;
}
}
v___jp_2407_:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_Elab_Command_getRef___redArg(v___y_2304_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v_ref_2413_; lean_object* v___x_2414_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v_ref_2413_ = l_Lean_replaceRef(v_ref_2300_, v_a_2412_);
lean_dec(v_a_2412_);
v___x_2414_ = l_Lean_Syntax_getPos_x3f(v_ref_2413_, v___y_2409_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_unsigned_to_nat(0u);
v___y_2400_ = v___y_2408_;
v___y_2401_ = v___y_2410_;
v___y_2402_ = v___y_2409_;
v___y_2403_ = v_ref_2413_;
v___y_2404_ = v___x_2415_;
goto v___jp_2399_;
}
else
{
lean_object* v_val_2416_; 
v_val_2416_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_val_2416_);
lean_dec_ref_known(v___x_2414_, 1);
v___y_2400_ = v___y_2408_;
v___y_2401_ = v___y_2410_;
v___y_2402_ = v___y_2409_;
v___y_2403_ = v_ref_2413_;
v___y_2404_ = v_val_2416_;
goto v___jp_2399_;
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec_ref(v_msgData_2301_);
v_a_2417_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2411_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2411_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
v___jp_2426_:
{
if (v___y_2429_ == 0)
{
v___y_2408_ = v___y_2427_;
v___y_2409_ = v___y_2428_;
v___y_2410_ = v_severity_2302_;
goto v___jp_2407_;
}
else
{
v___y_2408_ = v___y_2427_;
v___y_2409_ = v___y_2428_;
v___y_2410_ = v___x_2425_;
goto v___jp_2407_;
}
}
v___jp_2430_:
{
if (v___y_2431_ == 0)
{
lean_object* v___x_2432_; lean_object* v_scopes_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v_opts_2436_; uint8_t v___x_2437_; uint8_t v___x_2438_; 
v___x_2432_ = lean_st_ref_get(v___y_2305_);
v_scopes_2433_ = lean_ctor_get(v___x_2432_, 2);
lean_inc(v_scopes_2433_);
lean_dec(v___x_2432_);
v___x_2434_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2435_ = l_List_head_x21___redArg(v___x_2434_, v_scopes_2433_);
lean_dec(v_scopes_2433_);
v_opts_2436_ = lean_ctor_get(v___x_2435_, 1);
lean_inc_ref(v_opts_2436_);
lean_dec(v___x_2435_);
v___x_2437_ = 1;
v___x_2438_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2302_, v___x_2437_);
if (v___x_2438_ == 0)
{
lean_dec_ref(v_opts_2436_);
v___y_2427_ = v___y_2431_;
v___y_2428_ = v___y_2431_;
v___y_2429_ = v___x_2438_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = l_Lean_warningAsError;
v___x_2440_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2436_, v___x_2439_);
lean_dec_ref(v_opts_2436_);
v___y_2427_ = v___y_2431_;
v___y_2428_ = v___y_2431_;
v___y_2429_ = v___x_2440_;
goto v___jp_2426_;
}
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec_ref(v_msgData_2301_);
v___x_2441_ = lean_box(0);
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2445_, lean_object* v_msgData_2446_, lean_object* v_severity_2447_, lean_object* v_isSilent_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
uint8_t v_severity_boxed_2452_; uint8_t v_isSilent_boxed_2453_; lean_object* v_res_2454_; 
v_severity_boxed_2452_ = lean_unbox(v_severity_2447_);
v_isSilent_boxed_2453_ = lean_unbox(v_isSilent_2448_);
v_res_2454_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2445_, v_msgData_2446_, v_severity_boxed_2452_, v_isSilent_boxed_2453_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v_ref_2445_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2455_, lean_object* v_msgData_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
uint8_t v___x_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = 2;
v___x_2461_ = 0;
v___x_2462_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2455_, v_msgData_2456_, v___x_2460_, v___x_2461_, v___y_2457_, v___y_2458_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2463_, lean_object* v_msgData_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2463_, v_msgData_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v_ref_2463_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2469_, lean_object* v___x_2470_, lean_object* v___x_2471_, lean_object* v_a_2472_, lean_object* v_b_2473_){
_start:
{
lean_object* v_it_2475_; lean_object* v_startInclusive_2476_; lean_object* v_endExclusive_2477_; 
if (lean_obj_tag(v_a_2472_) == 0)
{
lean_object* v_currPos_2482_; lean_object* v_searcher_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2512_; 
v_currPos_2482_ = lean_ctor_get(v_a_2472_, 0);
v_searcher_2483_ = lean_ctor_get(v_a_2472_, 1);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_a_2472_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2485_ = v_a_2472_;
v_isShared_2486_ = v_isSharedCheck_2512_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_searcher_2483_);
lean_inc(v_currPos_2482_);
lean_dec(v_a_2472_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2512_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v_str_2487_; lean_object* v_startInclusive_2488_; lean_object* v_endExclusive_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v_str_2487_ = lean_ctor_get(v___x_2470_, 0);
v_startInclusive_2488_ = lean_ctor_get(v___x_2470_, 1);
v_endExclusive_2489_ = lean_ctor_get(v___x_2470_, 2);
v___x_2490_ = lean_nat_sub(v_endExclusive_2489_, v_startInclusive_2488_);
v___x_2491_ = lean_nat_dec_eq(v_searcher_2483_, v___x_2490_);
lean_dec(v___x_2490_);
if (v___x_2491_ == 0)
{
uint32_t v___x_2492_; lean_object* v___x_2493_; uint32_t v___x_2494_; uint8_t v___x_2495_; 
v___x_2492_ = 10;
v___x_2493_ = lean_nat_add(v_startInclusive_2488_, v_searcher_2483_);
v___x_2494_ = lean_string_utf8_get_fast(v_str_2487_, v___x_2493_);
v___x_2495_ = lean_uint32_dec_eq(v___x_2494_, v___x_2492_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
lean_dec(v_searcher_2483_);
v___x_2496_ = lean_string_utf8_next_fast(v_str_2487_, v___x_2493_);
lean_dec(v___x_2493_);
v___x_2497_ = lean_nat_sub(v___x_2496_, v_startInclusive_2488_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v___x_2497_);
v___x_2499_ = v___x_2485_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_currPos_2482_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
v_a_2472_ = v___x_2499_;
goto _start;
}
}
else
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v_slice_2505_; lean_object* v_nextIt_2507_; 
v___x_2502_ = lean_string_utf8_next_fast(v_str_2487_, v___x_2493_);
v___x_2503_ = lean_nat_sub(v___x_2502_, v___x_2493_);
lean_dec(v___x_2493_);
v___x_2504_ = lean_nat_add(v_searcher_2483_, v___x_2503_);
lean_dec(v___x_2503_);
v_slice_2505_ = l_String_Slice_subslice_x21(v___x_2470_, v_currPos_2482_, v_searcher_2483_);
lean_inc(v___x_2504_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v___x_2504_);
lean_ctor_set(v___x_2485_, 0, v___x_2504_);
v_nextIt_2507_ = v___x_2485_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v___x_2504_);
v_nextIt_2507_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v_startInclusive_2508_; lean_object* v_endExclusive_2509_; 
v_startInclusive_2508_ = lean_ctor_get(v_slice_2505_, 0);
lean_inc(v_startInclusive_2508_);
v_endExclusive_2509_ = lean_ctor_get(v_slice_2505_, 1);
lean_inc(v_endExclusive_2509_);
lean_dec_ref(v_slice_2505_);
v_it_2475_ = v_nextIt_2507_;
v_startInclusive_2476_ = v_startInclusive_2508_;
v_endExclusive_2477_ = v_endExclusive_2509_;
goto v___jp_2474_;
}
}
}
else
{
lean_object* v___x_2511_; 
lean_del_object(v___x_2485_);
lean_dec(v_searcher_2483_);
v___x_2511_ = lean_box(1);
lean_inc(v___x_2471_);
v_it_2475_ = v___x_2511_;
v_startInclusive_2476_ = v_currPos_2482_;
v_endExclusive_2477_ = v___x_2471_;
goto v___jp_2474_;
}
}
}
else
{
lean_dec(v___x_2471_);
lean_dec_ref(v___x_2469_);
return v_b_2473_;
}
v___jp_2474_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_inc_ref(v___x_2469_);
v___x_2478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2469_);
lean_ctor_set(v___x_2478_, 1, v_startInclusive_2476_);
lean_ctor_set(v___x_2478_, 2, v_endExclusive_2477_);
v___x_2479_ = l_String_Slice_toString(v___x_2478_);
lean_dec_ref_known(v___x_2478_, 3);
v___x_2480_ = lean_array_push(v_b_2473_, v___x_2479_);
v_a_2472_ = v_it_2475_;
v_b_2473_ = v___x_2480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2513_, lean_object* v___x_2514_, lean_object* v___x_2515_, lean_object* v_a_2516_, lean_object* v_b_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2513_, v___x_2514_, v___x_2515_, v_a_2516_, v_b_2517_);
lean_dec_ref(v___x_2514_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2519_, lean_object* v___x_2520_, lean_object* v___x_2521_, lean_object* v_a_2522_, lean_object* v_b_2523_){
_start:
{
lean_object* v_it_2525_; lean_object* v_startInclusive_2526_; lean_object* v_endExclusive_2527_; 
if (lean_obj_tag(v_a_2522_) == 0)
{
lean_object* v_currPos_2532_; lean_object* v_searcher_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2562_; 
v_currPos_2532_ = lean_ctor_get(v_a_2522_, 0);
v_searcher_2533_ = lean_ctor_get(v_a_2522_, 1);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_a_2522_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2535_ = v_a_2522_;
v_isShared_2536_ = v_isSharedCheck_2562_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_searcher_2533_);
lean_inc(v_currPos_2532_);
lean_dec(v_a_2522_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2562_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v_str_2537_; lean_object* v_startInclusive_2538_; lean_object* v_endExclusive_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; 
v_str_2537_ = lean_ctor_get(v___x_2520_, 0);
v_startInclusive_2538_ = lean_ctor_get(v___x_2520_, 1);
v_endExclusive_2539_ = lean_ctor_get(v___x_2520_, 2);
v___x_2540_ = lean_nat_sub(v_endExclusive_2539_, v_startInclusive_2538_);
v___x_2541_ = lean_nat_dec_eq(v_searcher_2533_, v___x_2540_);
lean_dec(v___x_2540_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; uint32_t v___x_2543_; uint32_t v___x_2544_; uint8_t v___x_2545_; 
v___x_2542_ = lean_nat_add(v_startInclusive_2538_, v_searcher_2533_);
v___x_2543_ = lean_string_utf8_get_fast(v_str_2537_, v___x_2542_);
v___x_2544_ = 10;
v___x_2545_ = lean_uint32_dec_eq(v___x_2543_, v___x_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_dec(v_searcher_2533_);
v___x_2546_ = lean_string_utf8_next_fast(v_str_2537_, v___x_2542_);
lean_dec(v___x_2542_);
v___x_2547_ = lean_nat_sub(v___x_2546_, v_startInclusive_2538_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 1, v___x_2547_);
v___x_2549_ = v___x_2535_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_currPos_2532_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; 
v___x_2550_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2549_, v_b_2523_);
return v___x_2550_;
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_slice_2555_; lean_object* v_nextIt_2557_; 
v___x_2552_ = lean_string_utf8_next_fast(v_str_2537_, v___x_2542_);
v___x_2553_ = lean_nat_sub(v___x_2552_, v___x_2542_);
lean_dec(v___x_2542_);
v___x_2554_ = lean_nat_add(v_searcher_2533_, v___x_2553_);
lean_dec(v___x_2553_);
v_slice_2555_ = l_String_Slice_subslice_x21(v___x_2520_, v_currPos_2532_, v_searcher_2533_);
lean_inc(v___x_2554_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 1, v___x_2554_);
lean_ctor_set(v___x_2535_, 0, v___x_2554_);
v_nextIt_2557_ = v___x_2535_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v___x_2554_);
v_nextIt_2557_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v_startInclusive_2558_; lean_object* v_endExclusive_2559_; 
v_startInclusive_2558_ = lean_ctor_get(v_slice_2555_, 0);
lean_inc(v_startInclusive_2558_);
v_endExclusive_2559_ = lean_ctor_get(v_slice_2555_, 1);
lean_inc(v_endExclusive_2559_);
lean_dec_ref(v_slice_2555_);
v_it_2525_ = v_nextIt_2557_;
v_startInclusive_2526_ = v_startInclusive_2558_;
v_endExclusive_2527_ = v_endExclusive_2559_;
goto v___jp_2524_;
}
}
}
else
{
lean_object* v___x_2561_; 
lean_del_object(v___x_2535_);
lean_dec(v_searcher_2533_);
v___x_2561_ = lean_box(1);
lean_inc(v___x_2521_);
v_it_2525_ = v___x_2561_;
v_startInclusive_2526_ = v_currPos_2532_;
v_endExclusive_2527_ = v___x_2521_;
goto v___jp_2524_;
}
}
}
else
{
lean_dec(v___x_2521_);
lean_dec_ref(v___x_2519_);
return v_b_2523_;
}
v___jp_2524_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_inc_ref(v___x_2519_);
v___x_2528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2519_);
lean_ctor_set(v___x_2528_, 1, v_startInclusive_2526_);
lean_ctor_set(v___x_2528_, 2, v_endExclusive_2527_);
v___x_2529_ = l_String_Slice_toString(v___x_2528_);
lean_dec_ref_known(v___x_2528_, 3);
v___x_2530_ = lean_array_push(v_b_2523_, v___x_2529_);
v___x_2531_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2519_, v___x_2520_, v___x_2521_, v_it_2525_, v___x_2530_);
return v___x_2531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2563_, lean_object* v___x_2564_, lean_object* v___x_2565_, lean_object* v_a_2566_, lean_object* v_b_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2563_, v___x_2564_, v___x_2565_, v_a_2566_, v_b_2567_);
lean_dec_ref(v___x_2564_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; lean_object* v_infoState_2573_; uint8_t v_enabled_2574_; 
v___x_2572_ = lean_st_ref_get(v___y_2570_);
v_infoState_2573_ = lean_ctor_get(v___x_2572_, 8);
lean_inc_ref(v_infoState_2573_);
lean_dec(v___x_2572_);
v_enabled_2574_ = lean_ctor_get_uint8(v_infoState_2573_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2573_);
if (v_enabled_2574_ == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_dec_ref(v_t_2569_);
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
return v___x_2576_;
}
else
{
lean_object* v___x_2577_; lean_object* v_infoState_2578_; lean_object* v_env_2579_; lean_object* v_messages_2580_; lean_object* v_scopes_2581_; lean_object* v_usedQuotCtxts_2582_; lean_object* v_nextMacroScope_2583_; lean_object* v_maxRecDepth_2584_; lean_object* v_ngen_2585_; lean_object* v_auxDeclNGen_2586_; lean_object* v_traceState_2587_; lean_object* v_snapshotTasks_2588_; lean_object* v_prevLinterStates_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2611_; 
v___x_2577_ = lean_st_ref_take(v___y_2570_);
v_infoState_2578_ = lean_ctor_get(v___x_2577_, 8);
v_env_2579_ = lean_ctor_get(v___x_2577_, 0);
v_messages_2580_ = lean_ctor_get(v___x_2577_, 1);
v_scopes_2581_ = lean_ctor_get(v___x_2577_, 2);
v_usedQuotCtxts_2582_ = lean_ctor_get(v___x_2577_, 3);
v_nextMacroScope_2583_ = lean_ctor_get(v___x_2577_, 4);
v_maxRecDepth_2584_ = lean_ctor_get(v___x_2577_, 5);
v_ngen_2585_ = lean_ctor_get(v___x_2577_, 6);
v_auxDeclNGen_2586_ = lean_ctor_get(v___x_2577_, 7);
v_traceState_2587_ = lean_ctor_get(v___x_2577_, 9);
v_snapshotTasks_2588_ = lean_ctor_get(v___x_2577_, 10);
v_prevLinterStates_2589_ = lean_ctor_get(v___x_2577_, 11);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2591_ = v___x_2577_;
v_isShared_2592_ = v_isSharedCheck_2611_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_prevLinterStates_2589_);
lean_inc(v_snapshotTasks_2588_);
lean_inc(v_traceState_2587_);
lean_inc(v_infoState_2578_);
lean_inc(v_auxDeclNGen_2586_);
lean_inc(v_ngen_2585_);
lean_inc(v_maxRecDepth_2584_);
lean_inc(v_nextMacroScope_2583_);
lean_inc(v_usedQuotCtxts_2582_);
lean_inc(v_scopes_2581_);
lean_inc(v_messages_2580_);
lean_inc(v_env_2579_);
lean_dec(v___x_2577_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2611_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
uint8_t v_enabled_2593_; lean_object* v_assignment_2594_; lean_object* v_lazyAssignment_2595_; lean_object* v_trees_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2610_; 
v_enabled_2593_ = lean_ctor_get_uint8(v_infoState_2578_, sizeof(void*)*3);
v_assignment_2594_ = lean_ctor_get(v_infoState_2578_, 0);
v_lazyAssignment_2595_ = lean_ctor_get(v_infoState_2578_, 1);
v_trees_2596_ = lean_ctor_get(v_infoState_2578_, 2);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_infoState_2578_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2598_ = v_infoState_2578_;
v_isShared_2599_ = v_isSharedCheck_2610_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_trees_2596_);
lean_inc(v_lazyAssignment_2595_);
lean_inc(v_assignment_2594_);
lean_dec(v_infoState_2578_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2610_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2600_ = l_Lean_PersistentArray_push___redArg(v_trees_2596_, v_t_2569_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 2, v___x_2600_);
v___x_2602_ = v___x_2598_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_assignment_2594_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_lazyAssignment_2595_);
lean_ctor_set(v_reuseFailAlloc_2609_, 2, v___x_2600_);
lean_ctor_set_uint8(v_reuseFailAlloc_2609_, sizeof(void*)*3, v_enabled_2593_);
v___x_2602_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2604_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 8, v___x_2602_);
v___x_2604_ = v___x_2591_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_env_2579_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_messages_2580_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v_scopes_2581_);
lean_ctor_set(v_reuseFailAlloc_2608_, 3, v_usedQuotCtxts_2582_);
lean_ctor_set(v_reuseFailAlloc_2608_, 4, v_nextMacroScope_2583_);
lean_ctor_set(v_reuseFailAlloc_2608_, 5, v_maxRecDepth_2584_);
lean_ctor_set(v_reuseFailAlloc_2608_, 6, v_ngen_2585_);
lean_ctor_set(v_reuseFailAlloc_2608_, 7, v_auxDeclNGen_2586_);
lean_ctor_set(v_reuseFailAlloc_2608_, 8, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2608_, 9, v_traceState_2587_);
lean_ctor_set(v_reuseFailAlloc_2608_, 10, v_snapshotTasks_2588_);
lean_ctor_set(v_reuseFailAlloc_2608_, 11, v_prevLinterStates_2589_);
v___x_2604_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = lean_st_ref_set(v___y_2570_, v___x_2604_);
v___x_2606_ = lean_box(0);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2612_, v___y_2613_);
lean_dec(v___y_2613_);
return v_res_2615_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = lean_unsigned_to_nat(32u);
v___x_2617_ = lean_mk_empty_array_with_capacity(v___x_2616_);
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2619_ = ((size_t)5ULL);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_unsigned_to_nat(32u);
v___x_2622_ = lean_mk_empty_array_with_capacity(v___x_2621_);
v___x_2623_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2624_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2622_);
lean_ctor_set(v___x_2624_, 2, v___x_2620_);
lean_ctor_set(v___x_2624_, 3, v___x_2620_);
lean_ctor_set_usize(v___x_2624_, 4, v___x_2619_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; lean_object* v_infoState_2630_; uint8_t v_enabled_2631_; 
v___x_2629_ = lean_st_ref_get(v___y_2627_);
v_infoState_2630_ = lean_ctor_get(v___x_2629_, 8);
lean_inc_ref(v_infoState_2630_);
lean_dec(v___x_2629_);
v_enabled_2631_ = lean_ctor_get_uint8(v_infoState_2630_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2630_);
if (v_enabled_2631_ == 0)
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_dec_ref(v_t_2625_);
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
return v___x_2633_;
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2635_, 0, v_t_2625_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2635_, v___y_2627_);
return v___x_2636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(lean_object* v_edited_2642_, lean_object* v___x_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v_fst_2646_; lean_object* v_snd_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2672_; 
v_fst_2646_ = lean_ctor_get(v_a_2645_, 0);
v_snd_2647_ = lean_ctor_get(v_a_2645_, 1);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_a_2645_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2649_ = v_a_2645_;
v_isShared_2650_ = v_isSharedCheck_2672_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_snd_2647_);
lean_inc(v_fst_2646_);
lean_dec(v_a_2645_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2672_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2651_; uint8_t v___y_2653_; uint8_t v___x_2668_; 
v___x_2651_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2668_ = lean_nat_dec_lt(v_snd_2647_, v___x_2643_);
if (v___x_2668_ == 0)
{
v___y_2653_ = v___x_2668_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2669_ = lean_array_get_borrowed(v___x_2651_, v_edited_2642_, v_snd_2647_);
v___x_2670_ = lean_string_dec_eq(v___x_2669_, v_a_2644_);
if (v___x_2670_ == 0)
{
v___y_2653_ = v___x_2668_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2671_; 
lean_del_object(v___x_2649_);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_fst_2646_);
lean_ctor_set(v___x_2671_, 1, v_snd_2647_);
return v___x_2671_;
}
}
v___jp_2652_:
{
if (v___y_2653_ == 0)
{
lean_object* v___x_2655_; 
if (v_isShared_2650_ == 0)
{
v___x_2655_ = v___x_2649_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_fst_2646_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_snd_2647_);
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
uint8_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2657_ = 0;
v___x_2658_ = lean_array_get_borrowed(v___x_2651_, v_edited_2642_, v_snd_2647_);
v___x_2659_ = lean_box(v___x_2657_);
lean_inc(v___x_2658_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 1, v___x_2658_);
lean_ctor_set(v___x_2649_, 0, v___x_2659_);
v___x_2661_ = v___x_2649_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v___x_2658_);
v___x_2661_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2662_ = lean_array_push(v_fst_2646_, v___x_2661_);
v___x_2663_ = lean_unsigned_to_nat(1u);
v___x_2664_ = lean_nat_add(v_snd_2647_, v___x_2663_);
lean_dec(v_snd_2647_);
v___x_2665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2662_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v_a_2645_ = v___x_2665_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg___boxed(lean_object* v_edited_2673_, lean_object* v___x_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2673_, v___x_2674_, v_a_2675_, v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v___x_2674_);
lean_dec_ref(v_edited_2673_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v_original_2678_, lean_object* v___x_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_fst_2682_; lean_object* v_snd_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2708_; 
v_fst_2682_ = lean_ctor_get(v_a_2681_, 0);
v_snd_2683_ = lean_ctor_get(v_a_2681_, 1);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_a_2681_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2685_ = v_a_2681_;
v_isShared_2686_ = v_isSharedCheck_2708_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_snd_2683_);
lean_inc(v_fst_2682_);
lean_dec(v_a_2681_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2708_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; uint8_t v___y_2689_; uint8_t v___x_2704_; 
v___x_2687_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2704_ = lean_nat_dec_lt(v_snd_2683_, v___x_2679_);
if (v___x_2704_ == 0)
{
v___y_2689_ = v___x_2704_;
goto v___jp_2688_;
}
else
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = lean_array_get_borrowed(v___x_2687_, v_original_2678_, v_snd_2683_);
v___x_2706_ = lean_string_dec_eq(v___x_2705_, v_a_2680_);
if (v___x_2706_ == 0)
{
v___y_2689_ = v___x_2704_;
goto v___jp_2688_;
}
else
{
lean_object* v___x_2707_; 
lean_del_object(v___x_2685_);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_fst_2682_);
lean_ctor_set(v___x_2707_, 1, v_snd_2683_);
return v___x_2707_;
}
}
v___jp_2688_:
{
if (v___y_2689_ == 0)
{
lean_object* v___x_2691_; 
if (v_isShared_2686_ == 0)
{
v___x_2691_ = v___x_2685_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_fst_2682_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_snd_2683_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
else
{
uint8_t v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2693_ = 1;
v___x_2694_ = lean_array_get_borrowed(v___x_2687_, v_original_2678_, v_snd_2683_);
v___x_2695_ = lean_box(v___x_2693_);
lean_inc(v___x_2694_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 1, v___x_2694_);
lean_ctor_set(v___x_2685_, 0, v___x_2695_);
v___x_2697_ = v___x_2685_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___x_2694_);
v___x_2697_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2698_ = lean_array_push(v_fst_2682_, v___x_2697_);
v___x_2699_ = lean_unsigned_to_nat(1u);
v___x_2700_ = lean_nat_add(v_snd_2683_, v___x_2699_);
lean_dec(v_snd_2683_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2698_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v_a_2681_ = v___x_2701_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v_original_2709_, lean_object* v___x_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2709_, v___x_2710_, v_a_2711_, v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v___x_2710_);
lean_dec_ref(v_original_2709_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v_original_2714_, lean_object* v___x_2715_, lean_object* v_edited_2716_, lean_object* v___x_2717_, lean_object* v_as_2718_, size_t v_sz_2719_, size_t v_i_2720_, lean_object* v_b_2721_){
_start:
{
uint8_t v___x_2722_; 
v___x_2722_ = lean_usize_dec_lt(v_i_2720_, v_sz_2719_);
if (v___x_2722_ == 0)
{
return v_b_2721_;
}
else
{
lean_object* v_snd_2723_; lean_object* v_fst_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2771_; 
v_snd_2723_ = lean_ctor_get(v_b_2721_, 1);
v_fst_2724_ = lean_ctor_get(v_b_2721_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_b_2721_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2726_ = v_b_2721_;
v_isShared_2727_ = v_isSharedCheck_2771_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_snd_2723_);
lean_inc(v_fst_2724_);
lean_dec(v_b_2721_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2771_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v_fst_2728_; lean_object* v_snd_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2770_; 
v_fst_2728_ = lean_ctor_get(v_snd_2723_, 0);
v_snd_2729_ = lean_ctor_get(v_snd_2723_, 1);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_snd_2723_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2731_ = v_snd_2723_;
v_isShared_2732_ = v_isSharedCheck_2770_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_snd_2729_);
lean_inc(v_fst_2728_);
lean_dec(v_snd_2723_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2770_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v_a_2733_; lean_object* v___x_2735_; 
v_a_2733_ = lean_array_uget_borrowed(v_as_2718_, v_i_2720_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 1, v_fst_2728_);
lean_ctor_set(v___x_2731_, 0, v_fst_2724_);
v___x_2735_ = v___x_2731_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_fst_2724_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v_fst_2728_);
v___x_2735_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; lean_object* v_fst_2737_; lean_object* v_snd_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2768_; 
v___x_2736_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2714_, v___x_2715_, v_a_2733_, v___x_2735_);
v_fst_2737_ = lean_ctor_get(v___x_2736_, 0);
v_snd_2738_ = lean_ctor_get(v___x_2736_, 1);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2740_ = v___x_2736_;
v_isShared_2741_ = v_isSharedCheck_2768_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_snd_2738_);
lean_inc(v_fst_2737_);
lean_dec(v___x_2736_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2768_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 1, v_snd_2729_);
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_fst_2737_);
lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_snd_2729_);
v___x_2743_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2744_; lean_object* v_fst_2745_; lean_object* v_snd_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2766_; 
v___x_2744_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2716_, v___x_2717_, v_a_2733_, v___x_2743_);
v_fst_2745_ = lean_ctor_get(v___x_2744_, 0);
v_snd_2746_ = lean_ctor_get(v___x_2744_, 1);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2748_ = v___x_2744_;
v_isShared_2749_ = v_isSharedCheck_2766_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_snd_2746_);
lean_inc(v_fst_2745_);
lean_dec(v___x_2744_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2766_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
uint8_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2750_ = 2;
v___x_2751_ = lean_box(v___x_2750_);
lean_inc(v_a_2733_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 1, v_a_2733_);
lean_ctor_set(v___x_2748_, 0, v___x_2751_);
v___x_2753_ = v___x_2748_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_a_2733_);
v___x_2753_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2754_ = lean_array_push(v_fst_2745_, v___x_2753_);
v___x_2755_ = lean_unsigned_to_nat(1u);
v___x_2756_ = lean_nat_add(v_snd_2738_, v___x_2755_);
lean_dec(v_snd_2738_);
v___x_2757_ = lean_nat_add(v_snd_2746_, v___x_2755_);
lean_dec(v_snd_2746_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 1, v___x_2757_);
lean_ctor_set(v___x_2726_, 0, v___x_2756_);
v___x_2759_ = v___x_2726_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; size_t v___x_2761_; size_t v___x_2762_; 
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2754_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = ((size_t)1ULL);
v___x_2762_ = lean_usize_add(v_i_2720_, v___x_2761_);
v_i_2720_ = v___x_2762_;
v_b_2721_ = v___x_2760_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v_original_2772_, lean_object* v___x_2773_, lean_object* v_edited_2774_, lean_object* v___x_2775_, lean_object* v_as_2776_, lean_object* v_sz_2777_, lean_object* v_i_2778_, lean_object* v_b_2779_){
_start:
{
size_t v_sz_boxed_2780_; size_t v_i_boxed_2781_; lean_object* v_res_2782_; 
v_sz_boxed_2780_ = lean_unbox_usize(v_sz_2777_);
lean_dec(v_sz_2777_);
v_i_boxed_2781_ = lean_unbox_usize(v_i_2778_);
lean_dec(v_i_2778_);
v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2772_, v___x_2773_, v_edited_2774_, v___x_2775_, v_as_2776_, v_sz_boxed_2780_, v_i_boxed_2781_, v_b_2779_);
lean_dec_ref(v_as_2776_);
lean_dec(v___x_2775_);
lean_dec_ref(v_edited_2774_);
lean_dec(v___x_2773_);
lean_dec_ref(v_original_2772_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v_edited_2783_, lean_object* v___x_2784_, lean_object* v_original_2785_, lean_object* v___x_2786_, lean_object* v_as_2787_, size_t v_sz_2788_, size_t v_i_2789_, lean_object* v_b_2790_){
_start:
{
uint8_t v___x_2791_; 
v___x_2791_ = lean_usize_dec_lt(v_i_2789_, v_sz_2788_);
if (v___x_2791_ == 0)
{
return v_b_2790_;
}
else
{
lean_object* v_snd_2792_; lean_object* v_fst_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2840_; 
v_snd_2792_ = lean_ctor_get(v_b_2790_, 1);
v_fst_2793_ = lean_ctor_get(v_b_2790_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_b_2790_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2795_ = v_b_2790_;
v_isShared_2796_ = v_isSharedCheck_2840_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_snd_2792_);
lean_inc(v_fst_2793_);
lean_dec(v_b_2790_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2840_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v_fst_2797_; lean_object* v_snd_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2839_; 
v_fst_2797_ = lean_ctor_get(v_snd_2792_, 0);
v_snd_2798_ = lean_ctor_get(v_snd_2792_, 1);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_snd_2792_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2800_ = v_snd_2792_;
v_isShared_2801_ = v_isSharedCheck_2839_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_snd_2798_);
lean_inc(v_fst_2797_);
lean_dec(v_snd_2792_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2839_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v_a_2802_; lean_object* v___x_2804_; 
v_a_2802_ = lean_array_uget_borrowed(v_as_2787_, v_i_2789_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 1, v_fst_2797_);
lean_ctor_set(v___x_2800_, 0, v_fst_2793_);
v___x_2804_ = v___x_2800_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_fst_2793_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_fst_2797_);
v___x_2804_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; lean_object* v_fst_2806_; lean_object* v_snd_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2837_; 
v___x_2805_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_2785_, v___x_2786_, v_a_2802_, v___x_2804_);
v_fst_2806_ = lean_ctor_get(v___x_2805_, 0);
v_snd_2807_ = lean_ctor_get(v___x_2805_, 1);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2809_ = v___x_2805_;
v_isShared_2810_ = v_isSharedCheck_2837_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_snd_2807_);
lean_inc(v_fst_2806_);
lean_dec(v___x_2805_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2837_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 1, v_snd_2798_);
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_fst_2806_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_snd_2798_);
v___x_2812_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2813_; lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2835_; 
v___x_2813_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_2783_, v___x_2784_, v_a_2802_, v___x_2812_);
v_fst_2814_ = lean_ctor_get(v___x_2813_, 0);
v_snd_2815_ = lean_ctor_get(v___x_2813_, 1);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2817_ = v___x_2813_;
v_isShared_2818_ = v_isSharedCheck_2835_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_snd_2815_);
lean_inc(v_fst_2814_);
lean_dec(v___x_2813_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2835_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
uint8_t v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
v___x_2819_ = 2;
v___x_2820_ = lean_box(v___x_2819_);
lean_inc(v_a_2802_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v_a_2802_);
lean_ctor_set(v___x_2817_, 0, v___x_2820_);
v___x_2822_ = v___x_2817_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_a_2802_);
v___x_2822_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2828_; 
v___x_2823_ = lean_array_push(v_fst_2814_, v___x_2822_);
v___x_2824_ = lean_unsigned_to_nat(1u);
v___x_2825_ = lean_nat_add(v_snd_2807_, v___x_2824_);
lean_dec(v_snd_2807_);
v___x_2826_ = lean_nat_add(v_snd_2815_, v___x_2824_);
lean_dec(v_snd_2815_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 1, v___x_2826_);
lean_ctor_set(v___x_2795_, 0, v___x_2825_);
v___x_2828_ = v___x_2795_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2825_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; size_t v___x_2830_; size_t v___x_2831_; lean_object* v___x_2832_; 
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2823_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = ((size_t)1ULL);
v___x_2831_ = lean_usize_add(v_i_2789_, v___x_2830_);
v___x_2832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v_original_2785_, v___x_2786_, v_edited_2783_, v___x_2784_, v_as_2787_, v_sz_2788_, v___x_2831_, v___x_2829_);
return v___x_2832_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v_edited_2841_, lean_object* v___x_2842_, lean_object* v_original_2843_, lean_object* v___x_2844_, lean_object* v_as_2845_, lean_object* v_sz_2846_, lean_object* v_i_2847_, lean_object* v_b_2848_){
_start:
{
size_t v_sz_boxed_2849_; size_t v_i_boxed_2850_; lean_object* v_res_2851_; 
v_sz_boxed_2849_ = lean_unbox_usize(v_sz_2846_);
lean_dec(v_sz_2846_);
v_i_boxed_2850_ = lean_unbox_usize(v_i_2847_);
lean_dec(v_i_2847_);
v_res_2851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_2841_, v___x_2842_, v_original_2843_, v___x_2844_, v_as_2845_, v_sz_boxed_2849_, v_i_boxed_2850_, v_b_2848_);
lean_dec_ref(v_as_2845_);
lean_dec(v___x_2844_);
lean_dec_ref(v_original_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_edited_2841_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(lean_object* v_a_2852_, lean_object* v_x_2853_){
_start:
{
if (lean_obj_tag(v_x_2853_) == 0)
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_box(0);
return v___x_2854_;
}
else
{
lean_object* v_key_2855_; lean_object* v_value_2856_; lean_object* v_tail_2857_; uint8_t v___x_2858_; 
v_key_2855_ = lean_ctor_get(v_x_2853_, 0);
v_value_2856_ = lean_ctor_get(v_x_2853_, 1);
v_tail_2857_ = lean_ctor_get(v_x_2853_, 2);
v___x_2858_ = lean_string_dec_eq(v_key_2855_, v_a_2852_);
if (v___x_2858_ == 0)
{
v_x_2853_ = v_tail_2857_;
goto _start;
}
else
{
lean_object* v___x_2860_; 
lean_inc(v_value_2856_);
v___x_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_value_2856_);
return v___x_2860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg___boxed(lean_object* v_a_2861_, lean_object* v_x_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2861_, v_x_2862_);
lean_dec(v_x_2862_);
lean_dec_ref(v_a_2861_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(lean_object* v_m_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v_buckets_2866_; lean_object* v___x_2867_; uint64_t v___x_2868_; uint64_t v___x_2869_; uint64_t v___x_2870_; uint64_t v_fold_2871_; uint64_t v___x_2872_; uint64_t v___x_2873_; uint64_t v___x_2874_; size_t v___x_2875_; size_t v___x_2876_; size_t v___x_2877_; size_t v___x_2878_; size_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_buckets_2866_ = lean_ctor_get(v_m_2864_, 1);
v___x_2867_ = lean_array_get_size(v_buckets_2866_);
v___x_2868_ = lean_string_hash(v_a_2865_);
v___x_2869_ = 32ULL;
v___x_2870_ = lean_uint64_shift_right(v___x_2868_, v___x_2869_);
v_fold_2871_ = lean_uint64_xor(v___x_2868_, v___x_2870_);
v___x_2872_ = 16ULL;
v___x_2873_ = lean_uint64_shift_right(v_fold_2871_, v___x_2872_);
v___x_2874_ = lean_uint64_xor(v_fold_2871_, v___x_2873_);
v___x_2875_ = lean_uint64_to_usize(v___x_2874_);
v___x_2876_ = lean_usize_of_nat(v___x_2867_);
v___x_2877_ = ((size_t)1ULL);
v___x_2878_ = lean_usize_sub(v___x_2876_, v___x_2877_);
v___x_2879_ = lean_usize_land(v___x_2875_, v___x_2878_);
v___x_2880_ = lean_array_uget_borrowed(v_buckets_2866_, v___x_2879_);
v___x_2881_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_2865_, v___x_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_m_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_2882_, v_a_2883_);
lean_dec_ref(v_a_2883_);
lean_dec_ref(v_m_2882_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(lean_object* v_a_2885_, lean_object* v_b_2886_, lean_object* v_x_2887_){
_start:
{
if (lean_obj_tag(v_x_2887_) == 0)
{
lean_dec(v_b_2886_);
lean_dec_ref(v_a_2885_);
return v_x_2887_;
}
else
{
lean_object* v_key_2888_; lean_object* v_value_2889_; lean_object* v_tail_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2902_; 
v_key_2888_ = lean_ctor_get(v_x_2887_, 0);
v_value_2889_ = lean_ctor_get(v_x_2887_, 1);
v_tail_2890_ = lean_ctor_get(v_x_2887_, 2);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_x_2887_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2892_ = v_x_2887_;
v_isShared_2893_ = v_isSharedCheck_2902_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_tail_2890_);
lean_inc(v_value_2889_);
lean_inc(v_key_2888_);
lean_dec(v_x_2887_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2902_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
uint8_t v___x_2894_; 
v___x_2894_ = lean_string_dec_eq(v_key_2888_, v_a_2885_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2885_, v_b_2886_, v_tail_2890_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 2, v___x_2895_);
v___x_2897_ = v___x_2892_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_key_2888_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_value_2889_);
lean_ctor_set(v_reuseFailAlloc_2898_, 2, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
else
{
lean_object* v___x_2900_; 
lean_dec(v_value_2889_);
lean_dec(v_key_2888_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 1, v_b_2886_);
lean_ctor_set(v___x_2892_, 0, v_a_2885_);
v___x_2900_ = v___x_2892_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2885_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_b_2886_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_tail_2890_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(lean_object* v_a_2903_, lean_object* v_x_2904_){
_start:
{
if (lean_obj_tag(v_x_2904_) == 0)
{
uint8_t v___x_2905_; 
v___x_2905_ = 0;
return v___x_2905_;
}
else
{
lean_object* v_key_2906_; lean_object* v_tail_2907_; uint8_t v___x_2908_; 
v_key_2906_ = lean_ctor_get(v_x_2904_, 0);
v_tail_2907_ = lean_ctor_get(v_x_2904_, 2);
v___x_2908_ = lean_string_dec_eq(v_key_2906_, v_a_2903_);
if (v___x_2908_ == 0)
{
v_x_2904_ = v_tail_2907_;
goto _start;
}
else
{
return v___x_2908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg___boxed(lean_object* v_a_2910_, lean_object* v_x_2911_){
_start:
{
uint8_t v_res_2912_; lean_object* v_r_2913_; 
v_res_2912_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2910_, v_x_2911_);
lean_dec(v_x_2911_);
lean_dec_ref(v_a_2910_);
v_r_2913_ = lean_box(v_res_2912_);
return v_r_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2914_, lean_object* v_x_2915_){
_start:
{
if (lean_obj_tag(v_x_2915_) == 0)
{
return v_x_2914_;
}
else
{
lean_object* v_key_2916_; lean_object* v_value_2917_; lean_object* v_tail_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2941_; 
v_key_2916_ = lean_ctor_get(v_x_2915_, 0);
v_value_2917_ = lean_ctor_get(v_x_2915_, 1);
v_tail_2918_ = lean_ctor_get(v_x_2915_, 2);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_x_2915_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2920_ = v_x_2915_;
v_isShared_2921_ = v_isSharedCheck_2941_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_tail_2918_);
lean_inc(v_value_2917_);
lean_inc(v_key_2916_);
lean_dec(v_x_2915_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2941_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; uint64_t v___x_2923_; uint64_t v___x_2924_; uint64_t v___x_2925_; uint64_t v_fold_2926_; uint64_t v___x_2927_; uint64_t v___x_2928_; uint64_t v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; size_t v___x_2933_; size_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2922_ = lean_array_get_size(v_x_2914_);
v___x_2923_ = lean_string_hash(v_key_2916_);
v___x_2924_ = 32ULL;
v___x_2925_ = lean_uint64_shift_right(v___x_2923_, v___x_2924_);
v_fold_2926_ = lean_uint64_xor(v___x_2923_, v___x_2925_);
v___x_2927_ = 16ULL;
v___x_2928_ = lean_uint64_shift_right(v_fold_2926_, v___x_2927_);
v___x_2929_ = lean_uint64_xor(v_fold_2926_, v___x_2928_);
v___x_2930_ = lean_uint64_to_usize(v___x_2929_);
v___x_2931_ = lean_usize_of_nat(v___x_2922_);
v___x_2932_ = ((size_t)1ULL);
v___x_2933_ = lean_usize_sub(v___x_2931_, v___x_2932_);
v___x_2934_ = lean_usize_land(v___x_2930_, v___x_2933_);
v___x_2935_ = lean_array_uget_borrowed(v_x_2914_, v___x_2934_);
lean_inc(v___x_2935_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 2, v___x_2935_);
v___x_2937_ = v___x_2920_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_key_2916_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_value_2917_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; 
v___x_2938_ = lean_array_uset(v_x_2914_, v___x_2934_, v___x_2937_);
v_x_2914_ = v___x_2938_;
v_x_2915_ = v_tail_2918_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(lean_object* v_i_2942_, lean_object* v_source_2943_, lean_object* v_target_2944_){
_start:
{
lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_2945_ = lean_array_get_size(v_source_2943_);
v___x_2946_ = lean_nat_dec_lt(v_i_2942_, v___x_2945_);
if (v___x_2946_ == 0)
{
lean_dec_ref(v_source_2943_);
lean_dec(v_i_2942_);
return v_target_2944_;
}
else
{
lean_object* v_es_2947_; lean_object* v___x_2948_; lean_object* v_source_2949_; lean_object* v_target_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_es_2947_ = lean_array_fget(v_source_2943_, v_i_2942_);
v___x_2948_ = lean_box(0);
v_source_2949_ = lean_array_fset(v_source_2943_, v_i_2942_, v___x_2948_);
v_target_2950_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_target_2944_, v_es_2947_);
v___x_2951_ = lean_unsigned_to_nat(1u);
v___x_2952_ = lean_nat_add(v_i_2942_, v___x_2951_);
lean_dec(v_i_2942_);
v_i_2942_ = v___x_2952_;
v_source_2943_ = v_source_2949_;
v_target_2944_ = v_target_2950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(lean_object* v_data_2954_){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v_nbuckets_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2955_ = lean_array_get_size(v_data_2954_);
v___x_2956_ = lean_unsigned_to_nat(2u);
v_nbuckets_2957_ = lean_nat_mul(v___x_2955_, v___x_2956_);
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_mk_array(v_nbuckets_2957_, v___x_2959_);
v___x_2961_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v___x_2958_, v_data_2954_, v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(lean_object* v_m_2962_, lean_object* v_a_2963_, lean_object* v_b_2964_){
_start:
{
lean_object* v_size_2965_; lean_object* v_buckets_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3009_; 
v_size_2965_ = lean_ctor_get(v_m_2962_, 0);
v_buckets_2966_ = lean_ctor_get(v_m_2962_, 1);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_m_2962_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2968_ = v_m_2962_;
v_isShared_2969_ = v_isSharedCheck_3009_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_buckets_2966_);
lean_inc(v_size_2965_);
lean_dec(v_m_2962_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_3009_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; uint64_t v___x_2971_; uint64_t v___x_2972_; uint64_t v___x_2973_; uint64_t v_fold_2974_; uint64_t v___x_2975_; uint64_t v___x_2976_; uint64_t v___x_2977_; size_t v___x_2978_; size_t v___x_2979_; size_t v___x_2980_; size_t v___x_2981_; size_t v___x_2982_; lean_object* v_bkt_2983_; uint8_t v___x_2984_; 
v___x_2970_ = lean_array_get_size(v_buckets_2966_);
v___x_2971_ = lean_string_hash(v_a_2963_);
v___x_2972_ = 32ULL;
v___x_2973_ = lean_uint64_shift_right(v___x_2971_, v___x_2972_);
v_fold_2974_ = lean_uint64_xor(v___x_2971_, v___x_2973_);
v___x_2975_ = 16ULL;
v___x_2976_ = lean_uint64_shift_right(v_fold_2974_, v___x_2975_);
v___x_2977_ = lean_uint64_xor(v_fold_2974_, v___x_2976_);
v___x_2978_ = lean_uint64_to_usize(v___x_2977_);
v___x_2979_ = lean_usize_of_nat(v___x_2970_);
v___x_2980_ = ((size_t)1ULL);
v___x_2981_ = lean_usize_sub(v___x_2979_, v___x_2980_);
v___x_2982_ = lean_usize_land(v___x_2978_, v___x_2981_);
v_bkt_2983_ = lean_array_uget_borrowed(v_buckets_2966_, v___x_2982_);
v___x_2984_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_2963_, v_bkt_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v_size_x27_2986_; lean_object* v___x_2987_; lean_object* v_buckets_x27_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2985_ = lean_unsigned_to_nat(1u);
v_size_x27_2986_ = lean_nat_add(v_size_2965_, v___x_2985_);
lean_dec(v_size_2965_);
lean_inc(v_bkt_2983_);
v___x_2987_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2987_, 0, v_a_2963_);
lean_ctor_set(v___x_2987_, 1, v_b_2964_);
lean_ctor_set(v___x_2987_, 2, v_bkt_2983_);
v_buckets_x27_2988_ = lean_array_uset(v_buckets_2966_, v___x_2982_, v___x_2987_);
v___x_2989_ = lean_unsigned_to_nat(4u);
v___x_2990_ = lean_nat_mul(v_size_x27_2986_, v___x_2989_);
v___x_2991_ = lean_unsigned_to_nat(3u);
v___x_2992_ = lean_nat_div(v___x_2990_, v___x_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_array_get_size(v_buckets_x27_2988_);
v___x_2994_ = lean_nat_dec_le(v___x_2992_, v___x_2993_);
lean_dec(v___x_2992_);
if (v___x_2994_ == 0)
{
lean_object* v_val_2995_; lean_object* v___x_2997_; 
v_val_2995_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_buckets_x27_2988_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v_val_2995_);
lean_ctor_set(v___x_2968_, 0, v_size_x27_2986_);
v___x_2997_ = v___x_2968_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_size_x27_2986_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_val_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
else
{
lean_object* v___x_3000_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v_buckets_x27_2988_);
lean_ctor_set(v___x_2968_, 0, v_size_x27_2986_);
v___x_3000_ = v___x_2968_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_size_x27_2986_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_buckets_x27_2988_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
else
{
lean_object* v___x_3002_; lean_object* v_buckets_x27_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
lean_inc(v_bkt_2983_);
v___x_3002_ = lean_box(0);
v_buckets_x27_3003_ = lean_array_uset(v_buckets_2966_, v___x_2982_, v___x_3002_);
v___x_3004_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_2963_, v_b_2964_, v_bkt_2983_);
v___x_3005_ = lean_array_uset(v_buckets_x27_3003_, v___x_2982_, v___x_3004_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v___x_3005_);
v___x_3007_ = v___x_2968_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_size_2965_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(lean_object* v_histogram_3010_, lean_object* v_index_3011_, lean_object* v_val_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3010_, v_val_3012_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3014_ = lean_unsigned_to_nat(1u);
v___x_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_index_3011_);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_box(0);
v___x_3018_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3014_);
lean_ctor_set(v___x_3018_, 1, v___x_3015_);
lean_ctor_set(v___x_3018_, 2, v___x_3016_);
lean_ctor_set(v___x_3018_, 3, v___x_3017_);
v___x_3019_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3010_, v_val_3012_, v___x_3018_);
return v___x_3019_;
}
else
{
lean_object* v_val_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3041_; 
v_val_3020_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3022_ = v___x_3013_;
v_isShared_3023_ = v_isSharedCheck_3041_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_val_3020_);
lean_dec(v___x_3013_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3041_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v_leftCount_3024_; lean_object* v_rightCount_3025_; lean_object* v_rightIndex_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3039_; 
v_leftCount_3024_ = lean_ctor_get(v_val_3020_, 0);
v_rightCount_3025_ = lean_ctor_get(v_val_3020_, 2);
v_rightIndex_3026_ = lean_ctor_get(v_val_3020_, 3);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_val_3020_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; 
v_unused_3040_ = lean_ctor_get(v_val_3020_, 1);
lean_dec(v_unused_3040_);
v___x_3028_ = v_val_3020_;
v_isShared_3029_ = v_isSharedCheck_3039_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_rightIndex_3026_);
lean_inc(v_rightCount_3025_);
lean_inc(v_leftCount_3024_);
lean_dec(v_val_3020_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3039_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3033_; 
v___x_3030_ = lean_unsigned_to_nat(1u);
v___x_3031_ = lean_nat_add(v_leftCount_3024_, v___x_3030_);
lean_dec(v_leftCount_3024_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v_index_3011_);
v___x_3033_ = v___x_3022_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_index_3011_);
v___x_3033_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3035_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v___x_3033_);
lean_ctor_set(v___x_3028_, 0, v___x_3031_);
v___x_3035_ = v___x_3028_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3037_, 2, v_rightCount_3025_);
lean_ctor_set(v_reuseFailAlloc_3037_, 3, v_rightIndex_3026_);
v___x_3035_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3010_, v_val_3012_, v___x_3035_);
return v___x_3036_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(lean_object* v_upperBound_3042_, lean_object* v_fst_3043_, lean_object* v___x_3044_, lean_object* v_fst_3045_, lean_object* v_a_3046_, lean_object* v_b_3047_){
_start:
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_nat_dec_lt(v_a_3046_, v_upperBound_3042_);
if (v___x_3048_ == 0)
{
lean_dec(v_a_3046_);
return v_b_3047_;
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3049_ = l_Subarray_get___redArg(v_fst_3045_, v_a_3046_);
lean_inc(v_a_3046_);
v___x_3050_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_b_3047_, v_a_3046_, v___x_3049_);
v___x_3051_ = lean_unsigned_to_nat(1u);
v___x_3052_ = lean_nat_add(v_a_3046_, v___x_3051_);
lean_dec(v_a_3046_);
v_a_3046_ = v___x_3052_;
v_b_3047_ = v___x_3050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg___boxed(lean_object* v_upperBound_3054_, lean_object* v_fst_3055_, lean_object* v___x_3056_, lean_object* v_fst_3057_, lean_object* v_a_3058_, lean_object* v_b_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_3054_, v_fst_3055_, v___x_3056_, v_fst_3057_, v_a_3058_, v_b_3059_);
lean_dec_ref(v_fst_3057_);
lean_dec(v___x_3056_);
lean_dec_ref(v_fst_3055_);
lean_dec(v_upperBound_3054_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(lean_object* v_x_3061_, lean_object* v_x_3062_){
_start:
{
if (lean_obj_tag(v_x_3062_) == 0)
{
lean_inc(v_x_3061_);
return v_x_3061_;
}
else
{
lean_object* v_key_3063_; lean_object* v_value_3064_; lean_object* v_tail_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v_key_3063_ = lean_ctor_get(v_x_3062_, 0);
v_value_3064_ = lean_ctor_get(v_x_3062_, 1);
v_tail_3065_ = lean_ctor_get(v_x_3062_, 2);
v___x_3066_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3061_, v_tail_3065_);
lean_inc(v_value_3064_);
lean_inc(v_key_3063_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v_key_3063_);
lean_ctor_set(v___x_3067_, 1, v_value_3064_);
v___x_3068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v___x_3066_);
return v___x_3068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15___boxed(lean_object* v_x_3069_, lean_object* v_x_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_x_3069_, v_x_3070_);
lean_dec(v_x_3070_);
lean_dec(v_x_3069_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(lean_object* v_as_3072_, size_t v_i_3073_, size_t v_stop_3074_, lean_object* v_b_3075_){
_start:
{
uint8_t v___x_3076_; 
v___x_3076_ = lean_usize_dec_eq(v_i_3073_, v_stop_3074_);
if (v___x_3076_ == 0)
{
size_t v___x_3077_; size_t v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3077_ = ((size_t)1ULL);
v___x_3078_ = lean_usize_sub(v_i_3073_, v___x_3077_);
v___x_3079_ = lean_array_uget_borrowed(v_as_3072_, v___x_3078_);
v___x_3080_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__15(v_b_3075_, v___x_3079_);
lean_dec(v_b_3075_);
v_i_3073_ = v___x_3078_;
v_b_3075_ = v___x_3080_;
goto _start;
}
else
{
return v_b_3075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16___boxed(lean_object* v_as_3082_, lean_object* v_i_3083_, lean_object* v_stop_3084_, lean_object* v_b_3085_){
_start:
{
size_t v_i_boxed_3086_; size_t v_stop_boxed_3087_; lean_object* v_res_3088_; 
v_i_boxed_3086_ = lean_unbox_usize(v_i_3083_);
lean_dec(v_i_3083_);
v_stop_boxed_3087_ = lean_unbox_usize(v_stop_3084_);
lean_dec(v_stop_3084_);
v_res_3088_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_as_3082_, v_i_boxed_3086_, v_stop_boxed_3087_, v_b_3085_);
lean_dec_ref(v_as_3082_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(lean_object* v_left_3089_, lean_object* v_right_3090_, lean_object* v_pref_3091_){
_start:
{
lean_object* v_start_3092_; lean_object* v_stop_3093_; lean_object* v_i_3094_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_start_3092_ = lean_ctor_get(v_left_3089_, 1);
v_stop_3093_ = lean_ctor_get(v_left_3089_, 2);
v_i_3094_ = lean_array_get_size(v_pref_3091_);
v___x_3100_ = lean_nat_sub(v_stop_3093_, v_start_3092_);
v___x_3101_ = lean_nat_dec_lt(v_i_3094_, v___x_3100_);
lean_dec(v___x_3100_);
if (v___x_3101_ == 0)
{
goto v___jp_3095_;
}
else
{
lean_object* v_start_3102_; lean_object* v_stop_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v_start_3102_ = lean_ctor_get(v_right_3090_, 1);
v_stop_3103_ = lean_ctor_get(v_right_3090_, 2);
v___x_3104_ = lean_nat_sub(v_stop_3103_, v_start_3102_);
v___x_3105_ = lean_nat_dec_lt(v_i_3094_, v___x_3104_);
lean_dec(v___x_3104_);
if (v___x_3105_ == 0)
{
goto v___jp_3095_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3106_ = l_Subarray_get___redArg(v_left_3089_, v_i_3094_);
v___x_3107_ = l_Subarray_get___redArg(v_right_3090_, v_i_3094_);
v___x_3108_ = lean_string_dec_eq(v___x_3106_, v___x_3107_);
lean_dec(v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec(v___x_3106_);
v___x_3109_ = l_Subarray_drop___redArg(v_left_3089_, v_i_3094_);
v___x_3110_ = l_Subarray_drop___redArg(v_right_3090_, v_i_3094_);
v___x_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3109_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v_pref_3091_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
return v___x_3112_;
}
else
{
lean_object* v___x_3113_; 
v___x_3113_ = lean_array_push(v_pref_3091_, v___x_3106_);
v_pref_3091_ = v___x_3113_;
goto _start;
}
}
}
v___jp_3095_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3096_ = l_Subarray_drop___redArg(v_left_3089_, v_i_3094_);
v___x_3097_ = l_Subarray_drop___redArg(v_right_3090_, v_i_3094_);
v___x_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3099_, 0, v_pref_3091_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
return v___x_3099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(lean_object* v_left_3117_, lean_object* v_right_3118_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3120_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12_spec__16(v_left_3117_, v_right_3118_, v___x_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(lean_object* v_a_3121_, lean_object* v_b_3122_){
_start:
{
lean_object* v_array_3123_; lean_object* v_start_3124_; lean_object* v_stop_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3138_; 
v_array_3123_ = lean_ctor_get(v_a_3121_, 0);
v_start_3124_ = lean_ctor_get(v_a_3121_, 1);
v_stop_3125_ = lean_ctor_get(v_a_3121_, 2);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_a_3121_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3127_ = v_a_3121_;
v_isShared_3128_ = v_isSharedCheck_3138_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_stop_3125_);
lean_inc(v_start_3124_);
lean_inc(v_array_3123_);
lean_dec(v_a_3121_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3138_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
uint8_t v___x_3129_; 
v___x_3129_ = lean_nat_dec_lt(v_start_3124_, v_stop_3125_);
if (v___x_3129_ == 0)
{
lean_del_object(v___x_3127_);
lean_dec(v_stop_3125_);
lean_dec(v_start_3124_);
lean_dec_ref(v_array_3123_);
return v_b_3122_;
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3130_ = lean_unsigned_to_nat(1u);
v___x_3131_ = lean_nat_add(v_start_3124_, v___x_3130_);
lean_inc_ref(v_array_3123_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 1, v___x_3131_);
v___x_3133_ = v___x_3127_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_array_3123_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v___x_3131_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_stop_3125_);
v___x_3133_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_array_fget(v_array_3123_, v_start_3124_);
lean_dec(v_start_3124_);
lean_dec_ref(v_array_3123_);
v___x_3135_ = lean_array_push(v_b_3122_, v___x_3134_);
v_a_3121_ = v___x_3133_;
v_b_3122_ = v___x_3135_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(lean_object* v_left_3139_, lean_object* v_right_3140_, lean_object* v_i_3141_){
_start:
{
lean_object* v_start_3142_; lean_object* v_stop_3143_; lean_object* v___x_3144_; uint8_t v___x_3158_; 
v_start_3142_ = lean_ctor_get(v_left_3139_, 1);
v_stop_3143_ = lean_ctor_get(v_left_3139_, 2);
v___x_3144_ = lean_nat_sub(v_stop_3143_, v_start_3142_);
v___x_3158_ = lean_nat_dec_lt(v_i_3141_, v___x_3144_);
if (v___x_3158_ == 0)
{
goto v___jp_3145_;
}
else
{
lean_object* v_start_3159_; lean_object* v_stop_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v_start_3159_ = lean_ctor_get(v_right_3140_, 1);
v_stop_3160_ = lean_ctor_get(v_right_3140_, 2);
v___x_3161_ = lean_nat_sub(v_stop_3160_, v_start_3159_);
v___x_3162_ = lean_nat_dec_lt(v_i_3141_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_dec(v___x_3161_);
goto v___jp_3145_;
}
else
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v___x_3163_ = lean_nat_sub(v___x_3144_, v_i_3141_);
lean_dec(v___x_3144_);
v___x_3164_ = lean_unsigned_to_nat(1u);
v___x_3165_ = lean_nat_sub(v___x_3163_, v___x_3164_);
v___x_3166_ = l_Subarray_get___redArg(v_left_3139_, v___x_3165_);
lean_dec(v___x_3165_);
v___x_3167_ = lean_nat_sub(v___x_3161_, v_i_3141_);
lean_dec(v___x_3161_);
v___x_3168_ = lean_nat_sub(v___x_3167_, v___x_3164_);
v___x_3169_ = l_Subarray_get___redArg(v_right_3140_, v___x_3168_);
lean_dec(v___x_3168_);
v___x_3170_ = lean_string_dec_eq(v___x_3166_, v___x_3169_);
lean_dec(v___x_3169_);
lean_dec(v___x_3166_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_dec(v_i_3141_);
lean_inc_ref(v_left_3139_);
v___x_3171_ = l_Subarray_take___redArg(v_left_3139_, v___x_3163_);
v___x_3172_ = l_Subarray_take___redArg(v_right_3140_, v___x_3167_);
lean_dec(v___x_3167_);
v___x_3173_ = l_Subarray_drop___redArg(v_left_3139_, v___x_3163_);
lean_dec(v___x_3163_);
v___x_3174_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3175_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3173_, v___x_3174_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3172_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3171_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
return v___x_3177_;
}
else
{
lean_object* v___x_3178_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3163_);
v___x_3178_ = lean_nat_add(v_i_3141_, v___x_3164_);
lean_dec(v_i_3141_);
v_i_3141_ = v___x_3178_;
goto _start;
}
}
}
v___jp_3145_:
{
lean_object* v_start_3146_; lean_object* v_stop_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_start_3146_ = lean_ctor_get(v_right_3140_, 1);
v_stop_3147_ = lean_ctor_get(v_right_3140_, 2);
v___x_3148_ = lean_nat_sub(v___x_3144_, v_i_3141_);
lean_dec(v___x_3144_);
lean_inc_ref(v_left_3139_);
v___x_3149_ = l_Subarray_take___redArg(v_left_3139_, v___x_3148_);
v___x_3150_ = lean_nat_sub(v_stop_3147_, v_start_3146_);
v___x_3151_ = lean_nat_sub(v___x_3150_, v_i_3141_);
lean_dec(v_i_3141_);
lean_dec(v___x_3150_);
v___x_3152_ = l_Subarray_take___redArg(v_right_3140_, v___x_3151_);
lean_dec(v___x_3151_);
v___x_3153_ = l_Subarray_drop___redArg(v_left_3139_, v___x_3148_);
lean_dec(v___x_3148_);
v___x_3154_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12___closed__0));
v___x_3155_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v___x_3153_, v___x_3154_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3152_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3149_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
return v___x_3157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(lean_object* v_left_3180_, lean_object* v_right_3181_){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18(v_left_3180_, v_right_3181_, v___x_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(lean_object* v_as_x27_3184_, lean_object* v_b_3185_){
_start:
{
if (lean_obj_tag(v_as_x27_3184_) == 0)
{
return v_b_3185_;
}
else
{
lean_object* v_head_3186_; lean_object* v_snd_3187_; lean_object* v_leftIndex_3188_; 
v_head_3186_ = lean_ctor_get(v_as_x27_3184_, 0);
v_snd_3187_ = lean_ctor_get(v_head_3186_, 1);
v_leftIndex_3188_ = lean_ctor_get(v_snd_3187_, 1);
if (lean_obj_tag(v_leftIndex_3188_) == 1)
{
lean_object* v_rightIndex_3189_; 
v_rightIndex_3189_ = lean_ctor_get(v_snd_3187_, 3);
if (lean_obj_tag(v_rightIndex_3189_) == 1)
{
if (lean_obj_tag(v_b_3185_) == 0)
{
lean_object* v_tail_3190_; lean_object* v_fst_3191_; lean_object* v_leftCount_3192_; lean_object* v_rightCount_3193_; lean_object* v_val_3194_; lean_object* v_val_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v_tail_3190_ = lean_ctor_get(v_as_x27_3184_, 1);
v_fst_3191_ = lean_ctor_get(v_head_3186_, 0);
v_leftCount_3192_ = lean_ctor_get(v_snd_3187_, 0);
v_rightCount_3193_ = lean_ctor_get(v_snd_3187_, 2);
v_val_3194_ = lean_ctor_get(v_leftIndex_3188_, 0);
v_val_3195_ = lean_ctor_get(v_rightIndex_3189_, 0);
v___x_3196_ = lean_nat_add(v_leftCount_3192_, v_rightCount_3193_);
lean_inc(v_val_3195_);
lean_inc(v_val_3194_);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v_val_3194_);
lean_ctor_set(v___x_3197_, 1, v_val_3195_);
lean_inc(v_fst_3191_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_fst_3191_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3196_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
v_as_x27_3184_ = v_tail_3190_;
v_b_3185_ = v___x_3200_;
goto _start;
}
else
{
lean_object* v_val_3202_; lean_object* v_tail_3203_; lean_object* v_fst_3204_; lean_object* v_leftCount_3205_; lean_object* v_rightCount_3206_; lean_object* v_val_3207_; lean_object* v_val_3208_; lean_object* v_fst_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3230_; 
v_val_3202_ = lean_ctor_get(v_b_3185_, 0);
lean_inc(v_val_3202_);
v_tail_3203_ = lean_ctor_get(v_as_x27_3184_, 1);
v_fst_3204_ = lean_ctor_get(v_head_3186_, 0);
v_leftCount_3205_ = lean_ctor_get(v_snd_3187_, 0);
v_rightCount_3206_ = lean_ctor_get(v_snd_3187_, 2);
v_val_3207_ = lean_ctor_get(v_leftIndex_3188_, 0);
v_val_3208_ = lean_ctor_get(v_rightIndex_3189_, 0);
v_fst_3209_ = lean_ctor_get(v_val_3202_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v_val_3202_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; 
v_unused_3231_ = lean_ctor_get(v_val_3202_, 1);
lean_dec(v_unused_3231_);
v___x_3211_ = v_val_3202_;
v_isShared_3212_ = v_isSharedCheck_3230_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_fst_3209_);
lean_dec(v_val_3202_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3230_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = lean_nat_add(v_leftCount_3205_, v_rightCount_3206_);
v___x_3214_ = lean_nat_dec_lt(v___x_3213_, v_fst_3209_);
lean_dec(v_fst_3209_);
if (v___x_3214_ == 0)
{
lean_dec(v___x_3213_);
lean_del_object(v___x_3211_);
v_as_x27_3184_ = v_tail_3203_;
goto _start;
}
else
{
lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3228_; 
v_isSharedCheck_3228_ = !lean_is_exclusive(v_b_3185_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v_b_3185_, 0);
lean_dec(v_unused_3229_);
v___x_3217_ = v_b_3185_;
v_isShared_3218_ = v_isSharedCheck_3228_;
goto v_resetjp_3216_;
}
else
{
lean_dec(v_b_3185_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3228_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
lean_inc(v_val_3208_);
lean_inc(v_val_3207_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 1, v_val_3208_);
lean_ctor_set(v___x_3211_, 0, v_val_3207_);
v___x_3220_ = v___x_3211_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_val_3207_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_val_3208_);
v___x_3220_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
lean_inc(v_fst_3204_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v_fst_3204_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3213_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3222_);
v___x_3224_ = v___x_3217_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
v_as_x27_3184_ = v_tail_3203_;
v_b_3185_ = v___x_3224_;
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
lean_object* v_tail_3232_; 
v_tail_3232_ = lean_ctor_get(v_as_x27_3184_, 1);
v_as_x27_3184_ = v_tail_3232_;
goto _start;
}
}
else
{
lean_object* v_tail_3234_; 
v_tail_3234_ = lean_ctor_get(v_as_x27_3184_, 1);
v_as_x27_3184_ = v_tail_3234_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg___boxed(lean_object* v_as_x27_3236_, lean_object* v_b_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3236_, v_b_3237_);
lean_dec(v_as_x27_3236_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(lean_object* v_histogram_3239_, lean_object* v_index_3240_, lean_object* v_val_3241_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_histogram_3239_, v_val_3241_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3243_ = lean_unsigned_to_nat(0u);
v___x_3244_ = lean_box(0);
v___x_3245_ = lean_unsigned_to_nat(1u);
v___x_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_index_3240_);
v___x_3247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3243_);
lean_ctor_set(v___x_3247_, 1, v___x_3244_);
lean_ctor_set(v___x_3247_, 2, v___x_3245_);
lean_ctor_set(v___x_3247_, 3, v___x_3246_);
v___x_3248_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3239_, v_val_3241_, v___x_3247_);
return v___x_3248_;
}
else
{
lean_object* v_val_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3270_; 
v_val_3249_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3251_ = v___x_3242_;
v_isShared_3252_ = v_isSharedCheck_3270_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_val_3249_);
lean_dec(v___x_3242_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3270_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v_leftCount_3253_; lean_object* v_leftIndex_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3267_; 
v_leftCount_3253_ = lean_ctor_get(v_val_3249_, 0);
v_leftIndex_3254_ = lean_ctor_get(v_val_3249_, 1);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_val_3249_);
if (v_isSharedCheck_3267_ == 0)
{
lean_object* v_unused_3268_; lean_object* v_unused_3269_; 
v_unused_3268_ = lean_ctor_get(v_val_3249_, 3);
lean_dec(v_unused_3268_);
v_unused_3269_ = lean_ctor_get(v_val_3249_, 2);
lean_dec(v_unused_3269_);
v___x_3256_ = v_val_3249_;
v_isShared_3257_ = v_isSharedCheck_3267_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_leftIndex_3254_);
lean_inc(v_leftCount_3253_);
lean_dec(v_val_3249_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3267_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3258_ = lean_unsigned_to_nat(1u);
v___x_3259_ = lean_nat_add(v_leftCount_3253_, v___x_3258_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v_index_3240_);
v___x_3261_ = v___x_3251_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_index_3240_);
v___x_3261_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3263_; 
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 3, v___x_3261_);
lean_ctor_set(v___x_3256_, 2, v___x_3259_);
v___x_3263_ = v___x_3256_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_leftCount_3253_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_leftIndex_3254_);
lean_ctor_set(v_reuseFailAlloc_3265_, 2, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3265_, 3, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_histogram_3239_, v_val_3241_, v___x_3263_);
return v___x_3264_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(lean_object* v_upperBound_3271_, lean_object* v___x_3272_, lean_object* v_fst_3273_, lean_object* v___x_3274_, lean_object* v_a_3275_, lean_object* v_b_3276_){
_start:
{
uint8_t v___x_3277_; 
v___x_3277_ = lean_nat_dec_lt(v_a_3275_, v_upperBound_3271_);
if (v___x_3277_ == 0)
{
lean_dec(v_a_3275_);
return v_b_3276_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3278_ = l_Subarray_get___redArg(v_fst_3273_, v_a_3275_);
lean_inc(v_a_3275_);
v___x_3279_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_b_3276_, v_a_3275_, v___x_3278_);
v___x_3280_ = lean_unsigned_to_nat(1u);
v___x_3281_ = lean_nat_add(v_a_3275_, v___x_3280_);
lean_dec(v_a_3275_);
v_a_3275_ = v___x_3281_;
v_b_3276_ = v___x_3279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg___boxed(lean_object* v_upperBound_3283_, lean_object* v___x_3284_, lean_object* v_fst_3285_, lean_object* v___x_3286_, lean_object* v_a_3287_, lean_object* v_b_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3283_, v___x_3284_, v_fst_3285_, v___x_3286_, v_a_3287_, v_b_3288_);
lean_dec(v___x_3286_);
lean_dec_ref(v_fst_3285_);
lean_dec(v___x_3284_);
lean_dec(v_upperBound_3283_);
return v_res_3289_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = lean_box(0);
v___x_3291_ = lean_unsigned_to_nat(16u);
v___x_3292_ = lean_mk_array(v___x_3291_, v___x_3290_);
return v___x_3292_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v_hist_3295_; 
v___x_3293_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__0);
v___x_3294_ = lean_unsigned_to_nat(0u);
v_hist_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3295_, 0, v___x_3294_);
lean_ctor_set(v_hist_3295_, 1, v___x_3293_);
return v_hist_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v_left_3296_, lean_object* v_right_3297_){
_start:
{
lean_object* v___x_3298_; lean_object* v_snd_3299_; lean_object* v_fst_3300_; lean_object* v_fst_3301_; lean_object* v_snd_3302_; lean_object* v___x_3303_; lean_object* v_snd_3304_; lean_object* v_fst_3305_; lean_object* v_fst_3306_; lean_object* v_snd_3307_; lean_object* v_start_3308_; lean_object* v_stop_3309_; lean_object* v___x_3310_; lean_object* v_hist_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v_start_3314_; lean_object* v_stop_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v_buckets_3318_; lean_object* v___x_3319_; lean_object* v___y_3321_; lean_object* v___x_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
v___x_3298_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__12(v_left_3296_, v_right_3297_);
v_snd_3299_ = lean_ctor_get(v___x_3298_, 1);
lean_inc(v_snd_3299_);
v_fst_3300_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_fst_3300_);
lean_dec_ref(v___x_3298_);
v_fst_3301_ = lean_ctor_get(v_snd_3299_, 0);
lean_inc(v_fst_3301_);
v_snd_3302_ = lean_ctor_get(v_snd_3299_, 1);
lean_inc(v_snd_3302_);
lean_dec(v_snd_3299_);
v___x_3303_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13(v_fst_3301_, v_snd_3302_);
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
v_start_3308_ = lean_ctor_get(v_fst_3305_, 1);
v_stop_3309_ = lean_ctor_get(v_fst_3305_, 2);
v___x_3310_ = lean_unsigned_to_nat(0u);
v_hist_3311_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___closed__1);
v___x_3312_ = lean_nat_sub(v_stop_3309_, v_start_3308_);
v___x_3313_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v___x_3312_, v_fst_3306_, v___x_3312_, v_fst_3305_, v___x_3310_, v_hist_3311_);
v_start_3314_ = lean_ctor_get(v_fst_3306_, 1);
v_stop_3315_ = lean_ctor_get(v_fst_3306_, 2);
v___x_3316_ = lean_nat_sub(v_stop_3315_, v_start_3314_);
v___x_3317_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v___x_3316_, v___x_3316_, v_fst_3306_, v___x_3312_, v___x_3310_, v___x_3313_);
lean_dec(v___x_3312_);
lean_dec(v___x_3316_);
v_buckets_3318_ = lean_ctor_get(v___x_3317_, 1);
lean_inc_ref(v_buckets_3318_);
lean_dec_ref(v___x_3317_);
v___x_3319_ = lean_box(0);
v___x_3347_ = lean_box(0);
v___x_3348_ = lean_array_get_size(v_buckets_3318_);
v___x_3349_ = lean_nat_dec_lt(v___x_3310_, v___x_3348_);
if (v___x_3349_ == 0)
{
lean_dec_ref(v_buckets_3318_);
v___y_3321_ = v___x_3347_;
goto v___jp_3320_;
}
else
{
size_t v___x_3350_; size_t v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = lean_usize_of_nat(v___x_3348_);
v___x_3351_ = ((size_t)0ULL);
v___x_3352_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__16(v_buckets_3318_, v___x_3350_, v___x_3351_, v___x_3347_);
lean_dec_ref(v_buckets_3318_);
v___y_3321_ = v___x_3352_;
goto v___jp_3320_;
}
v___jp_3320_:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v___y_3321_, v___x_3319_);
lean_dec(v___y_3321_);
if (lean_obj_tag(v___x_3322_) == 1)
{
lean_object* v_val_3323_; lean_object* v_snd_3324_; lean_object* v_snd_3325_; lean_object* v_fst_3326_; lean_object* v_fst_3327_; lean_object* v_snd_3328_; lean_object* v___x_3329_; lean_object* v_fst_3330_; lean_object* v_snd_3331_; lean_object* v___x_3332_; lean_object* v_fst_3333_; lean_object* v_snd_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v_val_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_val_3323_);
lean_dec_ref_known(v___x_3322_, 1);
v_snd_3324_ = lean_ctor_get(v_val_3323_, 1);
lean_inc(v_snd_3324_);
lean_dec(v_val_3323_);
v_snd_3325_ = lean_ctor_get(v_snd_3324_, 1);
lean_inc(v_snd_3325_);
v_fst_3326_ = lean_ctor_get(v_snd_3324_, 0);
lean_inc(v_fst_3326_);
lean_dec(v_snd_3324_);
v_fst_3327_ = lean_ctor_get(v_snd_3325_, 0);
lean_inc(v_fst_3327_);
v_snd_3328_ = lean_ctor_get(v_snd_3325_, 1);
lean_inc(v_snd_3328_);
lean_dec(v_snd_3325_);
v___x_3329_ = l_Subarray_split___redArg(v_fst_3305_, v_fst_3327_);
lean_dec(v_fst_3327_);
v_fst_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_fst_3330_);
v_snd_3331_ = lean_ctor_get(v___x_3329_, 1);
lean_inc(v_snd_3331_);
lean_dec_ref(v___x_3329_);
v___x_3332_ = l_Subarray_split___redArg(v_fst_3306_, v_snd_3328_);
lean_dec(v_snd_3328_);
v_fst_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_fst_3333_);
v_snd_3334_ = lean_ctor_get(v___x_3332_, 1);
lean_inc(v_snd_3334_);
lean_dec_ref(v___x_3332_);
v___x_3335_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v_fst_3330_, v_fst_3333_);
v___x_3336_ = l_Array_append___redArg(v_fst_3300_, v___x_3335_);
lean_dec_ref(v___x_3335_);
v___x_3337_ = lean_unsigned_to_nat(1u);
v___x_3338_ = lean_mk_empty_array_with_capacity(v___x_3337_);
v___x_3339_ = lean_array_push(v___x_3338_, v_fst_3326_);
v___x_3340_ = l_Array_append___redArg(v___x_3336_, v___x_3339_);
lean_dec_ref(v___x_3339_);
v___x_3341_ = l_Subarray_drop___redArg(v_snd_3331_, v___x_3337_);
v___x_3342_ = l_Subarray_drop___redArg(v_snd_3334_, v___x_3337_);
v___x_3343_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3341_, v___x_3342_);
v___x_3344_ = l_Array_append___redArg(v___x_3340_, v___x_3343_);
lean_dec_ref(v___x_3343_);
v___x_3345_ = l_Array_append___redArg(v___x_3344_, v_snd_3307_);
lean_dec(v_snd_3307_);
return v___x_3345_;
}
else
{
lean_object* v___x_3346_; 
lean_dec(v___x_3322_);
lean_dec(v_fst_3306_);
lean_dec(v_fst_3305_);
v___x_3346_ = l_Array_append___redArg(v_fst_3300_, v_snd_3307_);
lean_dec(v_snd_3307_);
return v___x_3346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_3353_, lean_object* v_original_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_fst_3356_; lean_object* v_snd_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3376_; 
v_fst_3356_ = lean_ctor_get(v_a_3355_, 0);
v_snd_3357_ = lean_ctor_get(v_a_3355_, 1);
v_isSharedCheck_3376_ = !lean_is_exclusive(v_a_3355_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3359_ = v_a_3355_;
v_isShared_3360_ = v_isSharedCheck_3376_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_snd_3357_);
lean_inc(v_fst_3356_);
lean_dec(v_a_3355_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3376_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
uint8_t v___x_3361_; 
v___x_3361_ = lean_nat_dec_lt(v_snd_3357_, v___x_3353_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3363_; 
if (v_isShared_3360_ == 0)
{
v___x_3363_ = v___x_3359_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_fst_3356_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_snd_3357_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
else
{
uint8_t v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3365_ = 1;
v___x_3366_ = lean_array_fget_borrowed(v_original_3354_, v_snd_3357_);
v___x_3367_ = lean_box(v___x_3365_);
lean_inc(v___x_3366_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v___x_3366_);
lean_ctor_set(v___x_3359_, 0, v___x_3367_);
v___x_3369_ = v___x_3359_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3375_, 1, v___x_3366_);
v___x_3369_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3370_ = lean_array_push(v_fst_3356_, v___x_3369_);
v___x_3371_ = lean_unsigned_to_nat(1u);
v___x_3372_ = lean_nat_add(v_snd_3357_, v___x_3371_);
lean_dec(v_snd_3357_);
v___x_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3370_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
v_a_3355_ = v___x_3373_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_3377_, lean_object* v_original_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3377_, v_original_3378_, v_a_3379_);
lean_dec_ref(v_original_3378_);
lean_dec(v___x_3377_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_3381_, size_t v_i_3382_, lean_object* v_bs_3383_){
_start:
{
uint8_t v___x_3384_; 
v___x_3384_ = lean_usize_dec_lt(v_i_3382_, v_sz_3381_);
if (v___x_3384_ == 0)
{
return v_bs_3383_;
}
else
{
lean_object* v_v_3385_; lean_object* v___x_3386_; lean_object* v_bs_x27_3387_; uint8_t v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; size_t v___x_3391_; size_t v___x_3392_; lean_object* v___x_3393_; 
v_v_3385_ = lean_array_uget(v_bs_3383_, v_i_3382_);
v___x_3386_ = lean_unsigned_to_nat(0u);
v_bs_x27_3387_ = lean_array_uset(v_bs_3383_, v_i_3382_, v___x_3386_);
v___x_3388_ = 0;
v___x_3389_ = lean_box(v___x_3388_);
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_ctor_set(v___x_3390_, 1, v_v_3385_);
v___x_3391_ = ((size_t)1ULL);
v___x_3392_ = lean_usize_add(v_i_3382_, v___x_3391_);
v___x_3393_ = lean_array_uset(v_bs_x27_3387_, v_i_3382_, v___x_3390_);
v_i_3382_ = v___x_3392_;
v_bs_3383_ = v___x_3393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_3395_, lean_object* v_i_3396_, lean_object* v_bs_3397_){
_start:
{
size_t v_sz_boxed_3398_; size_t v_i_boxed_3399_; lean_object* v_res_3400_; 
v_sz_boxed_3398_ = lean_unbox_usize(v_sz_3395_);
lean_dec(v_sz_3395_);
v_i_boxed_3399_ = lean_unbox_usize(v_i_3396_);
lean_dec(v_i_3396_);
v_res_3400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_3398_, v_i_boxed_3399_, v_bs_3397_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_3401_, lean_object* v_edited_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v_fst_3404_; lean_object* v_snd_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3424_; 
v_fst_3404_ = lean_ctor_get(v_a_3403_, 0);
v_snd_3405_ = lean_ctor_get(v_a_3403_, 1);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_a_3403_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3407_ = v_a_3403_;
v_isShared_3408_ = v_isSharedCheck_3424_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_snd_3405_);
lean_inc(v_fst_3404_);
lean_dec(v_a_3403_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3424_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
uint8_t v___x_3409_; 
v___x_3409_ = lean_nat_dec_lt(v_snd_3405_, v___x_3401_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3411_; 
if (v_isShared_3408_ == 0)
{
v___x_3411_ = v___x_3407_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_fst_3404_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_snd_3405_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
else
{
uint8_t v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3413_ = 0;
v___x_3414_ = lean_array_fget_borrowed(v_edited_3402_, v_snd_3405_);
v___x_3415_ = lean_box(v___x_3413_);
lean_inc(v___x_3414_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 1, v___x_3414_);
lean_ctor_set(v___x_3407_, 0, v___x_3415_);
v___x_3417_ = v___x_3407_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v___x_3414_);
v___x_3417_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3418_ = lean_array_push(v_fst_3404_, v___x_3417_);
v___x_3419_ = lean_unsigned_to_nat(1u);
v___x_3420_ = lean_nat_add(v_snd_3405_, v___x_3419_);
lean_dec(v_snd_3405_);
v___x_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3418_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v_a_3403_ = v___x_3421_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_3425_, lean_object* v_edited_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3425_, v_edited_3426_, v_a_3427_);
lean_dec_ref(v_edited_3426_);
lean_dec(v___x_3425_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3429_, size_t v_i_3430_, lean_object* v_bs_3431_){
_start:
{
uint8_t v___x_3432_; 
v___x_3432_ = lean_usize_dec_lt(v_i_3430_, v_sz_3429_);
if (v___x_3432_ == 0)
{
return v_bs_3431_;
}
else
{
lean_object* v_v_3433_; lean_object* v___x_3434_; lean_object* v_bs_x27_3435_; uint8_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; size_t v___x_3439_; size_t v___x_3440_; lean_object* v___x_3441_; 
v_v_3433_ = lean_array_uget(v_bs_3431_, v_i_3430_);
v___x_3434_ = lean_unsigned_to_nat(0u);
v_bs_x27_3435_ = lean_array_uset(v_bs_3431_, v_i_3430_, v___x_3434_);
v___x_3436_ = 1;
v___x_3437_ = lean_box(v___x_3436_);
v___x_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
lean_ctor_set(v___x_3438_, 1, v_v_3433_);
v___x_3439_ = ((size_t)1ULL);
v___x_3440_ = lean_usize_add(v_i_3430_, v___x_3439_);
v___x_3441_ = lean_array_uset(v_bs_x27_3435_, v_i_3430_, v___x_3438_);
v_i_3430_ = v___x_3440_;
v_bs_3431_ = v___x_3441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3443_, lean_object* v_i_3444_, lean_object* v_bs_3445_){
_start:
{
size_t v_sz_boxed_3446_; size_t v_i_boxed_3447_; lean_object* v_res_3448_; 
v_sz_boxed_3446_ = lean_unbox_usize(v_sz_3443_);
lean_dec(v_sz_3443_);
v_i_boxed_3447_ = lean_unbox_usize(v_i_3444_);
lean_dec(v_i_3444_);
v_res_3448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3446_, v_i_boxed_3447_, v_bs_3445_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3456_, lean_object* v_edited_3457_){
_start:
{
lean_object* v_i_3458_; lean_object* v___x_3459_; uint8_t v___x_3460_; 
v_i_3458_ = lean_unsigned_to_nat(0u);
v___x_3459_ = lean_array_get_size(v_original_3456_);
v___x_3460_ = lean_nat_dec_lt(v_i_3458_, v___x_3459_);
if (v___x_3460_ == 0)
{
size_t v_sz_3461_; size_t v___x_3462_; lean_object* v___x_3463_; 
lean_dec_ref(v_original_3456_);
v_sz_3461_ = lean_array_size(v_edited_3457_);
v___x_3462_ = ((size_t)0ULL);
v___x_3463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3461_, v___x_3462_, v_edited_3457_);
return v___x_3463_;
}
else
{
lean_object* v___x_3464_; uint8_t v___x_3465_; 
v___x_3464_ = lean_array_get_size(v_edited_3457_);
v___x_3465_ = lean_nat_dec_lt(v_i_3458_, v___x_3464_);
if (v___x_3465_ == 0)
{
size_t v_sz_3466_; size_t v___x_3467_; lean_object* v___x_3468_; 
lean_dec_ref(v_edited_3457_);
v_sz_3466_ = lean_array_size(v_original_3456_);
v___x_3467_ = ((size_t)0ULL);
v___x_3468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3466_, v___x_3467_, v_original_3456_);
return v___x_3468_;
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v_ds_3471_; lean_object* v___x_3472_; size_t v_sz_3473_; size_t v___x_3474_; lean_object* v___x_3475_; lean_object* v_snd_3476_; lean_object* v_fst_3477_; lean_object* v_fst_3478_; lean_object* v_snd_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3498_; 
lean_inc_ref(v_original_3456_);
v___x_3469_ = l_Array_toSubarray___redArg(v_original_3456_, v_i_3458_, v___x_3459_);
lean_inc_ref(v_edited_3457_);
v___x_3470_ = l_Array_toSubarray___redArg(v_edited_3457_, v_i_3458_, v___x_3464_);
v_ds_3471_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3469_, v___x_3470_);
v___x_3472_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3473_ = lean_array_size(v_ds_3471_);
v___x_3474_ = ((size_t)0ULL);
v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v_edited_3457_, v___x_3464_, v_original_3456_, v___x_3459_, v_ds_3471_, v_sz_3473_, v___x_3474_, v___x_3472_);
lean_dec_ref(v_ds_3471_);
v_snd_3476_ = lean_ctor_get(v___x_3475_, 1);
lean_inc(v_snd_3476_);
v_fst_3477_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_fst_3477_);
lean_dec_ref(v___x_3475_);
v_fst_3478_ = lean_ctor_get(v_snd_3476_, 0);
v_snd_3479_ = lean_ctor_get(v_snd_3476_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_snd_3476_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3481_ = v_snd_3476_;
v_isShared_3482_ = v_isSharedCheck_3498_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_snd_3479_);
lean_inc(v_fst_3478_);
lean_dec(v_snd_3476_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3498_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v_fst_3478_);
lean_ctor_set(v___x_3481_, 0, v_fst_3477_);
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_fst_3477_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_fst_3478_);
v___x_3484_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v___x_3485_; lean_object* v_fst_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3495_; 
v___x_3485_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3459_, v_original_3456_, v___x_3484_);
lean_dec_ref(v_original_3456_);
v_fst_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3495_ == 0)
{
lean_object* v_unused_3496_; 
v_unused_3496_ = lean_ctor_get(v___x_3485_, 1);
lean_dec(v_unused_3496_);
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3495_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_fst_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3495_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 1, v_snd_3479_);
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_fst_3486_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_snd_3479_);
v___x_3491_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; lean_object* v_fst_3493_; 
v___x_3492_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3464_, v_edited_3457_, v___x_3491_);
lean_dec_ref(v_edited_3457_);
v_fst_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_fst_3493_);
lean_dec_ref(v___x_3492_);
return v_fst_3493_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3499_, lean_object* v_x_3500_, lean_object* v_x_3501_){
_start:
{
if (lean_obj_tag(v_x_3500_) == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = l_List_reverse___redArg(v_x_3501_);
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
return v___x_3504_;
}
else
{
lean_object* v_head_3505_; lean_object* v_tail_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3515_; 
v_head_3505_ = lean_ctor_get(v_x_3500_, 0);
v_tail_3506_ = lean_ctor_get(v_x_3500_, 1);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_x_3500_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3508_ = v_x_3500_;
v_isShared_3509_ = v_isSharedCheck_3515_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_tail_3506_);
lean_inc(v_head_3505_);
lean_dec(v_x_3500_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3515_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3512_; 
v___x_3510_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3505_, v___y_3499_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v_x_3501_);
lean_ctor_set(v___x_3508_, 0, v___x_3510_);
v___x_3512_ = v___x_3508_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_x_3501_);
v___x_3512_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
v_x_3500_ = v_tail_3506_;
v_x_3501_ = v___x_3512_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3516_, lean_object* v_x_3517_, lean_object* v_x_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3516_, v_x_3517_, v_x_3518_);
lean_dec(v___y_3516_);
return v_res_3520_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__0));
v___x_3523_ = l_Lean_stringToMessageData(v___x_3522_);
return v___x_3523_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = l_Lean_MessageLog_empty;
v___x_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; uint8_t v___y_3582_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; uint8_t v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; uint8_t v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; uint8_t v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v_dc_x3f_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___x_3787_; uint8_t v___x_3788_; 
v___x_3787_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
lean_inc(v_x_3537_);
v___x_3788_ = l_Lean_Syntax_isOfKind(v_x_3537_, v___x_3787_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; 
lean_dec(v_x_3537_);
v___x_3789_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3789_;
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3790_ = lean_unsigned_to_nat(0u);
v___x_3791_ = l_Lean_Syntax_getArg(v_x_3537_, v___x_3790_);
v___x_3792_ = l_Lean_Syntax_isNone(v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; uint8_t v___x_3794_; 
v___x_3793_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3791_);
v___x_3794_ = l_Lean_Syntax_matchesNull(v___x_3791_, v___x_3793_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3795_; 
lean_dec(v___x_3791_);
lean_dec(v_x_3537_);
v___x_3795_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3795_;
}
else
{
lean_object* v_dc_x3f_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v_dc_x3f_3796_ = l_Lean_Syntax_getArg(v___x_3791_, v___x_3790_);
lean_dec(v___x_3791_);
v___x_3797_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3796_);
v___x_3798_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3796_, v___x_3797_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; 
lean_dec(v_dc_x3f_3796_);
lean_dec(v_x_3537_);
v___x_3799_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3799_;
}
else
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3800_, 0, v_dc_x3f_3796_);
v_dc_x3f_3768_ = v___x_3800_;
v___y_3769_ = v_a_3538_;
v___y_3770_ = v_a_3539_;
goto v___jp_3767_;
}
}
}
else
{
lean_object* v___x_3801_; 
lean_dec(v___x_3791_);
v___x_3801_ = lean_box(0);
v_dc_x3f_3768_ = v___x_3801_;
v___y_3769_ = v_a_3538_;
v___y_3770_ = v_a_3539_;
goto v___jp_3767_;
}
}
v___jp_3541_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3547_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1);
v___x_3548_ = l_Lean_stringToMessageData(v___y_3546_);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3545_, v___x_3549_, v___y_3544_, v___y_3542_);
lean_dec(v___y_3545_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3571_; 
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; 
v_unused_3572_ = lean_ctor_get(v___x_3550_, 0);
lean_dec(v_unused_3572_);
v___x_3552_ = v___x_3550_;
v_isShared_3553_ = v_isSharedCheck_3571_;
goto v_resetjp_3551_;
}
else
{
lean_dec(v___x_3550_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3571_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_Elab_Command_getRef___redArg(v___y_3544_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3560_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3554_, 1);
v___x_3556_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
lean_ctor_set(v___x_3557_, 1, v___y_3543_);
v___x_3558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3558_, 0, v_a_3555_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set_tag(v___x_3552_, 10);
lean_ctor_set(v___x_3552_, 0, v___x_3558_);
v___x_3560_ = v___x_3552_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3561_; 
v___x_3561_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3560_, v___y_3544_, v___y_3542_);
return v___x_3561_;
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_del_object(v___x_3552_);
lean_dec_ref(v___y_3543_);
v_a_3563_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3554_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3554_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3543_);
return v___x_3550_;
}
}
v___jp_3573_:
{
if (v___y_3582_ == 0)
{
lean_object* v___x_3583_; lean_object* v_env_3584_; lean_object* v_scopes_3585_; lean_object* v_usedQuotCtxts_3586_; lean_object* v_nextMacroScope_3587_; lean_object* v_maxRecDepth_3588_; lean_object* v_ngen_3589_; lean_object* v_auxDeclNGen_3590_; lean_object* v_infoState_3591_; lean_object* v_traceState_3592_; lean_object* v_snapshotTasks_3593_; lean_object* v_prevLinterStates_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3620_; 
lean_dec(v___y_3581_);
v___x_3583_ = lean_st_ref_take(v___y_3575_);
v_env_3584_ = lean_ctor_get(v___x_3583_, 0);
v_scopes_3585_ = lean_ctor_get(v___x_3583_, 2);
v_usedQuotCtxts_3586_ = lean_ctor_get(v___x_3583_, 3);
v_nextMacroScope_3587_ = lean_ctor_get(v___x_3583_, 4);
v_maxRecDepth_3588_ = lean_ctor_get(v___x_3583_, 5);
v_ngen_3589_ = lean_ctor_get(v___x_3583_, 6);
v_auxDeclNGen_3590_ = lean_ctor_get(v___x_3583_, 7);
v_infoState_3591_ = lean_ctor_get(v___x_3583_, 8);
v_traceState_3592_ = lean_ctor_get(v___x_3583_, 9);
v_snapshotTasks_3593_ = lean_ctor_get(v___x_3583_, 10);
v_prevLinterStates_3594_ = lean_ctor_get(v___x_3583_, 11);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v___x_3583_, 1);
lean_dec(v_unused_3621_);
v___x_3596_ = v___x_3583_;
v_isShared_3597_ = v_isSharedCheck_3620_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_prevLinterStates_3594_);
lean_inc(v_snapshotTasks_3593_);
lean_inc(v_traceState_3592_);
lean_inc(v_infoState_3591_);
lean_inc(v_auxDeclNGen_3590_);
lean_inc(v_ngen_3589_);
lean_inc(v_maxRecDepth_3588_);
lean_inc(v_nextMacroScope_3587_);
lean_inc(v_usedQuotCtxts_3586_);
lean_inc(v_scopes_3585_);
lean_inc(v_env_3584_);
lean_dec(v___x_3583_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3620_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 1, v___y_3577_);
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_env_3584_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v___y_3577_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_scopes_3585_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v_usedQuotCtxts_3586_);
lean_ctor_set(v_reuseFailAlloc_3619_, 4, v_nextMacroScope_3587_);
lean_ctor_set(v_reuseFailAlloc_3619_, 5, v_maxRecDepth_3588_);
lean_ctor_set(v_reuseFailAlloc_3619_, 6, v_ngen_3589_);
lean_ctor_set(v_reuseFailAlloc_3619_, 7, v_auxDeclNGen_3590_);
lean_ctor_set(v_reuseFailAlloc_3619_, 8, v_infoState_3591_);
lean_ctor_set(v_reuseFailAlloc_3619_, 9, v_traceState_3592_);
lean_ctor_set(v_reuseFailAlloc_3619_, 10, v_snapshotTasks_3593_);
lean_ctor_set(v_reuseFailAlloc_3619_, 11, v_prevLinterStates_3594_);
v___x_3599_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v_scopes_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v_opts_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3600_ = lean_st_ref_set(v___y_3575_, v___x_3599_);
v___x_3601_ = lean_st_ref_get(v___y_3575_);
v_scopes_3602_ = lean_ctor_get(v___x_3601_, 2);
lean_inc(v_scopes_3602_);
lean_dec(v___x_3601_);
v___x_3603_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3604_ = l_List_head_x21___redArg(v___x_3603_, v_scopes_3602_);
lean_dec(v_scopes_3602_);
v_opts_3605_ = lean_ctor_get(v___x_3604_, 1);
lean_inc_ref(v_opts_3605_);
lean_dec(v___x_3604_);
v___x_3606_ = l_Lean_guard__msgs_diff;
v___x_3607_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3605_, v___x_3606_);
lean_dec_ref(v_opts_3605_);
if (v___x_3607_ == 0)
{
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3574_);
lean_inc_ref(v___y_3576_);
v___y_3542_ = v___y_3575_;
v___y_3543_ = v___y_3576_;
v___y_3544_ = v___y_3579_;
v___y_3545_ = v___y_3578_;
v___y_3546_ = v___y_3576_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3608_ = lean_string_utf8_byte_size(v___y_3580_);
lean_inc(v___y_3574_);
lean_inc_ref(v___y_3580_);
v___x_3609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3609_, 0, v___y_3580_);
lean_ctor_set(v___x_3609_, 1, v___y_3574_);
lean_ctor_set(v___x_3609_, 2, v___x_3608_);
v___x_3610_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3609_);
v___x_3611_ = lean_mk_empty_array_with_capacity(v___y_3574_);
lean_inc_ref(v___x_3611_);
v___x_3612_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3580_, v___x_3609_, v___x_3608_, v___x_3610_, v___x_3611_);
lean_dec_ref_known(v___x_3609_, 3);
v___x_3613_ = lean_string_utf8_byte_size(v___y_3576_);
lean_inc_ref_n(v___y_3576_, 2);
v___x_3614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3614_, 0, v___y_3576_);
lean_ctor_set(v___x_3614_, 1, v___y_3574_);
lean_ctor_set(v___x_3614_, 2, v___x_3613_);
v___x_3615_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3614_);
v___x_3616_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3576_, v___x_3614_, v___x_3613_, v___x_3615_, v___x_3611_);
lean_dec_ref_known(v___x_3614_, 3);
v___x_3617_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3612_, v___x_3616_);
v___x_3618_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3617_);
lean_dec_ref(v___x_3617_);
v___y_3542_ = v___y_3575_;
v___y_3543_ = v___y_3576_;
v___y_3544_ = v___y_3579_;
v___y_3545_ = v___y_3578_;
v___y_3546_ = v___x_3618_;
goto v___jp_3541_;
}
}
}
}
else
{
lean_object* v___x_3622_; lean_object* v_env_3623_; lean_object* v_scopes_3624_; lean_object* v_usedQuotCtxts_3625_; lean_object* v_nextMacroScope_3626_; lean_object* v_maxRecDepth_3627_; lean_object* v_ngen_3628_; lean_object* v_auxDeclNGen_3629_; lean_object* v_infoState_3630_; lean_object* v_traceState_3631_; lean_object* v_snapshotTasks_3632_; lean_object* v_prevLinterStates_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3643_; 
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3574_);
v___x_3622_ = lean_st_ref_take(v___y_3575_);
v_env_3623_ = lean_ctor_get(v___x_3622_, 0);
v_scopes_3624_ = lean_ctor_get(v___x_3622_, 2);
v_usedQuotCtxts_3625_ = lean_ctor_get(v___x_3622_, 3);
v_nextMacroScope_3626_ = lean_ctor_get(v___x_3622_, 4);
v_maxRecDepth_3627_ = lean_ctor_get(v___x_3622_, 5);
v_ngen_3628_ = lean_ctor_get(v___x_3622_, 6);
v_auxDeclNGen_3629_ = lean_ctor_get(v___x_3622_, 7);
v_infoState_3630_ = lean_ctor_get(v___x_3622_, 8);
v_traceState_3631_ = lean_ctor_get(v___x_3622_, 9);
v_snapshotTasks_3632_ = lean_ctor_get(v___x_3622_, 10);
v_prevLinterStates_3633_ = lean_ctor_get(v___x_3622_, 11);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3643_ == 0)
{
lean_object* v_unused_3644_; 
v_unused_3644_ = lean_ctor_get(v___x_3622_, 1);
lean_dec(v_unused_3644_);
v___x_3635_ = v___x_3622_;
v_isShared_3636_ = v_isSharedCheck_3643_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_prevLinterStates_3633_);
lean_inc(v_snapshotTasks_3632_);
lean_inc(v_traceState_3631_);
lean_inc(v_infoState_3630_);
lean_inc(v_auxDeclNGen_3629_);
lean_inc(v_ngen_3628_);
lean_inc(v_maxRecDepth_3627_);
lean_inc(v_nextMacroScope_3626_);
lean_inc(v_usedQuotCtxts_3625_);
lean_inc(v_scopes_3624_);
lean_inc(v_env_3623_);
lean_dec(v___x_3622_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3643_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 1, v___y_3581_);
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_env_3623_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v___y_3581_);
lean_ctor_set(v_reuseFailAlloc_3642_, 2, v_scopes_3624_);
lean_ctor_set(v_reuseFailAlloc_3642_, 3, v_usedQuotCtxts_3625_);
lean_ctor_set(v_reuseFailAlloc_3642_, 4, v_nextMacroScope_3626_);
lean_ctor_set(v_reuseFailAlloc_3642_, 5, v_maxRecDepth_3627_);
lean_ctor_set(v_reuseFailAlloc_3642_, 6, v_ngen_3628_);
lean_ctor_set(v_reuseFailAlloc_3642_, 7, v_auxDeclNGen_3629_);
lean_ctor_set(v_reuseFailAlloc_3642_, 8, v_infoState_3630_);
lean_ctor_set(v_reuseFailAlloc_3642_, 9, v_traceState_3631_);
lean_ctor_set(v_reuseFailAlloc_3642_, 10, v_snapshotTasks_3632_);
lean_ctor_set(v_reuseFailAlloc_3642_, 11, v_prevLinterStates_3633_);
v___x_3638_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = lean_st_ref_set(v___y_3575_, v___x_3638_);
v___x_3640_ = lean_box(0);
v___x_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
return v___x_3641_;
}
}
}
}
v___jp_3645_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v_a_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v_str_3668_; lean_object* v_startInclusive_3669_; lean_object* v_endExclusive_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3685_; 
v___x_3658_ = l_Lean_MessageLog_toList(v___y_3647_);
lean_dec(v___y_3647_);
v___x_3659_ = lean_box(0);
v___x_3660_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3657_, v___x_3658_, v___x_3659_);
lean_dec(v___y_3657_);
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref(v___x_3660_);
v___x_3662_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3650_, v_a_3661_);
v___x_3663_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3664_ = l_String_intercalate(v___x_3663_, v___x_3662_);
v___x_3665_ = lean_string_utf8_byte_size(v___x_3664_);
lean_inc(v___y_3646_);
v___x_3666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3664_);
lean_ctor_set(v___x_3666_, 1, v___y_3646_);
lean_ctor_set(v___x_3666_, 2, v___x_3665_);
v___x_3667_ = l_String_Slice_trimAscii(v___x_3666_);
v_str_3668_ = lean_ctor_get(v___x_3667_, 0);
v_startInclusive_3669_ = lean_ctor_get(v___x_3667_, 1);
v_endExclusive_3670_ = lean_ctor_get(v___x_3667_, 2);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3672_ = v___x_3667_;
v_isShared_3673_ = v_isSharedCheck_3685_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_endExclusive_3670_);
lean_inc(v_startInclusive_3669_);
lean_inc(v_str_3668_);
lean_dec(v___x_3667_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3685_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; 
v___x_3674_ = lean_string_utf8_extract(v_str_3668_, v_startInclusive_3669_, v_endExclusive_3670_);
lean_dec(v_endExclusive_3670_);
lean_dec(v_startInclusive_3669_);
lean_dec_ref(v_str_3668_);
if (v___y_3653_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3676_; uint8_t v___x_3677_; 
lean_del_object(v___x_3672_);
lean_inc_ref(v___y_3654_);
v___x_3675_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3656_, v___y_3654_);
lean_inc_ref(v___x_3674_);
v___x_3676_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3656_, v___x_3674_);
v___x_3677_ = lean_string_dec_eq(v___x_3675_, v___x_3676_);
lean_dec_ref(v___x_3676_);
lean_dec_ref(v___x_3675_);
v___y_3574_ = v___y_3646_;
v___y_3575_ = v___y_3648_;
v___y_3576_ = v___x_3674_;
v___y_3577_ = v___y_3649_;
v___y_3578_ = v___y_3651_;
v___y_3579_ = v___y_3652_;
v___y_3580_ = v___y_3654_;
v___y_3581_ = v___y_3655_;
v___y_3582_ = v___x_3677_;
goto v___jp_3573_;
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
lean_inc_ref(v___x_3674_);
v___x_3678_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3656_, v___x_3674_);
lean_inc_ref(v___y_3654_);
v___x_3679_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3656_, v___y_3654_);
v___x_3680_ = lean_string_utf8_byte_size(v___x_3678_);
lean_inc(v___y_3646_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 2, v___x_3680_);
lean_ctor_set(v___x_3672_, 1, v___y_3646_);
lean_ctor_set(v___x_3672_, 0, v___x_3678_);
v___x_3682_ = v___x_3672_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v___y_3646_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
uint8_t v___x_3683_; 
v___x_3683_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3679_, v___x_3682_);
lean_dec_ref(v___x_3682_);
v___y_3574_ = v___y_3646_;
v___y_3575_ = v___y_3648_;
v___y_3576_ = v___x_3674_;
v___y_3577_ = v___y_3649_;
v___y_3578_ = v___y_3651_;
v___y_3579_ = v___y_3652_;
v___y_3580_ = v___y_3654_;
v___y_3581_ = v___y_3655_;
v___y_3582_ = v___x_3683_;
goto v___jp_3573_;
}
}
}
}
v___jp_3686_:
{
lean_object* v___x_3693_; 
v___x_3693_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3691_, v___y_3690_, v___y_3687_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v_filterFn_3695_; uint8_t v_whitespace_3696_; uint8_t v_ordering_3697_; uint8_t v_reportPositions_3698_; uint8_t v_substring_3699_; lean_object* v___x_3700_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
v_filterFn_3695_ = lean_ctor_get(v_a_3694_, 0);
lean_inc_ref(v_filterFn_3695_);
v_whitespace_3696_ = lean_ctor_get_uint8(v_a_3694_, sizeof(void*)*1);
v_ordering_3697_ = lean_ctor_get_uint8(v_a_3694_, sizeof(void*)*1 + 1);
v_reportPositions_3698_ = lean_ctor_get_uint8(v_a_3694_, sizeof(void*)*1 + 2);
v_substring_3699_ = lean_ctor_get_uint8(v_a_3694_, sizeof(void*)*1 + 3);
lean_dec(v_a_3694_);
v___x_3700_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3688_, v___y_3690_, v___y_3687_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v_a_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v_str_3710_; lean_object* v_startInclusive_3711_; lean_object* v_endExclusive_3712_; lean_object* v_fst_3713_; lean_object* v_snd_3714_; lean_object* v_fileMap_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
v___x_3702_ = l_Lean_MessageLog_toList(v_a_3701_);
v___x_3703_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3704_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3695_, v___x_3702_, v___x_3703_);
lean_dec(v___x_3702_);
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref(v___x_3704_);
v___x_3706_ = lean_unsigned_to_nat(0u);
v___x_3707_ = lean_string_utf8_byte_size(v___y_3692_);
v___x_3708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3708_, 0, v___y_3692_);
lean_ctor_set(v___x_3708_, 1, v___x_3706_);
lean_ctor_set(v___x_3708_, 2, v___x_3707_);
v___x_3709_ = l_String_Slice_trimAscii(v___x_3708_);
v_str_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc_ref(v_str_3710_);
v_startInclusive_3711_ = lean_ctor_get(v___x_3709_, 1);
lean_inc(v_startInclusive_3711_);
v_endExclusive_3712_ = lean_ctor_get(v___x_3709_, 2);
lean_inc(v_endExclusive_3712_);
lean_dec_ref(v___x_3709_);
v_fst_3713_ = lean_ctor_get(v_a_3705_, 0);
lean_inc(v_fst_3713_);
v_snd_3714_ = lean_ctor_get(v_a_3705_, 1);
lean_inc(v_snd_3714_);
lean_dec(v_a_3705_);
v_fileMap_3715_ = lean_ctor_get(v___y_3690_, 1);
v___x_3716_ = lean_string_utf8_extract(v_str_3710_, v_startInclusive_3711_, v_endExclusive_3712_);
lean_dec(v_endExclusive_3712_);
lean_dec(v_startInclusive_3711_);
lean_dec_ref(v_str_3710_);
v___x_3717_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3716_);
if (v_reportPositions_3698_ == 0)
{
lean_object* v___x_3718_; 
v___x_3718_ = lean_box(0);
v___y_3646_ = v___x_3706_;
v___y_3647_ = v_fst_3713_;
v___y_3648_ = v___y_3687_;
v___y_3649_ = v_a_3701_;
v___y_3650_ = v_ordering_3697_;
v___y_3651_ = v___y_3689_;
v___y_3652_ = v___y_3690_;
v___y_3653_ = v_substring_3699_;
v___y_3654_ = v___x_3717_;
v___y_3655_ = v_snd_3714_;
v___y_3656_ = v_whitespace_3696_;
v___y_3657_ = v___x_3718_;
goto v___jp_3645_;
}
else
{
uint8_t v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = 0;
v___x_3720_ = l_Lean_Syntax_getPos_x3f(v___y_3689_, v___x_3719_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_box(0);
v___y_3646_ = v___x_3706_;
v___y_3647_ = v_fst_3713_;
v___y_3648_ = v___y_3687_;
v___y_3649_ = v_a_3701_;
v___y_3650_ = v_ordering_3697_;
v___y_3651_ = v___y_3689_;
v___y_3652_ = v___y_3690_;
v___y_3653_ = v_substring_3699_;
v___y_3654_ = v___x_3717_;
v___y_3655_ = v_snd_3714_;
v___y_3656_ = v_whitespace_3696_;
v___y_3657_ = v___x_3721_;
goto v___jp_3645_;
}
else
{
lean_object* v_val_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3731_; 
v_val_3722_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3724_ = v___x_3720_;
v_isShared_3725_ = v_isSharedCheck_3731_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_val_3722_);
lean_dec(v___x_3720_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3731_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3726_; lean_object* v_line_3727_; lean_object* v___x_3729_; 
lean_inc_ref(v_fileMap_3715_);
v___x_3726_ = l_Lean_FileMap_toPosition(v_fileMap_3715_, v_val_3722_);
lean_dec(v_val_3722_);
v_line_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_line_3727_);
lean_dec_ref(v___x_3726_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v_line_3727_);
v___x_3729_ = v___x_3724_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_line_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
v___y_3646_ = v___x_3706_;
v___y_3647_ = v_fst_3713_;
v___y_3648_ = v___y_3687_;
v___y_3649_ = v_a_3701_;
v___y_3650_ = v_ordering_3697_;
v___y_3651_ = v___y_3689_;
v___y_3652_ = v___y_3690_;
v___y_3653_ = v_substring_3699_;
v___y_3654_ = v___x_3717_;
v___y_3655_ = v_snd_3714_;
v___y_3656_ = v_whitespace_3696_;
v___y_3657_ = v___x_3729_;
goto v___jp_3645_;
}
}
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec_ref(v_filterFn_3695_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3689_);
v_a_3732_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3700_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3700_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3689_);
lean_dec(v___y_3688_);
v_a_3740_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3693_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3693_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
v___jp_3748_:
{
if (lean_obj_tag(v___y_3749_) == 0)
{
lean_object* v___x_3755_; 
v___x_3755_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_3687_ = v___y_3750_;
v___y_3688_ = v___y_3751_;
v___y_3689_ = v___y_3752_;
v___y_3690_ = v___y_3753_;
v___y_3691_ = v___y_3754_;
v___y_3692_ = v___x_3755_;
goto v___jp_3686_;
}
else
{
lean_object* v_val_3756_; lean_object* v___x_3757_; 
v_val_3756_ = lean_ctor_get(v___y_3749_, 0);
lean_inc(v_val_3756_);
lean_dec_ref_known(v___y_3749_, 1);
v___x_3757_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3756_, v___y_3753_, v___y_3750_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3757_, 1);
v___y_3687_ = v___y_3750_;
v___y_3688_ = v___y_3751_;
v___y_3689_ = v___y_3752_;
v___y_3690_ = v___y_3753_;
v___y_3691_ = v___y_3754_;
v___y_3692_ = v_a_3758_;
goto v___jp_3686_;
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec(v___y_3754_);
lean_dec(v___y_3752_);
lean_dec(v___y_3751_);
v_a_3759_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3757_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3757_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
}
v___jp_3767_:
{
lean_object* v___x_3771_; lean_object* v_tk_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3771_ = lean_unsigned_to_nat(1u);
v_tk_3772_ = l_Lean_Syntax_getArg(v_x_3537_, v___x_3771_);
v___x_3773_ = lean_unsigned_to_nat(2u);
v___x_3774_ = l_Lean_Syntax_getArg(v_x_3537_, v___x_3773_);
v___x_3775_ = lean_unsigned_to_nat(4u);
v___x_3776_ = l_Lean_Syntax_getArg(v_x_3537_, v___x_3775_);
lean_dec(v_x_3537_);
v___x_3777_ = l_Lean_Syntax_getOptional_x3f(v___x_3774_);
lean_dec(v___x_3774_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_box(0);
v___y_3749_ = v_dc_x3f_3768_;
v___y_3750_ = v___y_3770_;
v___y_3751_ = v___x_3776_;
v___y_3752_ = v_tk_3772_;
v___y_3753_ = v___y_3769_;
v___y_3754_ = v___x_3778_;
goto v___jp_3748_;
}
else
{
lean_object* v_val_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
v_val_3779_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3777_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_val_3779_);
lean_dec(v___x_3777_);
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
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_val_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
v___y_3749_ = v_dc_x3f_3768_;
v___y_3750_ = v___y_3770_;
v___y_3751_ = v___x_3776_;
v___y_3752_ = v_tk_3772_;
v___y_3753_ = v___y_3769_;
v___y_3754_ = v___x_3784_;
goto v___jp_3748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3802_, v_a_3803_, v_a_3804_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3807_, lean_object* v_as_3808_, lean_object* v_as_x27_3809_, lean_object* v_b_3810_, lean_object* v_a_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v___x_3815_; 
v___x_3815_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3807_, v_as_x27_3809_, v_b_3810_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3816_, lean_object* v_as_3817_, lean_object* v_as_x27_3818_, lean_object* v_b_3819_, lean_object* v_a_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3816_, v_as_3817_, v_as_x27_3818_, v_b_3819_, v_a_3820_, v___y_3821_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v_as_x27_3818_);
lean_dec(v_as_3817_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3825_, lean_object* v_x_3826_, lean_object* v_x_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3825_, v_x_3826_, v_x_3827_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3832_, lean_object* v_x_3833_, lean_object* v_x_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3832_, v_x_3833_, v_x_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3832_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3839_, v___y_3841_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3844_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3849_, lean_object* v___x_3850_, lean_object* v___x_3851_, lean_object* v_inst_3852_, lean_object* v_R_3853_, lean_object* v_a_3854_, lean_object* v_b_3855_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3849_, v___x_3850_, v___x_3851_, v_a_3854_, v_b_3855_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3857_, lean_object* v___x_3858_, lean_object* v___x_3859_, lean_object* v_inst_3860_, lean_object* v_R_3861_, lean_object* v_a_3862_, lean_object* v_b_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3857_, v___x_3858_, v___x_3859_, v_inst_3860_, v_R_3861_, v_a_3862_, v_b_3863_);
lean_dec_ref(v___x_3858_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v___x_3869_; 
v___x_3869_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3865_, v___y_3867_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3875_, lean_object* v___x_3876_, lean_object* v___x_3877_, lean_object* v_inst_3878_, lean_object* v_R_3879_, lean_object* v_a_3880_, lean_object* v_b_3881_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3875_, v___x_3876_, v___x_3877_, v_a_3880_, v_b_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3883_, lean_object* v___x_3884_, lean_object* v___x_3885_, lean_object* v_inst_3886_, lean_object* v_R_3887_, lean_object* v_a_3888_, lean_object* v_b_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3883_, v___x_3884_, v___x_3885_, v_inst_3886_, v_R_3887_, v_a_3888_, v_b_3889_);
lean_dec_ref(v___x_3884_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v_original_3891_, lean_object* v___x_3892_, lean_object* v_a_3893_, lean_object* v_inst_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v_original_3891_, v___x_3892_, v_a_3893_, v_a_3895_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v_original_3897_, lean_object* v___x_3898_, lean_object* v_a_3899_, lean_object* v_inst_3900_, lean_object* v_a_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v_original_3897_, v___x_3898_, v_a_3899_, v_inst_3900_, v_a_3901_);
lean_dec_ref(v_a_3899_);
lean_dec(v___x_3898_);
lean_dec_ref(v_original_3897_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_edited_3903_, lean_object* v___x_3904_, lean_object* v_a_3905_, lean_object* v_inst_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___redArg(v_edited_3903_, v___x_3904_, v_a_3905_, v_a_3907_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___boxed(lean_object* v_edited_3909_, lean_object* v___x_3910_, lean_object* v_a_3911_, lean_object* v_inst_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_edited_3909_, v___x_3910_, v_a_3911_, v_inst_3912_, v_a_3913_);
lean_dec_ref(v_a_3911_);
lean_dec(v___x_3910_);
lean_dec_ref(v_edited_3909_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3915_, lean_object* v_original_3916_, lean_object* v_inst_3917_, lean_object* v_a_3918_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3915_, v_original_3916_, v_a_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3920_, lean_object* v_original_3921_, lean_object* v_inst_3922_, lean_object* v_a_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3920_, v_original_3921_, v_inst_3922_, v_a_3923_);
lean_dec_ref(v_original_3921_);
lean_dec(v___x_3920_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3925_, lean_object* v_edited_3926_, lean_object* v_inst_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3925_, v_edited_3926_, v_a_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3930_, lean_object* v_edited_3931_, lean_object* v_inst_3932_, lean_object* v_a_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3930_, v_edited_3931_, v_inst_3932_, v_a_3933_);
lean_dec_ref(v_edited_3931_);
lean_dec(v___x_3930_);
return v_res_3934_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3935_, lean_object* v_inst_3936_, lean_object* v_R_3937_, lean_object* v_a_3938_, uint8_t v_b_3939_, lean_object* v_c_3940_){
_start:
{
uint8_t v___x_3941_; 
v___x_3941_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3935_, v_a_3938_, v_b_3939_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3942_, lean_object* v_inst_3943_, lean_object* v_R_3944_, lean_object* v_a_3945_, lean_object* v_b_3946_, lean_object* v_c_3947_){
_start:
{
uint8_t v_b_boxed_3948_; uint8_t v_res_3949_; lean_object* v_r_3950_; 
v_b_boxed_3948_ = lean_unbox(v_b_3946_);
v_res_3949_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3942_, v_inst_3943_, v_R_3944_, v_a_3945_, v_b_boxed_3948_, v_c_3947_);
lean_dec_ref(v_s_3942_);
v_r_3950_ = lean_box(v_res_3949_);
return v_r_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3951_, lean_object* v_ref_3952_, lean_object* v_msg_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3952_, v_msg_3953_, v___y_3954_, v___y_3955_);
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3958_, lean_object* v_ref_3959_, lean_object* v_msg_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3958_, v_ref_3959_, v_msg_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v_ref_3959_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(lean_object* v_as_3965_, lean_object* v_as_x27_3966_, lean_object* v_b_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v___x_3969_; 
v___x_3969_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___redArg(v_as_x27_3966_, v_b_3967_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14___boxed(lean_object* v_as_3970_, lean_object* v_as_x27_3971_, lean_object* v_b_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__14(v_as_3970_, v_as_x27_3971_, v_b_3972_, v_a_3973_);
lean_dec(v_as_x27_3971_);
lean_dec(v_as_3970_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(lean_object* v_lsize_3975_, lean_object* v_rsize_3976_, lean_object* v_histogram_3977_, lean_object* v_index_3978_, lean_object* v_val_3979_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___redArg(v_histogram_3977_, v_index_3978_, v_val_3979_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17___boxed(lean_object* v_lsize_3981_, lean_object* v_rsize_3982_, lean_object* v_histogram_3983_, lean_object* v_index_3984_, lean_object* v_val_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17(v_lsize_3981_, v_rsize_3982_, v_histogram_3983_, v_index_3984_, v_val_3985_);
lean_dec(v_rsize_3982_);
lean_dec(v_lsize_3981_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(lean_object* v_upperBound_3987_, lean_object* v___x_3988_, lean_object* v_fst_3989_, lean_object* v___x_3990_, lean_object* v_inst_3991_, lean_object* v_R_3992_, lean_object* v_a_3993_, lean_object* v_b_3994_, lean_object* v_c_3995_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___redArg(v_upperBound_3987_, v___x_3988_, v_fst_3989_, v___x_3990_, v_a_3993_, v_b_3994_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18___boxed(lean_object* v_upperBound_3997_, lean_object* v___x_3998_, lean_object* v_fst_3999_, lean_object* v___x_4000_, lean_object* v_inst_4001_, lean_object* v_R_4002_, lean_object* v_a_4003_, lean_object* v_b_4004_, lean_object* v_c_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__18(v_upperBound_3997_, v___x_3998_, v_fst_3999_, v___x_4000_, v_inst_4001_, v_R_4002_, v_a_4003_, v_b_4004_, v_c_4005_);
lean_dec(v___x_4000_);
lean_dec_ref(v_fst_3999_);
lean_dec(v___x_3998_);
lean_dec(v_upperBound_3997_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(lean_object* v_lsize_4007_, lean_object* v_rsize_4008_, lean_object* v_histogram_4009_, lean_object* v_index_4010_, lean_object* v_val_4011_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___redArg(v_histogram_4009_, v_index_4010_, v_val_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19___boxed(lean_object* v_lsize_4013_, lean_object* v_rsize_4014_, lean_object* v_histogram_4015_, lean_object* v_index_4016_, lean_object* v_val_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__19(v_lsize_4013_, v_rsize_4014_, v_histogram_4015_, v_index_4016_, v_val_4017_);
lean_dec(v_rsize_4014_);
lean_dec(v_lsize_4013_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(lean_object* v_upperBound_4019_, lean_object* v_fst_4020_, lean_object* v___x_4021_, lean_object* v_fst_4022_, lean_object* v_inst_4023_, lean_object* v_R_4024_, lean_object* v_a_4025_, lean_object* v_b_4026_, lean_object* v_c_4027_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___redArg(v_upperBound_4019_, v_fst_4020_, v___x_4021_, v_fst_4022_, v_a_4025_, v_b_4026_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20___boxed(lean_object* v_upperBound_4029_, lean_object* v_fst_4030_, lean_object* v___x_4031_, lean_object* v_fst_4032_, lean_object* v_inst_4033_, lean_object* v_R_4034_, lean_object* v_a_4035_, lean_object* v_b_4036_, lean_object* v_c_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__20(v_upperBound_4029_, v_fst_4030_, v___x_4031_, v_fst_4032_, v_inst_4033_, v_R_4034_, v_a_4035_, v_b_4036_, v_c_4037_);
lean_dec_ref(v_fst_4032_);
lean_dec(v___x_4031_);
lean_dec_ref(v_fst_4030_);
lean_dec(v_upperBound_4029_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_4039_, lean_object* v_msg_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_4040_, v___y_4041_, v___y_4042_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_4045_, lean_object* v_msg_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_4045_, v_msg_4046_, v___y_4047_, v___y_4048_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(lean_object* v_00_u03b2_4051_, lean_object* v_m_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___redArg(v_m_4052_, v_a_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b2_4055_, lean_object* v_m_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23(v_00_u03b2_4055_, v_m_4056_, v_a_4057_);
lean_dec_ref(v_a_4057_);
lean_dec_ref(v_m_4056_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24(lean_object* v_00_u03b2_4059_, lean_object* v_m_4060_, lean_object* v_a_4061_, lean_object* v_b_4062_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24___redArg(v_m_4060_, v_a_4061_, v_b_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_4064_, lean_object* v_macroStack_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_4064_, v_macroStack_4065_, v___y_4067_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4070_, lean_object* v_macroStack_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4070_, v_macroStack_4071_, v___y_4072_, v___y_4073_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29(lean_object* v_inst_4076_, lean_object* v_R_4077_, lean_object* v_a_4078_, lean_object* v_b_4079_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__13_spec__18_spec__29___redArg(v_a_4078_, v_b_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(lean_object* v_00_u03b2_4081_, lean_object* v_a_4082_, lean_object* v_x_4083_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___redArg(v_a_4082_, v_x_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35___boxed(lean_object* v_00_u03b2_4085_, lean_object* v_a_4086_, lean_object* v_x_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__23_spec__35(v_00_u03b2_4085_, v_a_4086_, v_x_4087_);
lean_dec(v_x_4087_);
lean_dec_ref(v_a_4086_);
return v_res_4088_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(lean_object* v_00_u03b2_4089_, lean_object* v_a_4090_, lean_object* v_x_4091_){
_start:
{
uint8_t v___x_4092_; 
v___x_4092_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___redArg(v_a_4090_, v_x_4091_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37___boxed(lean_object* v_00_u03b2_4093_, lean_object* v_a_4094_, lean_object* v_x_4095_){
_start:
{
uint8_t v_res_4096_; lean_object* v_r_4097_; 
v_res_4096_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__37(v_00_u03b2_4093_, v_a_4094_, v_x_4095_);
lean_dec(v_x_4095_);
lean_dec_ref(v_a_4094_);
v_r_4097_ = lean_box(v_res_4096_);
return v_r_4097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38(lean_object* v_00_u03b2_4098_, lean_object* v_data_4099_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38___redArg(v_data_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39(lean_object* v_00_u03b2_4101_, lean_object* v_a_4102_, lean_object* v_b_4103_, lean_object* v_x_4104_){
_start:
{
lean_object* v___x_4105_; 
v___x_4105_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__39___redArg(v_a_4102_, v_b_4103_, v_x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44(lean_object* v_00_u03b2_4106_, lean_object* v_i_4107_, lean_object* v_source_4108_, lean_object* v_target_4109_){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44___redArg(v_i_4107_, v_source_4108_, v_target_4109_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4111_, lean_object* v_x_4112_, lean_object* v_x_4113_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10_spec__17_spec__24_spec__38_spec__44_spec__46___redArg(v_x_4112_, v_x_4113_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4123_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4124_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5));
v___x_4125_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4126_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4127_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4123_, v___x_4124_, v___x_4125_, v___x_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4156_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4157_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4158_ = l_Lean_addBuiltinDeclarationRanges(v___x_4156_, v___x_4157_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4161_){
_start:
{
lean_object* v_doc_4163_; lean_object* v___x_4164_; 
v_doc_4163_ = lean_ctor_get(v___y_4161_, 1);
lean_inc_ref(v_doc_4163_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v_doc_4163_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4165_);
lean_dec_ref(v___y_4165_);
return v_res_4167_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4168_, lean_object* v_a_4169_, uint8_t v_b_4170_){
_start:
{
lean_object* v_str_4171_; lean_object* v_startInclusive_4172_; lean_object* v_endExclusive_4173_; lean_object* v___x_4174_; uint8_t v___x_4175_; 
v_str_4171_ = lean_ctor_get(v_s_4168_, 0);
v_startInclusive_4172_ = lean_ctor_get(v_s_4168_, 1);
v_endExclusive_4173_ = lean_ctor_get(v_s_4168_, 2);
v___x_4174_ = lean_nat_sub(v_endExclusive_4173_, v_startInclusive_4172_);
v___x_4175_ = lean_nat_dec_eq(v_a_4169_, v___x_4174_);
lean_dec(v___x_4174_);
if (v___x_4175_ == 0)
{
lean_object* v___x_4176_; uint32_t v___x_4177_; uint32_t v___x_4178_; uint8_t v___x_4179_; 
v___x_4176_ = lean_nat_add(v_startInclusive_4172_, v_a_4169_);
lean_dec(v_a_4169_);
v___x_4177_ = lean_string_utf8_get_fast(v_str_4171_, v___x_4176_);
v___x_4178_ = 10;
v___x_4179_ = lean_uint32_dec_eq(v___x_4177_, v___x_4178_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4180_ = lean_string_utf8_next_fast(v_str_4171_, v___x_4176_);
lean_dec(v___x_4176_);
v___x_4181_ = lean_nat_sub(v___x_4180_, v_startInclusive_4172_);
v_a_4169_ = v___x_4181_;
v_b_4170_ = v___x_4179_;
goto _start;
}
else
{
lean_dec(v___x_4176_);
return v___x_4179_;
}
}
else
{
lean_dec(v_a_4169_);
return v_b_4170_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4183_, lean_object* v_a_4184_, lean_object* v_b_4185_){
_start:
{
uint8_t v_b_boxed_4186_; uint8_t v_res_4187_; lean_object* v_r_4188_; 
v_b_boxed_4186_ = lean_unbox(v_b_4185_);
v_res_4187_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4183_, v_a_4184_, v_b_boxed_4186_);
lean_dec_ref(v_s_4183_);
v_r_4188_ = lean_box(v_res_4187_);
return v_r_4188_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4189_){
_start:
{
lean_object* v_searcher_4190_; uint8_t v___x_4191_; uint8_t v___x_4192_; 
v_searcher_4190_ = lean_unsigned_to_nat(0u);
v___x_4191_ = 0;
v___x_4192_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4189_, v_searcher_4190_, v___x_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4193_){
_start:
{
uint8_t v_res_4194_; lean_object* v_r_4195_; 
v_res_4194_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4193_);
lean_dec_ref(v_s_4193_);
v_r_4195_ = lean_box(v_res_4194_);
return v_r_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4207_, lean_object* v_fst_4208_, uint8_t v___x_4209_, lean_object* v_a_4210_, lean_object* v___x_4211_, lean_object* v___x_4212_, lean_object* v___x_4213_, lean_object* v___x_4214_, lean_object* v___x_4215_, lean_object* v___x_4216_, lean_object* v___x_4217_, lean_object* v___x_4218_, lean_object* v_snd_4219_, lean_object* v___x_4220_){
_start:
{
if (lean_obj_tag(v___x_4207_) == 1)
{
lean_object* v_val_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4285_; 
v_val_4222_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4224_ = v___x_4207_;
v_isShared_4225_ = v_isSharedCheck_4285_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_val_4222_);
lean_dec(v___x_4207_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4285_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4228_ = l_Lean_Syntax_setArg(v_fst_4208_, v___x_4226_, v___x_4227_);
v___x_4229_ = l_Lean_Syntax_getPos_x3f(v___x_4228_, v___x_4209_);
lean_dec(v___x_4228_);
if (lean_obj_tag(v___x_4229_) == 1)
{
lean_object* v_val_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4281_; 
lean_dec_ref(v___x_4220_);
v_val_4230_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4232_ = v___x_4229_;
v_isShared_4233_ = v_isSharedCheck_4281_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_val_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4281_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___y_4235_; lean_object* v___x_4261_; uint8_t v___y_4268_; lean_object* v___x_4273_; uint8_t v___x_4274_; 
v___x_4261_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4219_);
v___x_4273_ = lean_string_utf8_byte_size(v___x_4261_);
v___x_4274_ = lean_nat_dec_eq(v___x_4273_, v___x_4226_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; lean_object* v___x_4276_; uint8_t v___x_4277_; 
v___x_4275_ = lean_string_length(v___x_4261_);
v___x_4276_ = lean_unsigned_to_nat(93u);
v___x_4277_ = lean_nat_dec_le(v___x_4275_, v___x_4276_);
if (v___x_4277_ == 0)
{
v___y_4268_ = v___x_4277_;
goto v___jp_4267_;
}
else
{
lean_object* v___x_4278_; uint8_t v___x_4279_; 
lean_inc_ref(v___x_4261_);
v___x_4278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4261_);
lean_ctor_set(v___x_4278_, 1, v___x_4226_);
lean_ctor_set(v___x_4278_, 2, v___x_4273_);
v___x_4279_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4278_);
lean_dec_ref_known(v___x_4278_, 3);
if (v___x_4279_ == 0)
{
v___y_4268_ = v___x_4277_;
goto v___jp_4267_;
}
else
{
goto v___jp_4262_;
}
}
}
else
{
lean_object* v___x_4280_; 
lean_dec_ref(v___x_4261_);
v___x_4280_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_4235_ = v___x_4280_;
goto v___jp_4234_;
}
v___jp_4234_:
{
lean_object* v_toEditableDocumentCore_4236_; lean_object* v_meta_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4257_; 
v_toEditableDocumentCore_4236_ = lean_ctor_get(v_a_4210_, 0);
lean_inc_ref(v_toEditableDocumentCore_4236_);
v_meta_4237_ = lean_ctor_get(v_toEditableDocumentCore_4236_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v_toEditableDocumentCore_4236_);
if (v_isSharedCheck_4257_ == 0)
{
lean_object* v_unused_4258_; lean_object* v_unused_4259_; lean_object* v_unused_4260_; 
v_unused_4258_ = lean_ctor_get(v_toEditableDocumentCore_4236_, 3);
lean_dec(v_unused_4258_);
v_unused_4259_ = lean_ctor_get(v_toEditableDocumentCore_4236_, 2);
lean_dec(v_unused_4259_);
v_unused_4260_ = lean_ctor_get(v_toEditableDocumentCore_4236_, 1);
lean_dec(v_unused_4260_);
v___x_4239_ = v_toEditableDocumentCore_4236_;
v_isShared_4240_ = v_isSharedCheck_4257_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_meta_4237_);
lean_dec(v_toEditableDocumentCore_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4257_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v_text_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4247_; 
v_text_4241_ = lean_ctor_get(v_meta_4237_, 3);
lean_inc_ref(v_text_4241_);
lean_dec_ref(v_meta_4237_);
v___x_4242_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4210_);
v___x_4243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4243_, 0, v_val_4222_);
lean_ctor_set(v___x_4243_, 1, v_val_4230_);
v___x_4244_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4241_, v___x_4243_);
v___x_4245_ = lean_box(0);
lean_inc(v___x_4211_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 3, v___x_4211_);
lean_ctor_set(v___x_4239_, 2, v___x_4245_);
lean_ctor_set(v___x_4239_, 1, v___y_4235_);
lean_ctor_set(v___x_4239_, 0, v___x_4244_);
v___x_4247_ = v___x_4239_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v___x_4244_);
lean_ctor_set(v_reuseFailAlloc_4256_, 1, v___y_4235_);
lean_ctor_set(v_reuseFailAlloc_4256_, 2, v___x_4245_);
lean_ctor_set(v_reuseFailAlloc_4256_, 3, v___x_4211_);
v___x_4247_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4248_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4242_, v___x_4247_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v___x_4248_);
v___x_4250_ = v___x_4232_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
lean_object* v___x_4251_; lean_object* v___x_4253_; 
lean_inc(v___x_4211_);
v___x_4251_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4211_);
lean_ctor_set(v___x_4251_, 1, v___x_4211_);
lean_ctor_set(v___x_4251_, 2, v___x_4212_);
lean_ctor_set(v___x_4251_, 3, v___x_4213_);
lean_ctor_set(v___x_4251_, 4, v___x_4214_);
lean_ctor_set(v___x_4251_, 5, v___x_4215_);
lean_ctor_set(v___x_4251_, 6, v___x_4216_);
lean_ctor_set(v___x_4251_, 7, v___x_4250_);
lean_ctor_set(v___x_4251_, 8, v___x_4217_);
lean_ctor_set(v___x_4251_, 9, v___x_4218_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set_tag(v___x_4224_, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4251_);
v___x_4253_ = v___x_4224_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4251_);
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
v___jp_4262_:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4263_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4264_ = lean_string_append(v___x_4263_, v___x_4261_);
lean_dec_ref(v___x_4261_);
v___x_4265_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4266_ = lean_string_append(v___x_4264_, v___x_4265_);
v___y_4235_ = v___x_4266_;
goto v___jp_4234_;
}
v___jp_4267_:
{
if (v___y_4268_ == 0)
{
goto v___jp_4262_;
}
else
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4269_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4270_ = lean_string_append(v___x_4269_, v___x_4261_);
lean_dec_ref(v___x_4261_);
v___x_4271_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4272_ = lean_string_append(v___x_4270_, v___x_4271_);
v___y_4235_ = v___x_4272_;
goto v___jp_4234_;
}
}
}
}
else
{
lean_object* v___x_4283_; 
lean_dec(v___x_4229_);
lean_dec(v_val_4222_);
lean_dec_ref(v_snd_4219_);
lean_dec(v___x_4218_);
lean_dec(v___x_4217_);
lean_dec(v___x_4216_);
lean_dec(v___x_4215_);
lean_dec(v___x_4214_);
lean_dec(v___x_4213_);
lean_dec_ref(v___x_4212_);
lean_dec(v___x_4211_);
lean_dec_ref(v_a_4210_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set_tag(v___x_4224_, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4220_);
v___x_4283_ = v___x_4224_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4220_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
else
{
lean_object* v___x_4286_; 
lean_dec_ref(v_snd_4219_);
lean_dec(v___x_4218_);
lean_dec(v___x_4217_);
lean_dec(v___x_4216_);
lean_dec(v___x_4215_);
lean_dec(v___x_4214_);
lean_dec(v___x_4213_);
lean_dec_ref(v___x_4212_);
lean_dec(v___x_4211_);
lean_dec_ref(v_a_4210_);
lean_dec(v_fst_4208_);
lean_dec(v___x_4207_);
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4220_);
return v___x_4286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4287_, lean_object* v_fst_4288_, lean_object* v___x_4289_, lean_object* v_a_4290_, lean_object* v___x_4291_, lean_object* v___x_4292_, lean_object* v___x_4293_, lean_object* v___x_4294_, lean_object* v___x_4295_, lean_object* v___x_4296_, lean_object* v___x_4297_, lean_object* v___x_4298_, lean_object* v_snd_4299_, lean_object* v___x_4300_, lean_object* v___y_4301_){
_start:
{
uint8_t v___x_4549__boxed_4302_; lean_object* v_res_4303_; 
v___x_4549__boxed_4302_ = lean_unbox(v___x_4289_);
v_res_4303_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4287_, v_fst_4288_, v___x_4549__boxed_4302_, v_a_4290_, v___x_4291_, v___x_4292_, v___x_4293_, v___x_4294_, v___x_4295_, v___x_4296_, v___x_4297_, v___x_4298_, v_snd_4299_, v___x_4300_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4307_, size_t v_sz_4308_, size_t v_i_4309_, lean_object* v_b_4310_){
_start:
{
lean_object* v_a_4312_; uint8_t v___x_4316_; 
v___x_4316_ = lean_usize_dec_lt(v_i_4309_, v_sz_4308_);
if (v___x_4316_ == 0)
{
lean_inc_ref(v_b_4310_);
return v_b_4310_;
}
else
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v_a_4319_; 
v___x_4317_ = lean_box(0);
v___x_4318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4319_ = lean_array_uget(v_as_4307_, v_i_4309_);
if (lean_obj_tag(v_a_4319_) == 1)
{
lean_object* v_i_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4354_; 
v_i_4320_ = lean_ctor_get(v_a_4319_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v_a_4319_);
if (v_isSharedCheck_4354_ == 0)
{
lean_object* v_unused_4355_; 
v_unused_4355_ = lean_ctor_get(v_a_4319_, 1);
lean_dec(v_unused_4355_);
v___x_4322_ = v_a_4319_;
v_isShared_4323_ = v_isSharedCheck_4354_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_i_4320_);
lean_dec(v_a_4319_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4354_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
if (lean_obj_tag(v_i_4320_) == 10)
{
lean_object* v_i_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4353_; 
v_i_4324_ = lean_ctor_get(v_i_4320_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v_i_4320_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4326_ = v_i_4320_;
v_isShared_4327_ = v_isSharedCheck_4353_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_i_4324_);
lean_dec(v_i_4320_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4353_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v_stx_4328_; lean_object* v_value_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4352_; 
v_stx_4328_ = lean_ctor_get(v_i_4324_, 0);
v_value_4329_ = lean_ctor_get(v_i_4324_, 1);
v_isSharedCheck_4352_ = !lean_is_exclusive(v_i_4324_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4331_ = v_i_4324_;
v_isShared_4332_ = v_isSharedCheck_4352_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_value_4329_);
lean_inc(v_stx_4328_);
lean_dec(v_i_4324_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4352_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4334_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4329_, v___x_4333_);
lean_dec(v_value_4329_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_del_object(v___x_4331_);
lean_dec(v_stx_4328_);
lean_del_object(v___x_4326_);
lean_del_object(v___x_4322_);
v_a_4312_ = v___x_4318_;
goto v___jp_4311_;
}
else
{
lean_object* v_val_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4351_; 
v_val_4335_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4337_ = v___x_4334_;
v_isShared_4338_ = v_isSharedCheck_4351_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_val_4335_);
lean_dec(v___x_4334_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4351_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4332_ == 0)
{
lean_ctor_set(v___x_4331_, 1, v_val_4335_);
v___x_4340_ = v___x_4331_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_stx_4328_);
lean_ctor_set(v_reuseFailAlloc_4350_, 1, v_val_4335_);
v___x_4340_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4342_; 
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 0, v___x_4340_);
v___x_4342_ = v___x_4337_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4340_);
v___x_4342_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
lean_object* v___x_4344_; 
if (v_isShared_4327_ == 0)
{
lean_ctor_set_tag(v___x_4326_, 1);
lean_ctor_set(v___x_4326_, 0, v___x_4342_);
v___x_4344_ = v___x_4326_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4342_);
v___x_4344_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
lean_object* v___x_4346_; 
if (v_isShared_4323_ == 0)
{
lean_ctor_set_tag(v___x_4322_, 0);
lean_ctor_set(v___x_4322_, 1, v___x_4317_);
lean_ctor_set(v___x_4322_, 0, v___x_4344_);
v___x_4346_ = v___x_4322_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v___x_4344_);
lean_ctor_set(v_reuseFailAlloc_4347_, 1, v___x_4317_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
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
lean_del_object(v___x_4322_);
lean_dec_ref(v_i_4320_);
v_a_4312_ = v___x_4318_;
goto v___jp_4311_;
}
}
}
else
{
lean_dec(v_a_4319_);
v_a_4312_ = v___x_4318_;
goto v___jp_4311_;
}
}
v___jp_4311_:
{
size_t v___x_4313_; size_t v___x_4314_; 
v___x_4313_ = ((size_t)1ULL);
v___x_4314_ = lean_usize_add(v_i_4309_, v___x_4313_);
v_i_4309_ = v___x_4314_;
v_b_4310_ = v_a_4312_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4356_, lean_object* v_sz_4357_, lean_object* v_i_4358_, lean_object* v_b_4359_){
_start:
{
size_t v_sz_boxed_4360_; size_t v_i_boxed_4361_; lean_object* v_res_4362_; 
v_sz_boxed_4360_ = lean_unbox_usize(v_sz_4357_);
lean_dec(v_sz_4357_);
v_i_boxed_4361_ = lean_unbox_usize(v_i_4358_);
lean_dec(v_i_4358_);
v_res_4362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4356_, v_sz_boxed_4360_, v_i_boxed_4361_, v_b_4359_);
lean_dec_ref(v_b_4359_);
lean_dec_ref(v_as_4356_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4363_, size_t v_sz_4364_, size_t v_i_4365_, lean_object* v_b_4366_){
_start:
{
lean_object* v_a_4368_; uint8_t v___x_4372_; 
v___x_4372_ = lean_usize_dec_lt(v_i_4365_, v_sz_4364_);
if (v___x_4372_ == 0)
{
lean_inc_ref(v_b_4366_);
return v_b_4366_;
}
else
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v_a_4375_; 
v___x_4373_ = lean_box(0);
v___x_4374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4375_ = lean_array_uget(v_as_4363_, v_i_4365_);
if (lean_obj_tag(v_a_4375_) == 1)
{
lean_object* v_i_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4410_; 
v_i_4376_ = lean_ctor_get(v_a_4375_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v_a_4375_);
if (v_isSharedCheck_4410_ == 0)
{
lean_object* v_unused_4411_; 
v_unused_4411_ = lean_ctor_get(v_a_4375_, 1);
lean_dec(v_unused_4411_);
v___x_4378_ = v_a_4375_;
v_isShared_4379_ = v_isSharedCheck_4410_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_i_4376_);
lean_dec(v_a_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4410_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
if (lean_obj_tag(v_i_4376_) == 10)
{
lean_object* v_i_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4409_; 
v_i_4380_ = lean_ctor_get(v_i_4376_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v_i_4376_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4382_ = v_i_4376_;
v_isShared_4383_ = v_isSharedCheck_4409_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_i_4380_);
lean_dec(v_i_4376_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4409_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v_stx_4384_; lean_object* v_value_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4408_; 
v_stx_4384_ = lean_ctor_get(v_i_4380_, 0);
v_value_4385_ = lean_ctor_get(v_i_4380_, 1);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_i_4380_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4387_ = v_i_4380_;
v_isShared_4388_ = v_isSharedCheck_4408_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_value_4385_);
lean_inc(v_stx_4384_);
lean_dec(v_i_4380_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4408_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4389_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4390_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4385_, v___x_4389_);
lean_dec(v_value_4385_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_del_object(v___x_4387_);
lean_dec(v_stx_4384_);
lean_del_object(v___x_4382_);
lean_del_object(v___x_4378_);
v_a_4368_ = v___x_4374_;
goto v___jp_4367_;
}
else
{
lean_object* v_val_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4407_; 
v_val_4391_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4393_ = v___x_4390_;
v_isShared_4394_ = v_isSharedCheck_4407_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_val_4391_);
lean_dec(v___x_4390_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4407_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 1, v_val_4391_);
v___x_4396_ = v___x_4387_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_stx_4384_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_val_4391_);
v___x_4396_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
lean_object* v___x_4398_; 
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v___x_4396_);
v___x_4398_ = v___x_4393_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4396_);
v___x_4398_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
lean_object* v___x_4400_; 
if (v_isShared_4383_ == 0)
{
lean_ctor_set_tag(v___x_4382_, 1);
lean_ctor_set(v___x_4382_, 0, v___x_4398_);
v___x_4400_ = v___x_4382_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4398_);
v___x_4400_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
lean_object* v___x_4402_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set_tag(v___x_4378_, 0);
lean_ctor_set(v___x_4378_, 1, v___x_4373_);
lean_ctor_set(v___x_4378_, 0, v___x_4400_);
v___x_4402_ = v___x_4378_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v___x_4373_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
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
lean_del_object(v___x_4378_);
lean_dec_ref(v_i_4376_);
v_a_4368_ = v___x_4374_;
goto v___jp_4367_;
}
}
}
else
{
lean_dec(v_a_4375_);
v_a_4368_ = v___x_4374_;
goto v___jp_4367_;
}
}
v___jp_4367_:
{
size_t v___x_4369_; size_t v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = ((size_t)1ULL);
v___x_4370_ = lean_usize_add(v_i_4365_, v___x_4369_);
v___x_4371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4363_, v_sz_4364_, v___x_4370_, v_a_4368_);
return v___x_4371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4412_, lean_object* v_sz_4413_, lean_object* v_i_4414_, lean_object* v_b_4415_){
_start:
{
size_t v_sz_boxed_4416_; size_t v_i_boxed_4417_; lean_object* v_res_4418_; 
v_sz_boxed_4416_ = lean_unbox_usize(v_sz_4413_);
lean_dec(v_sz_4413_);
v_i_boxed_4417_ = lean_unbox_usize(v_i_4414_);
lean_dec(v_i_4414_);
v_res_4418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4412_, v_sz_boxed_4416_, v_i_boxed_4417_, v_b_4415_);
lean_dec_ref(v_b_4415_);
lean_dec_ref(v_as_4412_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4419_){
_start:
{
if (lean_obj_tag(v_x_4419_) == 0)
{
lean_object* v_cs_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; size_t v_sz_4423_; size_t v___x_4424_; lean_object* v___x_4425_; lean_object* v_fst_4426_; 
v_cs_4420_ = lean_ctor_get(v_x_4419_, 0);
v___x_4421_ = lean_box(0);
v___x_4422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4423_ = lean_array_size(v_cs_4420_);
v___x_4424_ = ((size_t)0ULL);
v___x_4425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4420_, v_sz_4423_, v___x_4424_, v___x_4422_);
v_fst_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_fst_4426_);
lean_dec_ref(v___x_4425_);
if (lean_obj_tag(v_fst_4426_) == 0)
{
return v___x_4421_;
}
else
{
lean_object* v_val_4427_; 
v_val_4427_ = lean_ctor_get(v_fst_4426_, 0);
lean_inc(v_val_4427_);
lean_dec_ref_known(v_fst_4426_, 1);
return v_val_4427_;
}
}
else
{
lean_object* v_vs_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; size_t v_sz_4431_; size_t v___x_4432_; lean_object* v___x_4433_; lean_object* v_fst_4434_; 
v_vs_4428_ = lean_ctor_get(v_x_4419_, 0);
v___x_4429_ = lean_box(0);
v___x_4430_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4431_ = lean_array_size(v_vs_4428_);
v___x_4432_ = ((size_t)0ULL);
v___x_4433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4428_, v_sz_4431_, v___x_4432_, v___x_4430_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4436_, size_t v_sz_4437_, size_t v_i_4438_, lean_object* v_b_4439_){
_start:
{
uint8_t v___x_4440_; 
v___x_4440_ = lean_usize_dec_lt(v_i_4438_, v_sz_4437_);
if (v___x_4440_ == 0)
{
lean_inc_ref(v_b_4439_);
return v_b_4439_;
}
else
{
lean_object* v___x_4441_; lean_object* v_a_4442_; lean_object* v___x_4443_; 
v___x_4441_ = lean_box(0);
v_a_4442_ = lean_array_uget_borrowed(v_as_4436_, v_i_4438_);
v___x_4443_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4442_);
if (lean_obj_tag(v___x_4443_) == 1)
{
lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
v___x_4445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4445_, 0, v___x_4444_);
lean_ctor_set(v___x_4445_, 1, v___x_4441_);
return v___x_4445_;
}
else
{
lean_object* v___x_4446_; size_t v___x_4447_; size_t v___x_4448_; 
lean_dec(v___x_4443_);
v___x_4446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4447_ = ((size_t)1ULL);
v___x_4448_ = lean_usize_add(v_i_4438_, v___x_4447_);
v_i_4438_ = v___x_4448_;
v_b_4439_ = v___x_4446_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4450_, lean_object* v_sz_4451_, lean_object* v_i_4452_, lean_object* v_b_4453_){
_start:
{
size_t v_sz_boxed_4454_; size_t v_i_boxed_4455_; lean_object* v_res_4456_; 
v_sz_boxed_4454_ = lean_unbox_usize(v_sz_4451_);
lean_dec(v_sz_4451_);
v_i_boxed_4455_ = lean_unbox_usize(v_i_4452_);
lean_dec(v_i_4452_);
v_res_4456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4450_, v_sz_boxed_4454_, v_i_boxed_4455_, v_b_4453_);
lean_dec_ref(v_b_4453_);
lean_dec_ref(v_as_4450_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4457_);
lean_dec_ref(v_x_4457_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4459_){
_start:
{
lean_object* v_root_4460_; lean_object* v_tail_4461_; lean_object* v___x_4462_; 
v_root_4460_ = lean_ctor_get(v_t_4459_, 0);
v_tail_4461_ = lean_ctor_get(v_t_4459_, 1);
v___x_4462_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4460_);
if (lean_obj_tag(v___x_4462_) == 0)
{
lean_object* v___x_4463_; size_t v_sz_4464_; size_t v___x_4465_; lean_object* v___x_4466_; lean_object* v_fst_4467_; 
v___x_4463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4464_ = lean_array_size(v_tail_4461_);
v___x_4465_ = ((size_t)0ULL);
v___x_4466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4461_, v_sz_4464_, v___x_4465_, v___x_4463_);
v_fst_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_fst_4467_);
lean_dec_ref(v___x_4466_);
if (lean_obj_tag(v_fst_4467_) == 0)
{
return v___x_4462_;
}
else
{
lean_object* v_val_4468_; 
v_val_4468_ = lean_ctor_get(v_fst_4467_, 0);
lean_inc(v_val_4468_);
lean_dec_ref_known(v_fst_4467_, 1);
return v_val_4468_;
}
}
else
{
return v___x_4462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4469_);
lean_dec_ref(v_t_4469_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4485_, lean_object* v_a_4486_){
_start:
{
if (lean_obj_tag(v_node_4485_) == 1)
{
lean_object* v_children_4488_; lean_object* v_res_4489_; 
v_children_4488_ = lean_ctor_get(v_node_4485_, 1);
v_res_4489_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4488_);
if (lean_obj_tag(v_res_4489_) == 1)
{
lean_object* v_val_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4527_; 
v_val_4490_ = lean_ctor_get(v_res_4489_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v_res_4489_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4492_ = v_res_4489_;
v_isShared_4493_ = v_isSharedCheck_4527_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_val_4490_);
lean_dec(v_res_4489_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4527_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v_fst_4494_; lean_object* v_snd_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4526_; 
v_fst_4494_ = lean_ctor_get(v_val_4490_, 0);
v_snd_4495_ = lean_ctor_get(v_val_4490_, 1);
v_isSharedCheck_4526_ = !lean_is_exclusive(v_val_4490_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4497_ = v_val_4490_;
v_isShared_4498_ = v_isSharedCheck_4526_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_snd_4495_);
lean_inc(v_fst_4494_);
lean_dec(v_val_4490_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4526_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4525_; 
v___x_4499_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4486_);
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4502_ = v___x_4499_;
v_isShared_4503_ = v_isSharedCheck_4525_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4499_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4525_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; uint8_t v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___y_4512_; lean_object* v___x_4514_; 
v___x_4504_ = lean_box(0);
v___x_4505_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4506_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4507_ = 1;
v___x_4508_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4509_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4510_ = l_Lean_Syntax_getPos_x3f(v_fst_4494_, v___x_4507_);
v___x_4511_ = lean_box(v___x_4507_);
v___y_4512_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4512_, 0, v___x_4510_);
lean_closure_set(v___y_4512_, 1, v_fst_4494_);
lean_closure_set(v___y_4512_, 2, v___x_4511_);
lean_closure_set(v___y_4512_, 3, v_a_4500_);
lean_closure_set(v___y_4512_, 4, v___x_4504_);
lean_closure_set(v___y_4512_, 5, v___x_4505_);
lean_closure_set(v___y_4512_, 6, v___x_4506_);
lean_closure_set(v___y_4512_, 7, v___x_4504_);
lean_closure_set(v___y_4512_, 8, v___x_4508_);
lean_closure_set(v___y_4512_, 9, v___x_4504_);
lean_closure_set(v___y_4512_, 10, v___x_4504_);
lean_closure_set(v___y_4512_, 11, v___x_4504_);
lean_closure_set(v___y_4512_, 12, v_snd_4495_);
lean_closure_set(v___y_4512_, 13, v___x_4509_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 0, v___y_4512_);
v___x_4514_ = v___x_4492_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v___y_4512_);
v___x_4514_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
lean_object* v___x_4516_; 
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 1, v___x_4514_);
lean_ctor_set(v___x_4497_, 0, v___x_4509_);
v___x_4516_ = v___x_4497_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4509_);
lean_ctor_set(v_reuseFailAlloc_4523_, 1, v___x_4514_);
v___x_4516_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4521_; 
v___x_4517_ = lean_unsigned_to_nat(1u);
v___x_4518_ = lean_mk_empty_array_with_capacity(v___x_4517_);
v___x_4519_ = lean_array_push(v___x_4518_, v___x_4516_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v___x_4519_);
v___x_4521_ = v___x_4502_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4519_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
lean_dec(v_res_4489_);
v___x_4528_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4529_, 0, v___x_4528_);
return v___x_4529_;
}
}
else
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4530_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
return v___x_4531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4532_, v_a_4533_);
lean_dec_ref(v_a_4533_);
lean_dec_ref(v_node_4532_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4536_, lean_object* v_x_4537_, lean_object* v_x_4538_, lean_object* v_node_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4539_, v_a_4540_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4543_, lean_object* v_x_4544_, lean_object* v_x_4545_, lean_object* v_node_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4543_, v_x_4544_, v_x_4545_, v_node_4546_, v_a_4547_);
lean_dec_ref(v_a_4547_);
lean_dec_ref(v_node_4546_);
lean_dec_ref(v_x_4545_);
lean_dec_ref(v_x_4544_);
lean_dec_ref(v_x_4543_);
return v_res_4549_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4550_, lean_object* v_inst_4551_, lean_object* v_R_4552_, lean_object* v_a_4553_, uint8_t v_b_4554_, lean_object* v_c_4555_){
_start:
{
uint8_t v___x_4556_; 
v___x_4556_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4550_, v_a_4553_, v_b_4554_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4557_, lean_object* v_inst_4558_, lean_object* v_R_4559_, lean_object* v_a_4560_, lean_object* v_b_4561_, lean_object* v_c_4562_){
_start:
{
uint8_t v_b_boxed_4563_; uint8_t v_res_4564_; lean_object* v_r_4565_; 
v_b_boxed_4563_ = lean_unbox(v_b_4561_);
v_res_4564_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4557_, v_inst_4558_, v_R_4559_, v_a_4560_, v_b_boxed_4563_, v_c_4562_);
lean_dec_ref(v_s_4557_);
v_r_4565_ = lean_box(v_res_4564_);
return v_r_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_(){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4571_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_));
v___x_4572_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4573_ = l_Lean_CodeAction_insertBuiltin(v___x_4571_, v___x_4572_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365____boxed(lean_object* v_a_4574_){
_start:
{
lean_object* v_res_4575_; 
v_res_4575_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_365_();
return v_res_4575_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4577_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4578_ = lean_string_utf8_byte_size(v___x_4577_);
return v___x_4578_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; uint8_t v___x_4581_; 
v___x_4579_ = lean_unsigned_to_nat(0u);
v___x_4580_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4581_ = lean_nat_dec_eq(v___x_4580_, v___x_4579_);
return v___x_4581_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4582_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4583_ = lean_unsigned_to_nat(0u);
v___x_4584_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
lean_ctor_set(v___x_4585_, 1, v___x_4583_);
lean_ctor_set(v___x_4585_, 2, v___x_4582_);
return v___x_4585_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4(void){
_start:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4586_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4587_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4586_);
return v___x_4587_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4588_ = lean_unsigned_to_nat(0u);
v___x_4589_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4);
v___x_4590_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4591_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4590_);
lean_ctor_set(v___x_4591_, 1, v___x_4589_);
lean_ctor_set(v___x_4591_, 2, v___x_4588_);
lean_ctor_set(v___x_4591_, 3, v___x_4588_);
return v___x_4591_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4592_){
_start:
{
lean_object* v___y_4594_; uint8_t v___x_4597_; 
v___x_4597_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; 
v___x_4598_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5);
v___y_4594_ = v___x_4598_;
goto v___jp_4593_;
}
else
{
lean_object* v___x_4599_; 
v___x_4599_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_4594_ = v___x_4599_;
goto v___jp_4593_;
}
v___jp_4593_:
{
uint8_t v___x_4595_; uint8_t v___x_4596_; 
v___x_4595_ = 0;
lean_inc(v___y_4594_);
v___x_4596_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4592_, v___y_4594_, v___x_4595_);
return v___x_4596_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4600_){
_start:
{
uint8_t v_res_4601_; lean_object* v_r_4602_; 
v_res_4601_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4600_);
lean_dec_ref(v_s_4600_);
v_r_4602_ = lean_box(v_res_4601_);
return v_r_4602_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4603_, lean_object* v_as_x27_4604_, uint8_t v_b_4605_){
_start:
{
if (lean_obj_tag(v_as_x27_4604_) == 0)
{
lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4607_ = lean_box(v_b_4605_);
v___x_4608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
return v___x_4608_;
}
else
{
lean_object* v_head_4609_; uint8_t v_isSilent_4610_; 
v_head_4609_ = lean_ctor_get(v_as_x27_4604_, 0);
v_isSilent_4610_ = lean_ctor_get_uint8(v_head_4609_, sizeof(void*)*5 + 2);
if (v_isSilent_4610_ == 0)
{
lean_object* v_tail_4611_; lean_object* v_data_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; uint8_t v___x_4617_; 
v_tail_4611_ = lean_ctor_get(v_as_x27_4604_, 1);
v_data_4612_ = lean_ctor_get(v_head_4609_, 4);
lean_inc(v_data_4612_);
v___x_4613_ = l_Lean_MessageData_toString(v_data_4612_);
v___x_4614_ = lean_unsigned_to_nat(0u);
v___x_4615_ = lean_string_utf8_byte_size(v___x_4613_);
v___x_4616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4613_);
lean_ctor_set(v___x_4616_, 1, v___x_4614_);
lean_ctor_set(v___x_4616_, 2, v___x_4615_);
v___x_4617_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4616_);
lean_dec_ref_known(v___x_4616_, 3);
if (v___x_4617_ == 0)
{
v_as_x27_4604_ = v_tail_4611_;
goto _start;
}
else
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4619_ = lean_box(v_foundPanic_4603_);
v___x_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
return v___x_4620_;
}
}
else
{
lean_object* v_tail_4621_; 
v_tail_4621_ = lean_ctor_get(v_as_x27_4604_, 1);
v_as_x27_4604_ = v_tail_4621_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4623_, lean_object* v_as_x27_4624_, lean_object* v_b_4625_, lean_object* v___y_4626_){
_start:
{
uint8_t v_foundPanic_boxed_4627_; uint8_t v_b_boxed_4628_; lean_object* v_res_4629_; 
v_foundPanic_boxed_4627_ = lean_unbox(v_foundPanic_4623_);
v_b_boxed_4628_ = lean_unbox(v_b_4625_);
v_res_4629_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4627_, v_as_x27_4624_, v_b_boxed_4628_);
lean_dec(v_as_x27_4624_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4630_, uint8_t v_severity_4631_, uint8_t v_isSilent_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v___x_4636_; 
v___x_4636_ = l_Lean_Elab_Command_getRef___redArg(v___y_4633_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v___x_4638_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_a_4637_);
lean_dec_ref_known(v___x_4636_, 1);
v___x_4638_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4637_, v_msgData_4630_, v_severity_4631_, v_isSilent_4632_, v___y_4633_, v___y_4634_);
lean_dec(v_a_4637_);
return v___x_4638_;
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
lean_dec_ref(v_msgData_4630_);
v_a_4639_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v___x_4636_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4636_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4647_, lean_object* v_severity_4648_, lean_object* v_isSilent_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_){
_start:
{
uint8_t v_severity_boxed_4653_; uint8_t v_isSilent_boxed_4654_; lean_object* v_res_4655_; 
v_severity_boxed_4653_ = lean_unbox(v_severity_4648_);
v_isSilent_boxed_4654_ = lean_unbox(v_isSilent_4649_);
v_res_4655_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4647_, v_severity_boxed_4653_, v_isSilent_boxed_4654_, v___y_4650_, v___y_4651_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
uint8_t v___x_4660_; uint8_t v___x_4661_; lean_object* v___x_4662_; 
v___x_4660_ = 2;
v___x_4661_ = 0;
v___x_4662_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4656_, v___x_4660_, v___x_4661_, v___y_4657_, v___y_4658_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4663_, v___y_4664_, v___y_4665_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
return v_res_4667_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4675_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4676_ = l_Lean_MessageData_ofFormat(v___x_4675_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_){
_start:
{
lean_object* v___x_4681_; uint8_t v_foundPanic_4682_; 
v___x_4681_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4677_);
v_foundPanic_4682_ = l_Lean_Syntax_isOfKind(v_x_4677_, v___x_4681_);
if (v_foundPanic_4682_ == 0)
{
lean_object* v___x_4683_; 
lean_dec(v_x_4677_);
v___x_4683_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4683_;
}
else
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4684_ = lean_unsigned_to_nat(2u);
v___x_4685_ = l_Lean_Syntax_getArg(v_x_4677_, v___x_4684_);
lean_dec(v_x_4677_);
v___x_4686_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4685_, v_a_4678_, v_a_4679_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; uint8_t v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4745_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_a_4687_);
lean_dec_ref_known(v___x_4686_, 1);
v___x_4688_ = 0;
v___x_4689_ = l_Lean_MessageLog_toList(v_a_4687_);
v___x_4690_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4682_, v___x_4689_, v___x_4688_);
lean_dec(v___x_4689_);
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4693_ = v___x_4690_;
v_isShared_4694_ = v_isSharedCheck_4745_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4690_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4745_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
uint8_t v___x_4695_; 
v___x_4695_ = lean_unbox(v_a_4691_);
lean_dec(v_a_4691_);
if (v___x_4695_ == 0)
{
lean_object* v___x_4696_; lean_object* v_env_4697_; lean_object* v_scopes_4698_; lean_object* v_usedQuotCtxts_4699_; lean_object* v_nextMacroScope_4700_; lean_object* v_maxRecDepth_4701_; lean_object* v_ngen_4702_; lean_object* v_auxDeclNGen_4703_; lean_object* v_infoState_4704_; lean_object* v_traceState_4705_; lean_object* v_snapshotTasks_4706_; lean_object* v_prevLinterStates_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4717_; 
lean_del_object(v___x_4693_);
v___x_4696_ = lean_st_ref_take(v_a_4679_);
v_env_4697_ = lean_ctor_get(v___x_4696_, 0);
v_scopes_4698_ = lean_ctor_get(v___x_4696_, 2);
v_usedQuotCtxts_4699_ = lean_ctor_get(v___x_4696_, 3);
v_nextMacroScope_4700_ = lean_ctor_get(v___x_4696_, 4);
v_maxRecDepth_4701_ = lean_ctor_get(v___x_4696_, 5);
v_ngen_4702_ = lean_ctor_get(v___x_4696_, 6);
v_auxDeclNGen_4703_ = lean_ctor_get(v___x_4696_, 7);
v_infoState_4704_ = lean_ctor_get(v___x_4696_, 8);
v_traceState_4705_ = lean_ctor_get(v___x_4696_, 9);
v_snapshotTasks_4706_ = lean_ctor_get(v___x_4696_, 10);
v_prevLinterStates_4707_ = lean_ctor_get(v___x_4696_, 11);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4717_ == 0)
{
lean_object* v_unused_4718_; 
v_unused_4718_ = lean_ctor_get(v___x_4696_, 1);
lean_dec(v_unused_4718_);
v___x_4709_ = v___x_4696_;
v_isShared_4710_ = v_isSharedCheck_4717_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_prevLinterStates_4707_);
lean_inc(v_snapshotTasks_4706_);
lean_inc(v_traceState_4705_);
lean_inc(v_infoState_4704_);
lean_inc(v_auxDeclNGen_4703_);
lean_inc(v_ngen_4702_);
lean_inc(v_maxRecDepth_4701_);
lean_inc(v_nextMacroScope_4700_);
lean_inc(v_usedQuotCtxts_4699_);
lean_inc(v_scopes_4698_);
lean_inc(v_env_4697_);
lean_dec(v___x_4696_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4717_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4712_; 
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 1, v_a_4687_);
v___x_4712_ = v___x_4709_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_env_4697_);
lean_ctor_set(v_reuseFailAlloc_4716_, 1, v_a_4687_);
lean_ctor_set(v_reuseFailAlloc_4716_, 2, v_scopes_4698_);
lean_ctor_set(v_reuseFailAlloc_4716_, 3, v_usedQuotCtxts_4699_);
lean_ctor_set(v_reuseFailAlloc_4716_, 4, v_nextMacroScope_4700_);
lean_ctor_set(v_reuseFailAlloc_4716_, 5, v_maxRecDepth_4701_);
lean_ctor_set(v_reuseFailAlloc_4716_, 6, v_ngen_4702_);
lean_ctor_set(v_reuseFailAlloc_4716_, 7, v_auxDeclNGen_4703_);
lean_ctor_set(v_reuseFailAlloc_4716_, 8, v_infoState_4704_);
lean_ctor_set(v_reuseFailAlloc_4716_, 9, v_traceState_4705_);
lean_ctor_set(v_reuseFailAlloc_4716_, 10, v_snapshotTasks_4706_);
lean_ctor_set(v_reuseFailAlloc_4716_, 11, v_prevLinterStates_4707_);
v___x_4712_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4713_ = lean_st_ref_set(v_a_4679_, v___x_4712_);
v___x_4714_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4715_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4714_, v_a_4678_, v_a_4679_);
return v___x_4715_;
}
}
}
else
{
lean_object* v___x_4719_; lean_object* v_env_4720_; lean_object* v_scopes_4721_; lean_object* v_usedQuotCtxts_4722_; lean_object* v_nextMacroScope_4723_; lean_object* v_maxRecDepth_4724_; lean_object* v_ngen_4725_; lean_object* v_auxDeclNGen_4726_; lean_object* v_infoState_4727_; lean_object* v_traceState_4728_; lean_object* v_snapshotTasks_4729_; lean_object* v_prevLinterStates_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4743_; 
lean_dec(v_a_4687_);
v___x_4719_ = lean_st_ref_take(v_a_4679_);
v_env_4720_ = lean_ctor_get(v___x_4719_, 0);
v_scopes_4721_ = lean_ctor_get(v___x_4719_, 2);
v_usedQuotCtxts_4722_ = lean_ctor_get(v___x_4719_, 3);
v_nextMacroScope_4723_ = lean_ctor_get(v___x_4719_, 4);
v_maxRecDepth_4724_ = lean_ctor_get(v___x_4719_, 5);
v_ngen_4725_ = lean_ctor_get(v___x_4719_, 6);
v_auxDeclNGen_4726_ = lean_ctor_get(v___x_4719_, 7);
v_infoState_4727_ = lean_ctor_get(v___x_4719_, 8);
v_traceState_4728_ = lean_ctor_get(v___x_4719_, 9);
v_snapshotTasks_4729_ = lean_ctor_get(v___x_4719_, 10);
v_prevLinterStates_4730_ = lean_ctor_get(v___x_4719_, 11);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4743_ == 0)
{
lean_object* v_unused_4744_; 
v_unused_4744_ = lean_ctor_get(v___x_4719_, 1);
lean_dec(v_unused_4744_);
v___x_4732_ = v___x_4719_;
v_isShared_4733_ = v_isSharedCheck_4743_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_prevLinterStates_4730_);
lean_inc(v_snapshotTasks_4729_);
lean_inc(v_traceState_4728_);
lean_inc(v_infoState_4727_);
lean_inc(v_auxDeclNGen_4726_);
lean_inc(v_ngen_4725_);
lean_inc(v_maxRecDepth_4724_);
lean_inc(v_nextMacroScope_4723_);
lean_inc(v_usedQuotCtxts_4722_);
lean_inc(v_scopes_4721_);
lean_inc(v_env_4720_);
lean_dec(v___x_4719_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4743_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4734_; lean_object* v___x_4736_; 
v___x_4734_ = l_Lean_MessageLog_empty;
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 1, v___x_4734_);
v___x_4736_ = v___x_4732_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_env_4720_);
lean_ctor_set(v_reuseFailAlloc_4742_, 1, v___x_4734_);
lean_ctor_set(v_reuseFailAlloc_4742_, 2, v_scopes_4721_);
lean_ctor_set(v_reuseFailAlloc_4742_, 3, v_usedQuotCtxts_4722_);
lean_ctor_set(v_reuseFailAlloc_4742_, 4, v_nextMacroScope_4723_);
lean_ctor_set(v_reuseFailAlloc_4742_, 5, v_maxRecDepth_4724_);
lean_ctor_set(v_reuseFailAlloc_4742_, 6, v_ngen_4725_);
lean_ctor_set(v_reuseFailAlloc_4742_, 7, v_auxDeclNGen_4726_);
lean_ctor_set(v_reuseFailAlloc_4742_, 8, v_infoState_4727_);
lean_ctor_set(v_reuseFailAlloc_4742_, 9, v_traceState_4728_);
lean_ctor_set(v_reuseFailAlloc_4742_, 10, v_snapshotTasks_4729_);
lean_ctor_set(v_reuseFailAlloc_4742_, 11, v_prevLinterStates_4730_);
v___x_4736_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4740_; 
v___x_4737_ = lean_st_ref_set(v_a_4679_, v___x_4736_);
v___x_4738_ = lean_box(0);
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 0, v___x_4738_);
v___x_4740_ = v___x_4693_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4738_);
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
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
v_a_4746_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4686_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4686_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4754_, v_a_4755_, v_a_4756_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4759_, lean_object* v_as_4760_, lean_object* v_as_x27_4761_, uint8_t v_b_4762_, lean_object* v_a_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
lean_object* v___x_4767_; 
v___x_4767_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4759_, v_as_x27_4761_, v_b_4762_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4768_, lean_object* v_as_4769_, lean_object* v_as_x27_4770_, lean_object* v_b_4771_, lean_object* v_a_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_){
_start:
{
uint8_t v_foundPanic_boxed_4776_; uint8_t v_b_boxed_4777_; lean_object* v_res_4778_; 
v_foundPanic_boxed_4776_ = lean_unbox(v_foundPanic_4768_);
v_b_boxed_4777_ = lean_unbox(v_b_4771_);
v_res_4778_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4776_, v_as_4769_, v_as_x27_4770_, v_b_boxed_4777_, v_a_4772_, v___y_4773_, v___y_4774_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec(v_as_x27_4770_);
lean_dec(v_as_4769_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4787_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4788_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4789_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4790_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4791_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4787_, v___x_4788_, v___x_4789_, v___x_4790_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4792_){
_start:
{
lean_object* v_res_4793_; 
v_res_4793_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4793_;
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
