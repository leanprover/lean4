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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Message_isTrace(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_91_; lean_object* v___y_95_; uint32_t v___y_96_; lean_object* v_str_100_; lean_object* v_pos_112_; lean_object* v_endPos_113_; uint8_t v_severity_114_; lean_object* v_caption_115_; lean_object* v_data_116_; lean_object* v___x_117_; lean_object* v___y_119_; lean_object* v___y_120_; lean_object* v___y_121_; lean_object* v_str_132_; lean_object* v_str_144_; lean_object* v___y_155_; lean_object* v_str_159_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_pos_112_ = lean_ctor_get(v_msg_87_, 1);
lean_inc_ref(v_pos_112_);
v_endPos_113_ = lean_ctor_get(v_msg_87_, 2);
lean_inc(v_endPos_113_);
v_severity_114_ = lean_ctor_get_uint8(v_msg_87_, sizeof(void*)*5 + 1);
v_caption_115_ = lean_ctor_get(v_msg_87_, 3);
v_data_116_ = lean_ctor_get(v_msg_87_, 4);
lean_inc(v_data_116_);
v___x_117_ = l_Lean_MessageData_toString(v_data_116_);
v___x_166_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_167_ = lean_string_dec_eq(v_caption_115_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__11));
lean_inc_ref(v_caption_115_);
v___x_169_ = lean_string_append(v_caption_115_, v___x_168_);
v___x_170_ = lean_string_append(v___x_169_, v___x_117_);
lean_dec_ref(v___x_117_);
v_str_159_ = v___x_170_;
goto v___jp_158_;
}
else
{
v_str_159_ = v___x_117_;
goto v___jp_158_;
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
v___jp_118_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_122_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__1));
v___x_123_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v___y_120_, v_pos_112_);
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
lean_dec_ref(v___x_123_);
v___x_125_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2));
v___x_126_ = lean_string_append(v___x_124_, v___x_125_);
v___x_127_ = lean_string_append(v___x_126_, v___y_121_);
lean_dec_ref(v___y_121_);
v___x_128_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_129_ = lean_string_append(v___x_127_, v___x_128_);
v___x_130_ = lean_string_append(v___x_129_, v___y_119_);
lean_dec_ref(v___y_119_);
v_str_100_ = v___x_130_;
goto v___jp_99_;
}
v___jp_131_:
{
if (lean_obj_tag(v_reportPos_x3f_88_) == 1)
{
if (lean_obj_tag(v_endPos_113_) == 0)
{
lean_object* v_val_133_; lean_object* v___x_134_; 
v_val_133_ = lean_ctor_get(v_reportPos_x3f_88_, 0);
v___x_134_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__3));
v___y_119_ = v_str_132_;
v___y_120_ = v_val_133_;
v___y_121_ = v___x_134_;
goto v___jp_118_;
}
else
{
lean_object* v_val_135_; lean_object* v_val_136_; lean_object* v_line_137_; lean_object* v_column_138_; lean_object* v_line_139_; uint8_t v___x_140_; 
v_val_135_ = lean_ctor_get(v_endPos_113_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v_endPos_113_, 1);
v_val_136_ = lean_ctor_get(v_reportPos_x3f_88_, 0);
v_line_137_ = lean_ctor_get(v_val_135_, 0);
v_column_138_ = lean_ctor_get(v_val_135_, 1);
v_line_139_ = lean_ctor_get(v_pos_112_, 0);
v___x_140_ = lean_nat_dec_eq(v_line_137_, v_line_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v_val_136_, v_val_135_);
v___y_119_ = v_str_132_;
v___y_120_ = v_val_136_;
v___y_121_ = v___x_141_;
goto v___jp_118_;
}
else
{
lean_object* v___x_142_; 
lean_inc(v_column_138_);
lean_dec(v_val_135_);
v___x_142_ = l_Nat_reprFast(v_column_138_);
v___y_119_ = v_str_132_;
v___y_120_ = v_val_136_;
v___y_121_ = v___x_142_;
goto v___jp_118_;
}
}
}
else
{
lean_dec(v_endPos_113_);
lean_dec_ref(v_pos_112_);
v_str_100_ = v_str_132_;
goto v___jp_99_;
}
}
v___jp_143_:
{
uint8_t v___x_145_; 
v___x_145_ = l_Lean_Message_isTrace(v_msg_87_);
lean_dec_ref(v_msg_87_);
if (v___x_145_ == 0)
{
switch(v_severity_114_)
{
case 0:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__4));
v___x_147_ = lean_string_append(v___x_146_, v_str_144_);
lean_dec_ref(v_str_144_);
v_str_132_ = v___x_147_;
goto v___jp_131_;
}
case 1:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__5));
v___x_149_ = lean_string_append(v___x_148_, v_str_144_);
lean_dec_ref(v_str_144_);
v_str_132_ = v___x_149_;
goto v___jp_131_;
}
default: 
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__6));
v___x_151_ = lean_string_append(v___x_150_, v_str_144_);
lean_dec_ref(v_str_144_);
v_str_132_ = v___x_151_;
goto v___jp_131_;
}
}
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__7));
v___x_153_ = lean_string_append(v___x_152_, v_str_144_);
lean_dec_ref(v_str_144_);
v_str_132_ = v___x_153_;
goto v___jp_131_;
}
}
v___jp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_157_ = lean_string_append(v___x_156_, v___y_155_);
lean_dec_ref(v___y_155_);
v_str_144_ = v___x_157_;
goto v___jp_143_;
}
v___jp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_161_ = lean_string_utf8_byte_size(v_str_159_);
v___x_162_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_163_ = lean_nat_dec_le(v___x_162_, v___x_161_);
if (v___x_163_ == 0)
{
v___y_155_ = v_str_159_;
goto v___jp_154_;
}
else
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_string_memcmp(v_str_159_, v___x_160_, v___x_164_, v___x_164_, v___x_162_);
if (v___x_165_ == 0)
{
v___y_155_ = v_str_159_;
goto v___jp_154_;
}
else
{
v_str_144_ = v_str_159_;
goto v___jp_143_;
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
uint8_t v___x_775__boxed_427_; uint8_t v_res_428_; lean_object* v_r_429_; 
v___x_775__boxed_427_ = lean_unbox(v___x_425_);
v_res_428_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_775__boxed_427_, v_x_426_);
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
uint8_t v___x_781__boxed_442_; uint8_t v___x_782__boxed_443_; uint8_t v_res_444_; lean_object* v_r_445_; 
v___x_781__boxed_442_ = lean_unbox(v___x_439_);
v___x_782__boxed_443_ = lean_unbox(v___x_440_);
v_res_444_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_781__boxed_442_, v___x_782__boxed_443_, v_msg_441_);
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
uint8_t v___x_797__boxed_458_; uint8_t v___x_798__boxed_459_; uint8_t v_res_460_; lean_object* v_r_461_; 
v___x_797__boxed_458_ = lean_unbox(v___x_455_);
v___x_798__boxed_459_ = lean_unbox(v___x_456_);
v_res_460_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_797__boxed_458_, v___x_798__boxed_459_, v_msg_457_);
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
uint8_t v___x_813__boxed_474_; uint8_t v___x_814__boxed_475_; uint8_t v_res_476_; lean_object* v_r_477_; 
v___x_813__boxed_474_ = lean_unbox(v___x_471_);
v___x_814__boxed_475_ = lean_unbox(v___x_472_);
v_res_476_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_813__boxed_474_, v___x_814__boxed_475_, v_msg_473_);
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
uint8_t v_a_6430__boxed_580_; uint8_t v_res_581_; lean_object* v_r_582_; 
v_a_6430__boxed_580_ = lean_unbox(v_a_578_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_576_, v_snd_577_, v_a_6430__boxed_580_, v___y_579_);
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
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = lean_unsigned_to_nat(1u);
v___x_710_ = l_Lean_Syntax_getArg(v___x_702_, v___x_709_);
lean_dec(v___x_702_);
v___x_711_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v___x_710_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___f_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
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
uint8_t v___x_7305__boxed_1040_; size_t v_i_boxed_1041_; size_t v_stop_boxed_1042_; lean_object* v_res_1043_; 
v___x_7305__boxed_1040_ = lean_unbox(v___x_1035_);
v_i_boxed_1041_ = lean_unbox_usize(v_i_1037_);
lean_dec(v_i_1037_);
v_stop_boxed_1042_ = lean_unbox_usize(v_stop_1038_);
lean_dec(v_stop_1038_);
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_7305__boxed_1040_, v_as_1036_, v_i_boxed_1041_, v_stop_boxed_1042_, v_b_1039_);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object* v_s_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0));
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object* v_s_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v_s_1442_);
lean_dec_ref(v_s_1442_);
return v_res_1443_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1446_ = lean_nat_dec_eq(v___x_1445_, v___x_1444_);
return v___x_1446_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1447_ = lean_obj_once(&l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9, &l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9_once, _init_l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9);
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v___x_1448_);
lean_ctor_set(v___x_1450_, 2, v___x_1447_);
return v___x_1450_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1452_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2);
v___x_1455_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1456_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
lean_ctor_set(v___x_1456_, 1, v___x_1454_);
lean_ctor_set(v___x_1456_, 2, v___x_1453_);
lean_ctor_set(v___x_1456_, 3, v___x_1453_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object* v_s_1457_, lean_object* v_replacement_1458_){
_start:
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_1460_ = lean_uint8_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__3);
v___x_1462_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1457_, v_replacement_1458_, v___x_1461_, v___x_1459_);
return v___x_1462_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___x_1464_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1457_, v_replacement_1458_, v___x_1463_, v___x_1459_);
return v___x_1464_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object* v_s_1465_, lean_object* v_replacement_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1465_, v_replacement_1466_);
lean_dec_ref(v_replacement_1466_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object* v_s_1468_, lean_object* v___x_1469_, lean_object* v___x_1470_, lean_object* v_a_1471_, lean_object* v_b_1472_){
_start:
{
lean_object* v_it_1474_; lean_object* v_startInclusive_1475_; lean_object* v_endExclusive_1476_; 
if (lean_obj_tag(v_a_1471_) == 0)
{
lean_object* v_currPos_1484_; lean_object* v_searcher_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1513_; 
v_currPos_1484_ = lean_ctor_get(v_a_1471_, 0);
v_searcher_1485_ = lean_ctor_get(v_a_1471_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_a_1471_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1487_ = v_a_1471_;
v_isShared_1488_ = v_isSharedCheck_1513_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_searcher_1485_);
lean_inc(v_currPos_1484_);
lean_dec(v_a_1471_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1513_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
uint8_t v_decide_1499_; 
v_decide_1499_ = lean_nat_dec_eq(v_searcher_1485_, v___x_1470_);
if (v_decide_1499_ == 0)
{
uint32_t v___x_1500_; uint32_t v___x_1501_; uint8_t v___x_1502_; 
v___x_1500_ = lean_string_utf8_get_fast(v_s_1468_, v_searcher_1485_);
v___x_1501_ = 32;
v___x_1502_ = lean_uint32_dec_eq(v___x_1500_, v___x_1501_);
if (v___x_1502_ == 0)
{
uint32_t v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = 9;
v___x_1504_ = lean_uint32_dec_eq(v___x_1500_, v___x_1503_);
if (v___x_1504_ == 0)
{
uint32_t v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = 13;
v___x_1506_ = lean_uint32_dec_eq(v___x_1500_, v___x_1505_);
if (v___x_1506_ == 0)
{
uint32_t v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = 10;
v___x_1508_ = lean_uint32_dec_eq(v___x_1500_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_del_object(v___x_1487_);
v___x_1509_ = lean_string_utf8_next_fast(v_s_1468_, v_searcher_1485_);
lean_dec(v_searcher_1485_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_currPos_1484_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v_a_1471_ = v___x_1510_;
goto _start;
}
else
{
goto v___jp_1489_;
}
}
else
{
goto v___jp_1489_;
}
}
else
{
goto v___jp_1489_;
}
}
else
{
goto v___jp_1489_;
}
}
else
{
lean_object* v___x_1512_; 
lean_del_object(v___x_1487_);
lean_dec(v_searcher_1485_);
v___x_1512_ = lean_box(1);
lean_inc(v___x_1470_);
v_it_1474_ = v___x_1512_;
v_startInclusive_1475_ = v_currPos_1484_;
v_endExclusive_1476_ = v___x_1470_;
goto v___jp_1473_;
}
v___jp_1489_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v_slice_1493_; lean_object* v_nextIt_1495_; 
v___x_1490_ = lean_string_utf8_next_fast(v_s_1468_, v_searcher_1485_);
v___x_1491_ = lean_nat_sub(v___x_1490_, v_searcher_1485_);
v___x_1492_ = lean_nat_add(v_searcher_1485_, v___x_1491_);
lean_dec(v___x_1491_);
v_slice_1493_ = l_String_Slice_subslice_x21(v___x_1469_, v_currPos_1484_, v_searcher_1485_);
lean_inc(v___x_1492_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1492_);
lean_ctor_set(v___x_1487_, 0, v___x_1492_);
v_nextIt_1495_ = v___x_1487_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v___x_1492_);
v_nextIt_1495_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v_startInclusive_1496_; lean_object* v_endExclusive_1497_; 
v_startInclusive_1496_ = lean_ctor_get(v_slice_1493_, 0);
lean_inc(v_startInclusive_1496_);
v_endExclusive_1497_ = lean_ctor_get(v_slice_1493_, 1);
lean_inc(v_endExclusive_1497_);
lean_dec_ref(v_slice_1493_);
v_it_1474_ = v_nextIt_1495_;
v_startInclusive_1475_ = v_startInclusive_1496_;
v_endExclusive_1476_ = v_endExclusive_1497_;
goto v___jp_1473_;
}
}
}
}
else
{
lean_dec(v___x_1470_);
lean_dec_ref(v_s_1468_);
return v_b_1472_;
}
v___jp_1473_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1477_ = lean_nat_sub(v_endExclusive_1476_, v_startInclusive_1475_);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = lean_nat_dec_eq(v___x_1477_, v___x_1478_);
lean_dec(v___x_1477_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_inc_ref(v_s_1468_);
v___x_1480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1480_, 0, v_s_1468_);
lean_ctor_set(v___x_1480_, 1, v_startInclusive_1475_);
lean_ctor_set(v___x_1480_, 2, v_endExclusive_1476_);
v___x_1481_ = lean_array_push(v_b_1472_, v___x_1480_);
v_a_1471_ = v_it_1474_;
v_b_1472_ = v___x_1481_;
goto _start;
}
else
{
lean_dec(v_endExclusive_1476_);
lean_dec(v_startInclusive_1475_);
v_a_1471_ = v_it_1474_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object* v_s_1514_, lean_object* v___x_1515_, lean_object* v___x_1516_, lean_object* v_a_1517_, lean_object* v_b_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1514_, v___x_1515_, v___x_1516_, v_a_1517_, v_b_1518_);
lean_dec_ref(v___x_1515_);
return v_res_1519_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1521_ = lean_string_utf8_byte_size(v___x_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1522_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v___x_1523_);
lean_ctor_set(v___x_1525_, 2, v___x_1522_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t v_mode_1528_, lean_object* v_s_1529_){
_start:
{
switch(v_mode_1528_)
{
case 0:
{
return v_s_1529_;
}
case 1:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = lean_string_utf8_byte_size(v_s_1529_);
v___x_1533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1533_, 0, v_s_1529_);
lean_ctor_set(v___x_1533_, 1, v___x_1531_);
lean_ctor_set(v___x_1533_, 2, v___x_1532_);
v___x_1534_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v___x_1533_, v___x_1530_);
return v___x_1534_;
}
default: 
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1, &l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1_once, _init_l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1);
v___x_1537_ = lean_string_utf8_byte_size(v_s_1529_);
lean_inc_ref(v_s_1529_);
v___x_1538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1538_, 0, v_s_1529_);
lean_ctor_set(v___x_1538_, 1, v___x_1535_);
lean_ctor_set(v___x_1538_, 2, v___x_1537_);
v___x_1539_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v___x_1538_);
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__2));
v___x_1541_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1529_, v___x_1538_, v___x_1537_, v___x_1539_, v___x_1540_);
lean_dec_ref_known(v___x_1538_, 3);
v___x_1542_ = lean_array_to_list(v___x_1541_);
v___x_1543_ = l_String_Slice_intercalate(v___x_1536_, v___x_1542_);
lean_dec(v___x_1542_);
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object* v_mode_1544_, lean_object* v_s_1545_){
_start:
{
uint8_t v_mode_boxed_1546_; lean_object* v_res_1547_; 
v_mode_boxed_1546_ = lean_unbox(v_mode_1544_);
v_res_1547_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v_mode_boxed_1546_, v_s_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object* v_s_1548_, lean_object* v_pattern_1549_, lean_object* v_replacement_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1548_, v_replacement_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object* v_s_1552_, lean_object* v_pattern_1553_, lean_object* v_replacement_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(v_s_1552_, v_pattern_1553_, v_replacement_1554_);
lean_dec_ref(v_replacement_1554_);
lean_dec_ref(v_pattern_1553_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object* v_s_1556_, lean_object* v___x_1557_, lean_object* v___x_1558_, lean_object* v_inst_1559_, lean_object* v_R_1560_, lean_object* v_a_1561_, lean_object* v_b_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1556_, v___x_1557_, v___x_1558_, v_a_1561_, v_b_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___boxed(lean_object* v_s_1564_, lean_object* v___x_1565_, lean_object* v___x_1566_, lean_object* v_inst_1567_, lean_object* v_R_1568_, lean_object* v_a_1569_, lean_object* v_b_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(v_s_1564_, v___x_1565_, v___x_1566_, v_inst_1567_, v_R_1568_, v_a_1569_, v_b_1570_);
lean_dec_ref(v___x_1565_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(lean_object* v_hi_1572_, lean_object* v_pivot_1573_, lean_object* v_as_1574_, lean_object* v_i_1575_, lean_object* v_k_1576_){
_start:
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_nat_dec_lt(v_k_1576_, v_hi_1572_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v_k_1576_);
v___x_1578_ = lean_array_fswap(v_as_1574_, v_i_1575_, v_hi_1572_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_i_1575_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
return v___x_1579_;
}
else
{
lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = lean_array_fget_borrowed(v_as_1574_, v_k_1576_);
v___x_1581_ = lean_string_dec_lt(v___x_1580_, v_pivot_1573_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_unsigned_to_nat(1u);
v___x_1583_ = lean_nat_add(v_k_1576_, v___x_1582_);
lean_dec(v_k_1576_);
v_k_1576_ = v___x_1583_;
goto _start;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1585_ = lean_array_fswap(v_as_1574_, v_i_1575_, v_k_1576_);
v___x_1586_ = lean_unsigned_to_nat(1u);
v___x_1587_ = lean_nat_add(v_i_1575_, v___x_1586_);
lean_dec(v_i_1575_);
v___x_1588_ = lean_nat_add(v_k_1576_, v___x_1586_);
lean_dec(v_k_1576_);
v_as_1574_ = v___x_1585_;
v_i_1575_ = v___x_1587_;
v_k_1576_ = v___x_1588_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg___boxed(lean_object* v_hi_1590_, lean_object* v_pivot_1591_, lean_object* v_as_1592_, lean_object* v_i_1593_, lean_object* v_k_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1590_, v_pivot_1591_, v_as_1592_, v_i_1593_, v_k_1594_);
lean_dec_ref(v_pivot_1591_);
lean_dec(v_hi_1590_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object* v_n_1596_, lean_object* v_as_1597_, lean_object* v_lo_1598_, lean_object* v_hi_1599_){
_start:
{
lean_object* v___y_1601_; uint8_t v___x_1611_; 
v___x_1611_ = lean_nat_dec_lt(v_lo_1598_, v_hi_1599_);
if (v___x_1611_ == 0)
{
lean_dec(v_lo_1598_);
return v_as_1597_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v_mid_1614_; lean_object* v___y_1616_; lean_object* v___y_1622_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1612_ = lean_nat_add(v_lo_1598_, v_hi_1599_);
v___x_1613_ = lean_unsigned_to_nat(1u);
v_mid_1614_ = lean_nat_shiftr(v___x_1612_, v___x_1613_);
lean_dec(v___x_1612_);
v___x_1627_ = lean_array_fget_borrowed(v_as_1597_, v_mid_1614_);
v___x_1628_ = lean_array_fget_borrowed(v_as_1597_, v_lo_1598_);
v___x_1629_ = lean_string_dec_lt(v___x_1627_, v___x_1628_);
if (v___x_1629_ == 0)
{
v___y_1622_ = v_as_1597_;
goto v___jp_1621_;
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_array_fswap(v_as_1597_, v_lo_1598_, v_mid_1614_);
v___y_1622_ = v___x_1630_;
goto v___jp_1621_;
}
v___jp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1617_ = lean_array_fget_borrowed(v___y_1616_, v_mid_1614_);
v___x_1618_ = lean_array_fget_borrowed(v___y_1616_, v_hi_1599_);
v___x_1619_ = lean_string_dec_lt(v___x_1617_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_dec(v_mid_1614_);
v___y_1601_ = v___y_1616_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_array_fswap(v___y_1616_, v_mid_1614_, v_hi_1599_);
lean_dec(v_mid_1614_);
v___y_1601_ = v___x_1620_;
goto v___jp_1600_;
}
}
v___jp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1623_ = lean_array_fget_borrowed(v___y_1622_, v_hi_1599_);
v___x_1624_ = lean_array_fget_borrowed(v___y_1622_, v_lo_1598_);
v___x_1625_ = lean_string_dec_lt(v___x_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
v___y_1616_ = v___y_1622_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_array_fswap(v___y_1622_, v_lo_1598_, v_hi_1599_);
v___y_1616_ = v___x_1626_;
goto v___jp_1615_;
}
}
}
v___jp_1600_:
{
lean_object* v_pivot_1602_; lean_object* v___x_1603_; lean_object* v_fst_1604_; lean_object* v_snd_1605_; uint8_t v___x_1606_; 
v_pivot_1602_ = lean_array_fget(v___y_1601_, v_hi_1599_);
lean_inc_n(v_lo_1598_, 2);
v___x_1603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1599_, v_pivot_1602_, v___y_1601_, v_lo_1598_, v_lo_1598_);
lean_dec(v_pivot_1602_);
v_fst_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_fst_1604_);
v_snd_1605_ = lean_ctor_get(v___x_1603_, 1);
lean_inc(v_snd_1605_);
lean_dec_ref(v___x_1603_);
v___x_1606_ = lean_nat_dec_le(v_hi_1599_, v_fst_1604_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1596_, v_snd_1605_, v_lo_1598_, v_fst_1604_);
v___x_1608_ = lean_unsigned_to_nat(1u);
v___x_1609_ = lean_nat_add(v_fst_1604_, v___x_1608_);
lean_dec(v_fst_1604_);
v_as_1597_ = v___x_1607_;
v_lo_1598_ = v___x_1609_;
goto _start;
}
else
{
lean_dec(v_fst_1604_);
lean_dec(v_lo_1598_);
return v_snd_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object* v_n_1631_, lean_object* v_as_1632_, lean_object* v_lo_1633_, lean_object* v_hi_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1631_, v_as_1632_, v_lo_1633_, v_hi_1634_);
lean_dec(v_hi_1634_);
lean_dec(v_n_1631_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t v_mode_1636_, lean_object* v_msgs_1637_){
_start:
{
if (v_mode_1636_ == 0)
{
return v_msgs_1637_;
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1638_ = lean_array_mk(v_msgs_1637_);
v___x_1639_ = lean_array_get_size(v___x_1638_);
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1646_ = lean_nat_dec_eq(v___x_1639_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___y_1650_; uint8_t v___x_1652_; 
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_sub(v___x_1639_, v___x_1647_);
v___x_1652_ = lean_nat_dec_le(v___x_1645_, v___x_1648_);
if (v___x_1652_ == 0)
{
lean_inc(v___x_1648_);
v___y_1650_ = v___x_1648_;
goto v___jp_1649_;
}
else
{
v___y_1650_ = v___x_1645_;
goto v___jp_1649_;
}
v___jp_1649_:
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_nat_dec_le(v___y_1650_, v___x_1648_);
if (v___x_1651_ == 0)
{
lean_dec(v___x_1648_);
lean_inc(v___y_1650_);
v___y_1641_ = v___y_1650_;
v___y_1642_ = v___y_1650_;
goto v___jp_1640_;
}
else
{
v___y_1641_ = v___y_1650_;
v___y_1642_ = v___x_1648_;
goto v___jp_1640_;
}
}
}
else
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_array_to_list(v___x_1638_);
return v___x_1653_;
}
v___jp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v___x_1639_, v___x_1638_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
v___x_1644_ = lean_array_to_list(v___x_1643_);
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* v_mode_1654_, lean_object* v_msgs_1655_){
_start:
{
uint8_t v_mode_boxed_1656_; lean_object* v_res_1657_; 
v_mode_boxed_1656_ = lean_unbox(v_mode_1654_);
v_res_1657_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_boxed_1656_, v_msgs_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object* v_n_1658_, lean_object* v_as_1659_, lean_object* v_lo_1660_, lean_object* v_hi_1661_, lean_object* v_w_1662_, lean_object* v_hlo_1663_, lean_object* v_hhi_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1658_, v_as_1659_, v_lo_1660_, v_hi_1661_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object* v_n_1666_, lean_object* v_as_1667_, lean_object* v_lo_1668_, lean_object* v_hi_1669_, lean_object* v_w_1670_, lean_object* v_hlo_1671_, lean_object* v_hhi_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(v_n_1666_, v_as_1667_, v_lo_1668_, v_hi_1669_, v_w_1670_, v_hlo_1671_, v_hhi_1672_);
lean_dec(v_hi_1669_);
lean_dec(v_n_1666_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(lean_object* v_n_1674_, lean_object* v_lo_1675_, lean_object* v_hi_1676_, lean_object* v_hhi_1677_, lean_object* v_pivot_1678_, lean_object* v_as_1679_, lean_object* v_i_1680_, lean_object* v_k_1681_, lean_object* v_ilo_1682_, lean_object* v_ik_1683_, lean_object* v_w_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1676_, v_pivot_1678_, v_as_1679_, v_i_1680_, v_k_1681_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___boxed(lean_object* v_n_1686_, lean_object* v_lo_1687_, lean_object* v_hi_1688_, lean_object* v_hhi_1689_, lean_object* v_pivot_1690_, lean_object* v_as_1691_, lean_object* v_i_1692_, lean_object* v_k_1693_, lean_object* v_ilo_1694_, lean_object* v_ik_1695_, lean_object* v_w_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(v_n_1686_, v_lo_1687_, v_hi_1688_, v_hhi_1689_, v_pivot_1690_, v_as_1691_, v_i_1692_, v_k_1693_, v_ilo_1694_, v_ik_1695_, v_w_1696_);
lean_dec_ref(v_pivot_1690_);
lean_dec(v_hi_1688_);
lean_dec(v_lo_1687_);
lean_dec(v_n_1686_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object* v_as_1698_, size_t v_i_1699_, size_t v_stop_1700_, lean_object* v_b_1701_){
_start:
{
uint8_t v___x_1702_; 
v___x_1702_ = lean_usize_dec_eq(v_i_1699_, v_stop_1700_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v_diagnostics_1704_; lean_object* v_msgLog_1705_; lean_object* v___x_1706_; size_t v___x_1707_; size_t v___x_1708_; 
v___x_1703_ = lean_array_uget_borrowed(v_as_1698_, v_i_1699_);
v_diagnostics_1704_ = lean_ctor_get(v___x_1703_, 1);
v_msgLog_1705_ = lean_ctor_get(v_diagnostics_1704_, 0);
lean_inc_ref(v_msgLog_1705_);
v___x_1706_ = l_Lean_MessageLog_append(v_b_1701_, v_msgLog_1705_);
v___x_1707_ = ((size_t)1ULL);
v___x_1708_ = lean_usize_add(v_i_1699_, v___x_1707_);
v_i_1699_ = v___x_1708_;
v_b_1701_ = v___x_1706_;
goto _start;
}
else
{
return v_b_1701_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0___boxed(lean_object* v_as_1710_, lean_object* v_i_1711_, lean_object* v_stop_1712_, lean_object* v_b_1713_){
_start:
{
size_t v_i_boxed_1714_; size_t v_stop_boxed_1715_; lean_object* v_res_1716_; 
v_i_boxed_1714_ = lean_unbox_usize(v_i_1711_);
lean_dec(v_i_1711_);
v_stop_boxed_1715_ = lean_unbox_usize(v_stop_1712_);
lean_dec(v_stop_1712_);
v_res_1716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v_as_1710_, v_i_boxed_1714_, v_stop_boxed_1715_, v_b_1713_);
lean_dec_ref(v_as_1710_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object* v_as_1717_, size_t v_i_1718_, size_t v_stop_1719_, lean_object* v_b_1720_){
_start:
{
lean_object* v___y_1722_; uint8_t v___x_1726_; 
v___x_1726_ = lean_usize_dec_eq(v_i_1718_, v_stop_1719_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1727_ = lean_array_uget_borrowed(v_as_1717_, v_i_1718_);
v___x_1728_ = l_Lean_MessageLog_empty;
lean_inc(v___x_1727_);
v___x_1729_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1727_);
v___x_1730_ = l_Lean_Language_SnapshotTree_getAll(v___x_1729_);
v___x_1731_ = lean_unsigned_to_nat(0u);
v___x_1732_ = lean_array_get_size(v___x_1730_);
v___x_1733_ = lean_nat_dec_lt(v___x_1731_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_dec_ref(v___x_1730_);
v___x_1734_ = l_Lean_MessageLog_append(v_b_1720_, v___x_1728_);
v___y_1722_ = v___x_1734_;
goto v___jp_1721_;
}
else
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_nat_dec_le(v___x_1732_, v___x_1732_);
if (v___x_1735_ == 0)
{
if (v___x_1733_ == 0)
{
lean_object* v___x_1736_; 
lean_dec_ref(v___x_1730_);
v___x_1736_ = l_Lean_MessageLog_append(v_b_1720_, v___x_1728_);
v___y_1722_ = v___x_1736_;
goto v___jp_1721_;
}
else
{
size_t v___x_1737_; size_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1737_ = ((size_t)0ULL);
v___x_1738_ = lean_usize_of_nat(v___x_1732_);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1730_, v___x_1737_, v___x_1738_, v___x_1728_);
lean_dec_ref(v___x_1730_);
v___x_1740_ = l_Lean_MessageLog_append(v_b_1720_, v___x_1739_);
v___y_1722_ = v___x_1740_;
goto v___jp_1721_;
}
}
else
{
size_t v___x_1741_; size_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1741_ = ((size_t)0ULL);
v___x_1742_ = lean_usize_of_nat(v___x_1732_);
v___x_1743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1730_, v___x_1741_, v___x_1742_, v___x_1728_);
lean_dec_ref(v___x_1730_);
v___x_1744_ = l_Lean_MessageLog_append(v_b_1720_, v___x_1743_);
v___y_1722_ = v___x_1744_;
goto v___jp_1721_;
}
}
}
else
{
return v_b_1720_;
}
v___jp_1721_:
{
size_t v___x_1723_; size_t v___x_1724_; 
v___x_1723_ = ((size_t)1ULL);
v___x_1724_ = lean_usize_add(v_i_1718_, v___x_1723_);
v_i_1718_ = v___x_1724_;
v_b_1720_ = v___y_1722_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1___boxed(lean_object* v_as_1745_, lean_object* v_i_1746_, lean_object* v_stop_1747_, lean_object* v_b_1748_){
_start:
{
size_t v_i_boxed_1749_; size_t v_stop_boxed_1750_; lean_object* v_res_1751_; 
v_i_boxed_1749_ = lean_unbox_usize(v_i_1746_);
lean_dec(v_i_1746_);
v_stop_boxed_1750_ = lean_unbox_usize(v_stop_1747_);
lean_dec(v_stop_1747_);
v_res_1751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_as_1745_, v_i_boxed_1749_, v_stop_boxed_1750_, v_b_1748_);
lean_dec_ref(v_as_1745_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object* v_cmd_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_fileName_1758_; lean_object* v_fileMap_1759_; lean_object* v_currRecDepth_1760_; lean_object* v_cmdPos_1761_; lean_object* v_macroStack_1762_; lean_object* v_quotContext_x3f_1763_; lean_object* v_currMacroScope_1764_; lean_object* v_ref_1765_; lean_object* v_cancelTk_x3f_1766_; uint8_t v_suppressElabErrors_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_fileName_1758_ = lean_ctor_get(v_a_1755_, 0);
v_fileMap_1759_ = lean_ctor_get(v_a_1755_, 1);
v_currRecDepth_1760_ = lean_ctor_get(v_a_1755_, 2);
v_cmdPos_1761_ = lean_ctor_get(v_a_1755_, 3);
v_macroStack_1762_ = lean_ctor_get(v_a_1755_, 4);
v_quotContext_x3f_1763_ = lean_ctor_get(v_a_1755_, 5);
v_currMacroScope_1764_ = lean_ctor_get(v_a_1755_, 6);
v_ref_1765_ = lean_ctor_get(v_a_1755_, 7);
v_cancelTk_x3f_1766_ = lean_ctor_get(v_a_1755_, 9);
v_suppressElabErrors_1767_ = lean_ctor_get_uint8(v_a_1755_, sizeof(void*)*10);
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
v___x_1770_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1766_);
lean_inc(v_ref_1765_);
lean_inc(v_currMacroScope_1764_);
lean_inc(v_quotContext_x3f_1763_);
lean_inc(v_macroStack_1762_);
lean_inc(v_cmdPos_1761_);
lean_inc(v_currRecDepth_1760_);
lean_inc_ref(v_fileMap_1759_);
lean_inc_ref(v_fileName_1758_);
v___x_1771_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1771_, 0, v_fileName_1758_);
lean_ctor_set(v___x_1771_, 1, v_fileMap_1759_);
lean_ctor_set(v___x_1771_, 2, v_currRecDepth_1760_);
lean_ctor_set(v___x_1771_, 3, v_cmdPos_1761_);
lean_ctor_set(v___x_1771_, 4, v_macroStack_1762_);
lean_ctor_set(v___x_1771_, 5, v_quotContext_x3f_1763_);
lean_ctor_set(v___x_1771_, 6, v_currMacroScope_1764_);
lean_ctor_set(v___x_1771_, 7, v_ref_1765_);
lean_ctor_set(v___x_1771_, 8, v___x_1770_);
lean_ctor_set(v___x_1771_, 9, v_cancelTk_x3f_1766_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*10, v_suppressElabErrors_1767_);
v___x_1772_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1754_, v___x_1769_, v___x_1771_, v_a_1756_);
lean_dec_ref_known(v___x_1771_, 10);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1818_; 
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v___x_1772_, 0);
lean_dec(v_unused_1819_);
v___x_1774_ = v___x_1772_;
v_isShared_1775_ = v_isSharedCheck_1818_;
goto v_resetjp_1773_;
}
else
{
lean_dec(v___x_1772_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1818_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v_messages_1778_; lean_object* v___y_1780_; lean_object* v_snapshotTasks_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1776_ = lean_st_ref_get(v_a_1756_);
v___x_1777_ = lean_st_ref_get(v_a_1756_);
v_messages_1778_ = lean_ctor_get(v___x_1776_, 1);
lean_inc_ref(v_messages_1778_);
lean_dec(v___x_1776_);
v_snapshotTasks_1807_ = lean_ctor_get(v___x_1777_, 10);
lean_inc_ref(v_snapshotTasks_1807_);
lean_dec(v___x_1777_);
v___x_1808_ = l_Lean_MessageLog_empty;
v___x_1809_ = lean_array_get_size(v_snapshotTasks_1807_);
v___x_1810_ = lean_nat_dec_lt(v___x_1768_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_dec_ref(v_snapshotTasks_1807_);
v___y_1780_ = v___x_1808_;
goto v___jp_1779_;
}
else
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_nat_dec_le(v___x_1809_, v___x_1809_);
if (v___x_1811_ == 0)
{
if (v___x_1810_ == 0)
{
lean_dec_ref(v_snapshotTasks_1807_);
v___y_1780_ = v___x_1808_;
goto v___jp_1779_;
}
else
{
size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = lean_usize_of_nat(v___x_1809_);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1807_, v___x_1812_, v___x_1813_, v___x_1808_);
lean_dec_ref(v_snapshotTasks_1807_);
v___y_1780_ = v___x_1814_;
goto v___jp_1779_;
}
}
else
{
size_t v___x_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = ((size_t)0ULL);
v___x_1816_ = lean_usize_of_nat(v___x_1809_);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1807_, v___x_1815_, v___x_1816_, v___x_1808_);
lean_dec_ref(v_snapshotTasks_1807_);
v___y_1780_ = v___x_1817_;
goto v___jp_1779_;
}
}
v___jp_1779_:
{
lean_object* v___x_1781_; lean_object* v_env_1782_; lean_object* v_messages_1783_; lean_object* v_scopes_1784_; lean_object* v_usedQuotCtxts_1785_; lean_object* v_nextMacroScope_1786_; lean_object* v_maxRecDepth_1787_; lean_object* v_ngen_1788_; lean_object* v_auxDeclNGen_1789_; lean_object* v_infoState_1790_; lean_object* v_traceState_1791_; lean_object* v_prevLinterStates_1792_; lean_object* v_codeQualityEntryTasks_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1805_; 
v___x_1781_ = lean_st_ref_take(v_a_1756_);
v_env_1782_ = lean_ctor_get(v___x_1781_, 0);
v_messages_1783_ = lean_ctor_get(v___x_1781_, 1);
v_scopes_1784_ = lean_ctor_get(v___x_1781_, 2);
v_usedQuotCtxts_1785_ = lean_ctor_get(v___x_1781_, 3);
v_nextMacroScope_1786_ = lean_ctor_get(v___x_1781_, 4);
v_maxRecDepth_1787_ = lean_ctor_get(v___x_1781_, 5);
v_ngen_1788_ = lean_ctor_get(v___x_1781_, 6);
v_auxDeclNGen_1789_ = lean_ctor_get(v___x_1781_, 7);
v_infoState_1790_ = lean_ctor_get(v___x_1781_, 8);
v_traceState_1791_ = lean_ctor_get(v___x_1781_, 9);
v_prevLinterStates_1792_ = lean_ctor_get(v___x_1781_, 11);
v_codeQualityEntryTasks_1793_ = lean_ctor_get(v___x_1781_, 12);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; 
v_unused_1806_ = lean_ctor_get(v___x_1781_, 10);
lean_dec(v_unused_1806_);
v___x_1795_ = v___x_1781_;
v_isShared_1796_ = v_isSharedCheck_1805_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1793_);
lean_inc(v_prevLinterStates_1792_);
lean_inc(v_traceState_1791_);
lean_inc(v_infoState_1790_);
lean_inc(v_auxDeclNGen_1789_);
lean_inc(v_ngen_1788_);
lean_inc(v_maxRecDepth_1787_);
lean_inc(v_nextMacroScope_1786_);
lean_inc(v_usedQuotCtxts_1785_);
lean_inc(v_scopes_1784_);
lean_inc(v_messages_1783_);
lean_inc(v_env_1782_);
lean_dec(v___x_1781_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1805_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 10, v___x_1769_);
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_env_1782_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_messages_1783_);
lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_scopes_1784_);
lean_ctor_set(v_reuseFailAlloc_1804_, 3, v_usedQuotCtxts_1785_);
lean_ctor_set(v_reuseFailAlloc_1804_, 4, v_nextMacroScope_1786_);
lean_ctor_set(v_reuseFailAlloc_1804_, 5, v_maxRecDepth_1787_);
lean_ctor_set(v_reuseFailAlloc_1804_, 6, v_ngen_1788_);
lean_ctor_set(v_reuseFailAlloc_1804_, 7, v_auxDeclNGen_1789_);
lean_ctor_set(v_reuseFailAlloc_1804_, 8, v_infoState_1790_);
lean_ctor_set(v_reuseFailAlloc_1804_, 9, v_traceState_1791_);
lean_ctor_set(v_reuseFailAlloc_1804_, 10, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1804_, 11, v_prevLinterStates_1792_);
lean_ctor_set(v_reuseFailAlloc_1804_, 12, v_codeQualityEntryTasks_1793_);
v___x_1798_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1799_ = lean_st_ref_put(v_a_1756_, v___x_1798_);
v___x_1800_ = l_Lean_MessageLog_append(v_messages_1778_, v___y_1780_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1800_);
v___x_1802_ = v___x_1774_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_a_1820_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1772_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1772_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1828_, v_a_1829_, v_a_1830_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
return v_res_1832_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1833_, lean_object* v_opt_1834_){
_start:
{
lean_object* v_name_1835_; lean_object* v_defValue_1836_; lean_object* v_map_1837_; lean_object* v___x_1838_; 
v_name_1835_ = lean_ctor_get(v_opt_1834_, 0);
v_defValue_1836_ = lean_ctor_get(v_opt_1834_, 1);
v_map_1837_ = lean_ctor_get(v_opts_1833_, 0);
v___x_1838_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1837_, v_name_1835_);
if (lean_obj_tag(v___x_1838_) == 0)
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_unbox(v_defValue_1836_);
return v___x_1839_;
}
else
{
lean_object* v_val_1840_; 
v_val_1840_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v___x_1838_, 1);
if (lean_obj_tag(v_val_1840_) == 1)
{
uint8_t v_v_1841_; 
v_v_1841_ = lean_ctor_get_uint8(v_val_1840_, 0);
lean_dec_ref_known(v_val_1840_, 0);
return v_v_1841_;
}
else
{
uint8_t v___x_1842_; 
lean_dec(v_val_1840_);
v___x_1842_ = lean_unbox(v_defValue_1836_);
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1843_, lean_object* v_opt_1844_){
_start:
{
uint8_t v_res_1845_; lean_object* v_r_1846_; 
v_res_1845_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1843_, v_opt_1844_);
lean_dec_ref(v_opt_1844_);
lean_dec_ref(v_opts_1843_);
v_r_1846_ = lean_box(v_res_1845_);
return v_r_1846_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0));
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1851_);
lean_dec_ref(v_s_1851_);
return v_res_1852_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_box(1);
v___x_1854_ = l_Lean_MessageData_ofFormat(v___x_1853_);
return v___x_1854_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1859_ = l_Lean_MessageData_ofFormat(v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1860_, lean_object* v_x_1861_){
_start:
{
if (lean_obj_tag(v_x_1861_) == 0)
{
return v_x_1860_;
}
else
{
lean_object* v_head_1862_; lean_object* v_tail_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1885_; 
v_head_1862_ = lean_ctor_get(v_x_1861_, 0);
v_tail_1863_ = lean_ctor_get(v_x_1861_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_x_1861_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1865_ = v_x_1861_;
v_isShared_1866_ = v_isSharedCheck_1885_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_tail_1863_);
lean_inc(v_head_1862_);
lean_dec(v_x_1861_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1885_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_before_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1883_; 
v_before_1867_ = lean_ctor_get(v_head_1862_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_head_1862_);
if (v_isSharedCheck_1883_ == 0)
{
lean_object* v_unused_1884_; 
v_unused_1884_ = lean_ctor_get(v_head_1862_, 1);
lean_dec(v_unused_1884_);
v___x_1869_ = v_head_1862_;
v_isShared_1870_ = v_isSharedCheck_1883_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_before_1867_);
lean_dec(v_head_1862_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1883_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1871_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 7);
lean_ctor_set(v___x_1869_, 1, v___x_1871_);
lean_ctor_set(v___x_1869_, 0, v_x_1860_);
v___x_1873_ = v___x_1869_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_x_1860_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1866_ == 0)
{
lean_ctor_set_tag(v___x_1865_, 7);
lean_ctor_set(v___x_1865_, 1, v___x_1874_);
lean_ctor_set(v___x_1865_, 0, v___x_1873_);
v___x_1876_ = v___x_1865_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = l_Lean_MessageData_ofSyntax(v_before_1867_);
v___x_1878_ = l_Lean_indentD(v___x_1877_);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1876_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v_x_1860_ = v___x_1879_;
v_x_1861_ = v_tail_1863_;
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
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1890_ = l_Lean_MessageData_ofFormat(v___x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1891_, lean_object* v_macroStack_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v_scopes_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v_opts_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1895_ = lean_st_ref_get(v___y_1893_);
v_scopes_1896_ = lean_ctor_get(v___x_1895_, 2);
lean_inc(v_scopes_1896_);
lean_dec(v___x_1895_);
v___x_1897_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1898_ = l_List_head_x21___redArg(v___x_1897_, v_scopes_1896_);
lean_dec(v_scopes_1896_);
v_opts_1899_ = lean_ctor_get(v___x_1898_, 1);
lean_inc_ref(v_opts_1899_);
lean_dec(v___x_1898_);
v___x_1900_ = l_Lean_Elab_pp_macroStack;
v___x_1901_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1899_, v___x_1900_);
lean_dec_ref(v_opts_1899_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; 
lean_dec(v_macroStack_1892_);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v_msgData_1891_);
return v___x_1902_;
}
else
{
if (lean_obj_tag(v_macroStack_1892_) == 0)
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_msgData_1891_);
return v___x_1903_;
}
else
{
lean_object* v_head_1904_; lean_object* v_after_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1920_; 
v_head_1904_ = lean_ctor_get(v_macroStack_1892_, 0);
lean_inc(v_head_1904_);
v_after_1905_ = lean_ctor_get(v_head_1904_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_head_1904_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; 
v_unused_1921_ = lean_ctor_get(v_head_1904_, 0);
lean_dec(v_unused_1921_);
v___x_1907_ = v_head_1904_;
v_isShared_1908_ = v_isSharedCheck_1920_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_after_1905_);
lean_dec(v_head_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1920_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 7);
lean_ctor_set(v___x_1907_, 1, v___x_1909_);
lean_ctor_set(v___x_1907_, 0, v_msgData_1891_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_msgData_1891_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v_msgData_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1912_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = l_Lean_MessageData_ofSyntax(v_after_1905_);
v___x_1915_ = l_Lean_indentD(v___x_1914_);
v_msgData_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1916_, 0, v___x_1913_);
lean_ctor_set(v_msgData_1916_, 1, v___x_1915_);
v___x_1917_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1916_, v_macroStack_1892_);
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
return v___x_1918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1922_, lean_object* v_macroStack_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1922_, v_macroStack_1923_, v___y_1924_);
lean_dec(v___y_1924_);
return v_res_1926_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1927_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
lean_ctor_set(v___x_1932_, 2, v___x_1931_);
lean_ctor_set(v___x_1932_, 3, v___x_1931_);
lean_ctor_set(v___x_1932_, 4, v___x_1930_);
lean_ctor_set(v___x_1932_, 5, v___x_1930_);
lean_ctor_set(v___x_1932_, 6, v___x_1930_);
lean_ctor_set(v___x_1932_, 7, v___x_1930_);
lean_ctor_set(v___x_1932_, 8, v___x_1930_);
lean_ctor_set(v___x_1932_, 9, v___x_1930_);
lean_ctor_set(v___x_1932_, 10, v___x_1930_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = lean_unsigned_to_nat(32u);
v___x_1934_ = lean_mk_empty_array_with_capacity(v___x_1933_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1936_ = ((size_t)5ULL);
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = lean_unsigned_to_nat(32u);
v___x_1939_ = lean_mk_empty_array_with_capacity(v___x_1938_);
v___x_1940_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1941_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v___x_1939_);
lean_ctor_set(v___x_1941_, 2, v___x_1937_);
lean_ctor_set(v___x_1941_, 3, v___x_1937_);
lean_ctor_set_usize(v___x_1941_, 4, v___x_1936_);
return v___x_1941_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1942_ = lean_box(1);
v___x_1943_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1944_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v___x_1943_);
lean_ctor_set(v___x_1945_, 2, v___x_1942_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; lean_object* v_env_1950_; lean_object* v___x_1951_; lean_object* v_scopes_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v_opts_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1949_ = lean_st_ref_get(v___y_1947_);
v_env_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc_ref(v_env_1950_);
lean_dec(v___x_1949_);
v___x_1951_ = lean_st_ref_get(v___y_1947_);
v_scopes_1952_ = lean_ctor_get(v___x_1951_, 2);
lean_inc(v_scopes_1952_);
lean_dec(v___x_1951_);
v___x_1953_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1954_ = l_List_head_x21___redArg(v___x_1953_, v_scopes_1952_);
lean_dec(v_scopes_1952_);
v_opts_1955_ = lean_ctor_get(v___x_1954_, 1);
lean_inc_ref(v_opts_1955_);
lean_dec(v___x_1954_);
v___x_1956_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1957_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1958_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1958_, 0, v_env_1950_);
lean_ctor_set(v___x_1958_, 1, v___x_1956_);
lean_ctor_set(v___x_1958_, 2, v___x_1957_);
lean_ctor_set(v___x_1958_, 3, v_opts_1955_);
v___x_1959_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
lean_ctor_set(v___x_1959_, 1, v_msgData_1946_);
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1961_, v___y_1962_);
lean_dec(v___y_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Elab_Command_getRef___redArg(v___y_1966_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v_macroStack_1971_; lean_object* v___x_1972_; lean_object* v_a_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1984_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v_macroStack_1971_ = lean_ctor_get(v___y_1966_, 4);
v___x_1972_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1965_, v___y_1967_);
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref(v___x_1972_);
v___x_1974_ = l_Lean_Elab_getBetterRef(v_a_1970_, v_macroStack_1971_);
lean_dec(v_a_1970_);
lean_inc(v_macroStack_1971_);
v___x_1975_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1973_, v_macroStack_1971_, v___y_1967_);
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1974_);
lean_ctor_set(v___x_1980_, 1, v_a_1976_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set_tag(v___x_1978_, 1);
lean_ctor_set(v___x_1978_, 0, v___x_1980_);
v___x_1982_ = v___x_1978_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v_msg_1965_);
v_a_1985_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1969_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1969_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_1998_, lean_object* v_msg_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_Elab_Command_getRef___redArg(v___y_2000_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v_fileName_2005_; lean_object* v_fileMap_2006_; lean_object* v_currRecDepth_2007_; lean_object* v_cmdPos_2008_; lean_object* v_macroStack_2009_; lean_object* v_quotContext_x3f_2010_; lean_object* v_currMacroScope_2011_; lean_object* v_snap_x3f_2012_; lean_object* v_cancelTk_x3f_2013_; uint8_t v_suppressElabErrors_2014_; lean_object* v_ref_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v_fileName_2005_ = lean_ctor_get(v___y_2000_, 0);
v_fileMap_2006_ = lean_ctor_get(v___y_2000_, 1);
v_currRecDepth_2007_ = lean_ctor_get(v___y_2000_, 2);
v_cmdPos_2008_ = lean_ctor_get(v___y_2000_, 3);
v_macroStack_2009_ = lean_ctor_get(v___y_2000_, 4);
v_quotContext_x3f_2010_ = lean_ctor_get(v___y_2000_, 5);
v_currMacroScope_2011_ = lean_ctor_get(v___y_2000_, 6);
v_snap_x3f_2012_ = lean_ctor_get(v___y_2000_, 8);
v_cancelTk_x3f_2013_ = lean_ctor_get(v___y_2000_, 9);
v_suppressElabErrors_2014_ = lean_ctor_get_uint8(v___y_2000_, sizeof(void*)*10);
v_ref_2015_ = l_Lean_replaceRef(v_ref_1998_, v_a_2004_);
lean_dec(v_a_2004_);
lean_inc(v_cancelTk_x3f_2013_);
lean_inc(v_snap_x3f_2012_);
lean_inc(v_currMacroScope_2011_);
lean_inc(v_quotContext_x3f_2010_);
lean_inc(v_macroStack_2009_);
lean_inc(v_cmdPos_2008_);
lean_inc(v_currRecDepth_2007_);
lean_inc_ref(v_fileMap_2006_);
lean_inc_ref(v_fileName_2005_);
v___x_2016_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2016_, 0, v_fileName_2005_);
lean_ctor_set(v___x_2016_, 1, v_fileMap_2006_);
lean_ctor_set(v___x_2016_, 2, v_currRecDepth_2007_);
lean_ctor_set(v___x_2016_, 3, v_cmdPos_2008_);
lean_ctor_set(v___x_2016_, 4, v_macroStack_2009_);
lean_ctor_set(v___x_2016_, 5, v_quotContext_x3f_2010_);
lean_ctor_set(v___x_2016_, 6, v_currMacroScope_2011_);
lean_ctor_set(v___x_2016_, 7, v_ref_2015_);
lean_ctor_set(v___x_2016_, 8, v_snap_x3f_2012_);
lean_ctor_set(v___x_2016_, 9, v_cancelTk_x3f_2013_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*10, v_suppressElabErrors_2014_);
v___x_2017_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1999_, v___x_2016_, v___y_2001_);
lean_dec_ref_known(v___x_2016_, 10);
return v___x_2017_;
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec_ref(v_msg_1999_);
v_a_2018_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2003_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2003_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_2026_, lean_object* v_msg_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_2026_, v_msg_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v_ref_2026_);
return v_res_2031_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_2034_ = l_Lean_stringToMessageData(v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_val_2049_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_unsigned_to_nat(1u);
v___x_2057_ = l_Lean_Syntax_getArg(v_stx_2038_, v___x_2056_);
switch(lean_obj_tag(v___x_2057_))
{
case 2:
{
lean_object* v_val_2058_; 
lean_dec(v_stx_2038_);
v_val_2058_ = lean_ctor_get(v___x_2057_, 1);
lean_inc_ref(v_val_2058_);
lean_dec_ref_known(v___x_2057_, 2);
v_val_2049_ = v_val_2058_;
goto v___jp_2048_;
}
case 1:
{
lean_object* v_kind_2059_; 
v_kind_2059_ = lean_ctor_get(v___x_2057_, 1);
lean_inc(v_kind_2059_);
if (lean_obj_tag(v_kind_2059_) == 1)
{
lean_object* v_pre_2060_; 
v_pre_2060_ = lean_ctor_get(v_kind_2059_, 0);
lean_inc(v_pre_2060_);
if (lean_obj_tag(v_pre_2060_) == 1)
{
lean_object* v_pre_2061_; 
v_pre_2061_ = lean_ctor_get(v_pre_2060_, 0);
lean_inc(v_pre_2061_);
if (lean_obj_tag(v_pre_2061_) == 1)
{
lean_object* v_pre_2062_; 
v_pre_2062_ = lean_ctor_get(v_pre_2061_, 0);
lean_inc(v_pre_2062_);
if (lean_obj_tag(v_pre_2062_) == 1)
{
lean_object* v_pre_2063_; 
v_pre_2063_ = lean_ctor_get(v_pre_2062_, 0);
if (lean_obj_tag(v_pre_2063_) == 0)
{
lean_object* v_str_2064_; lean_object* v_str_2065_; lean_object* v_str_2066_; lean_object* v_str_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_str_2064_ = lean_ctor_get(v_kind_2059_, 1);
lean_inc_ref(v_str_2064_);
lean_dec_ref_known(v_kind_2059_, 2);
v_str_2065_ = lean_ctor_get(v_pre_2060_, 1);
lean_inc_ref(v_str_2065_);
lean_dec_ref_known(v_pre_2060_, 2);
v_str_2066_ = lean_ctor_get(v_pre_2061_, 1);
lean_inc_ref(v_str_2066_);
lean_dec_ref_known(v_pre_2061_, 2);
v_str_2067_ = lean_ctor_get(v_pre_2062_, 1);
lean_inc_ref(v_str_2067_);
lean_dec_ref_known(v_pre_2062_, 2);
v___x_2068_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_2069_ = lean_string_dec_eq(v_str_2067_, v___x_2068_);
lean_dec_ref(v_str_2067_);
if (v___x_2069_ == 0)
{
lean_dec_ref(v_str_2066_);
lean_dec_ref(v_str_2065_);
lean_dec_ref(v_str_2064_);
lean_dec_ref_known(v___x_2057_, 3);
goto v___jp_2042_;
}
else
{
lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2070_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2071_ = lean_string_dec_eq(v_str_2066_, v___x_2070_);
lean_dec_ref(v_str_2066_);
if (v___x_2071_ == 0)
{
lean_dec_ref(v_str_2065_);
lean_dec_ref(v_str_2064_);
lean_dec_ref_known(v___x_2057_, 3);
goto v___jp_2042_;
}
else
{
lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2072_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2073_ = lean_string_dec_eq(v_str_2065_, v___x_2072_);
lean_dec_ref(v_str_2065_);
if (v___x_2073_ == 0)
{
lean_dec_ref(v_str_2064_);
lean_dec_ref_known(v___x_2057_, 3);
goto v___jp_2042_;
}
else
{
lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2074_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2075_ = lean_string_dec_eq(v_str_2064_, v___x_2074_);
lean_dec_ref(v_str_2064_);
if (v___x_2075_ == 0)
{
lean_dec_ref_known(v___x_2057_, 3);
goto v___jp_2042_;
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_unsigned_to_nat(0u);
v___x_2077_ = l_Lean_Syntax_getArg(v___x_2057_, v___x_2076_);
lean_dec_ref_known(v___x_2057_, 3);
if (lean_obj_tag(v___x_2077_) == 2)
{
lean_object* v_val_2078_; 
lean_dec(v_stx_2038_);
v_val_2078_ = lean_ctor_get(v___x_2077_, 1);
lean_inc_ref(v_val_2078_);
lean_dec_ref_known(v___x_2077_, 2);
v_val_2049_ = v_val_2078_;
goto v___jp_2048_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec(v___x_2077_);
v___x_2079_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2038_);
v___x_2080_ = l_Lean_MessageData_ofSyntax(v_stx_2038_);
v___x_2081_ = l_Lean_indentD(v___x_2080_);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2079_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2038_, v___x_2082_, v___y_2039_, v___y_2040_);
lean_dec(v_stx_2038_);
return v___x_2083_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2062_, 2);
lean_dec_ref_known(v_pre_2061_, 2);
lean_dec_ref_known(v_pre_2060_, 2);
lean_dec_ref_known(v_kind_2059_, 2);
lean_dec_ref_known(v___x_2057_, 3);
goto v___jp_2042_;
}
}
else
{
lean_dec_ref_known(v_pre_2061_, 2);
lean_dec(v_pre_2062_);
lean_dec_ref_known(v_pre_2060_, 2);
lean_dec_ref_known(v_kind_2059_, 2);
lean_dec_ref_known(v___x_2057_, 3);
goto v___jp_2042_;
}
}
else
{
lean_dec_ref_known(v_pre_2060_, 2);
lean_dec(v_pre_2061_);
lean_dec_ref_known(v_kind_2059_, 2);
lean_dec_ref_known(v___x_2057_, 3);
goto v___jp_2042_;
}
}
else
{
lean_dec(v_pre_2060_);
lean_dec_ref_known(v_kind_2059_, 2);
lean_dec_ref_known(v___x_2057_, 3);
goto v___jp_2042_;
}
}
else
{
lean_dec(v_kind_2059_);
lean_dec_ref_known(v___x_2057_, 3);
goto v___jp_2042_;
}
}
default: 
{
lean_dec(v___x_2057_);
goto v___jp_2042_;
}
}
v___jp_2042_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2043_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2038_);
v___x_2044_ = l_Lean_MessageData_ofSyntax(v_stx_2038_);
v___x_2045_ = l_Lean_indentD(v___x_2044_);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2043_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2038_, v___x_2046_, v___y_2039_, v___y_2040_);
lean_dec(v_stx_2038_);
return v___x_2047_;
}
v___jp_2048_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = lean_string_utf8_byte_size(v_val_2049_);
v___x_2052_ = lean_unsigned_to_nat(2u);
v___x_2053_ = lean_nat_sub(v___x_2051_, v___x_2052_);
v___x_2054_ = lean_string_utf8_extract(v_val_2049_, v___x_2050_, v___x_2053_);
lean_dec(v___x_2053_);
lean_dec_ref(v_val_2049_);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2089_, size_t v_sz_2090_, size_t v_i_2091_, lean_object* v_b_2092_){
_start:
{
lean_object* v_a_2094_; uint8_t v___x_2098_; 
v___x_2098_ = lean_usize_dec_lt(v_i_2091_, v_sz_2090_);
if (v___x_2098_ == 0)
{
return v_b_2092_;
}
else
{
lean_object* v_a_2099_; lean_object* v_fst_2100_; lean_object* v_snd_2101_; lean_object* v_out_2102_; uint8_t v___x_2103_; 
v_a_2099_ = lean_array_uget_borrowed(v_as_2089_, v_i_2091_);
v_fst_2100_ = lean_ctor_get(v_a_2099_, 0);
v_snd_2101_ = lean_ctor_get(v_a_2099_, 1);
v_out_2102_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2103_ = lean_string_dec_eq(v_snd_2101_, v_out_2102_);
if (v___x_2103_ == 0)
{
uint8_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2104_ = lean_unbox(v_fst_2100_);
v___x_2105_ = l_Lean_Diff_Action_linePrefix(v___x_2104_);
v___x_2106_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2107_ = lean_string_append(v___x_2105_, v___x_2106_);
v___x_2108_ = lean_string_append(v___x_2107_, v_snd_2101_);
v___x_2109_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2110_ = lean_string_append(v___x_2108_, v___x_2109_);
v___x_2111_ = lean_string_append(v_b_2092_, v___x_2110_);
lean_dec_ref(v___x_2110_);
v_a_2094_ = v___x_2111_;
goto v___jp_2093_;
}
else
{
uint8_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2112_ = lean_unbox(v_fst_2100_);
v___x_2113_ = l_Lean_Diff_Action_linePrefix(v___x_2112_);
v___x_2114_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2115_ = lean_string_append(v___x_2113_, v___x_2114_);
v___x_2116_ = lean_string_append(v_b_2092_, v___x_2115_);
lean_dec_ref(v___x_2115_);
v_a_2094_ = v___x_2116_;
goto v___jp_2093_;
}
}
v___jp_2093_:
{
size_t v___x_2095_; size_t v___x_2096_; 
v___x_2095_ = ((size_t)1ULL);
v___x_2096_ = lean_usize_add(v_i_2091_, v___x_2095_);
v_i_2091_ = v___x_2096_;
v_b_2092_ = v_a_2094_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2117_, lean_object* v_sz_2118_, lean_object* v_i_2119_, lean_object* v_b_2120_){
_start:
{
size_t v_sz_boxed_2121_; size_t v_i_boxed_2122_; lean_object* v_res_2123_; 
v_sz_boxed_2121_ = lean_unbox_usize(v_sz_2118_);
lean_dec(v_sz_2118_);
v_i_boxed_2122_ = lean_unbox_usize(v_i_2119_);
lean_dec(v_i_2119_);
v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2117_, v_sz_boxed_2121_, v_i_boxed_2122_, v_b_2120_);
lean_dec_ref(v_as_2117_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2124_){
_start:
{
lean_object* v_out_2125_; size_t v_sz_2126_; size_t v___x_2127_; lean_object* v___x_2128_; 
v_out_2125_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v_sz_2126_ = lean_array_size(v_lines_2124_);
v___x_2127_ = ((size_t)0ULL);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2124_, v_sz_2126_, v___x_2127_, v_out_2125_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2129_);
lean_dec_ref(v_lines_2129_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2131_, lean_object* v_as_x27_2132_, lean_object* v_b_2133_){
_start:
{
if (lean_obj_tag(v_as_x27_2132_) == 0)
{
lean_object* v___x_2135_; 
lean_dec_ref(v_filterFn_2131_);
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_b_2133_);
return v___x_2135_;
}
else
{
lean_object* v_head_2136_; uint8_t v_isSilent_2137_; 
v_head_2136_ = lean_ctor_get(v_as_x27_2132_, 0);
v_isSilent_2137_ = lean_ctor_get_uint8(v_head_2136_, sizeof(void*)*5 + 2);
if (v_isSilent_2137_ == 0)
{
lean_object* v_tail_2138_; lean_object* v_fst_2139_; lean_object* v_snd_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2160_; 
v_tail_2138_ = lean_ctor_get(v_as_x27_2132_, 1);
v_fst_2139_ = lean_ctor_get(v_b_2133_, 0);
v_snd_2140_ = lean_ctor_get(v_b_2133_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_b_2133_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2142_ = v_b_2133_;
v_isShared_2143_ = v_isSharedCheck_2160_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_snd_2140_);
lean_inc(v_fst_2139_);
lean_dec(v_b_2133_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2160_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; uint8_t v___x_2145_; 
lean_inc_ref(v_filterFn_2131_);
lean_inc(v_head_2136_);
v___x_2144_ = lean_apply_1(v_filterFn_2131_, v_head_2136_);
v___x_2145_ = lean_unbox(v___x_2144_);
switch(v___x_2145_)
{
case 0:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_inc(v_head_2136_);
v___x_2146_ = l_Lean_MessageLog_add(v_head_2136_, v_fst_2139_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2146_);
v___x_2148_ = v___x_2142_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_snd_2140_);
v___x_2148_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
v_as_x27_2132_ = v_tail_2138_;
v_b_2133_ = v___x_2148_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2152_; 
if (v_isShared_2143_ == 0)
{
v___x_2152_ = v___x_2142_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_fst_2139_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_snd_2140_);
v___x_2152_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
v_as_x27_2132_ = v_tail_2138_;
v_b_2133_ = v___x_2152_;
goto _start;
}
}
default: 
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
lean_inc(v_head_2136_);
v___x_2155_ = l_Lean_MessageLog_add(v_head_2136_, v_snd_2140_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 1, v___x_2155_);
v___x_2157_ = v___x_2142_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_fst_2139_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
v_as_x27_2132_ = v_tail_2138_;
v_b_2133_ = v___x_2157_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2161_; lean_object* v_fst_2162_; lean_object* v_snd_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2171_; 
v_tail_2161_ = lean_ctor_get(v_as_x27_2132_, 1);
v_fst_2162_ = lean_ctor_get(v_b_2133_, 0);
v_snd_2163_ = lean_ctor_get(v_b_2133_, 1);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_b_2133_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2165_ = v_b_2133_;
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_snd_2163_);
lean_inc(v_fst_2162_);
lean_dec(v_b_2133_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_fst_2162_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_snd_2163_);
v___x_2168_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
v_as_x27_2132_ = v_tail_2161_;
v_b_2133_ = v___x_2168_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2172_, lean_object* v_as_x27_2173_, lean_object* v_b_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2172_, v_as_x27_2173_, v_b_2174_);
lean_dec(v_as_x27_2173_);
return v_res_2176_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2177_, lean_object* v_a_2178_, uint8_t v_b_2179_){
_start:
{
uint8_t v___x_2180_; 
v___x_2180_ = 0;
switch(lean_obj_tag(v_a_2178_))
{
case 0:
{
lean_object* v_pos_2181_; lean_object* v_startInclusive_2182_; lean_object* v_endExclusive_2183_; lean_object* v___x_2184_; uint8_t v_decide_2185_; 
v_pos_2181_ = lean_ctor_get(v_a_2178_, 0);
lean_inc(v_pos_2181_);
lean_dec_ref_known(v_a_2178_, 1);
v_startInclusive_2182_ = lean_ctor_get(v_s_2177_, 1);
v_endExclusive_2183_ = lean_ctor_get(v_s_2177_, 2);
v___x_2184_ = lean_nat_sub(v_endExclusive_2183_, v_startInclusive_2182_);
v_decide_2185_ = lean_nat_dec_eq(v_pos_2181_, v___x_2184_);
lean_dec(v___x_2184_);
lean_dec(v_pos_2181_);
if (v_decide_2185_ == 0)
{
uint8_t v___x_2186_; 
v___x_2186_ = 1;
return v___x_2186_;
}
else
{
return v_decide_2185_;
}
}
case 1:
{
lean_object* v_pos_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2200_; 
v_pos_2187_ = lean_ctor_get(v_a_2178_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_a_2178_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2189_ = v_a_2178_;
v_isShared_2190_ = v_isSharedCheck_2200_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_pos_2187_);
lean_dec(v_a_2178_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2200_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v_str_2191_; lean_object* v_startInclusive_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v_str_2191_ = lean_ctor_get(v_s_2177_, 0);
v_startInclusive_2192_ = lean_ctor_get(v_s_2177_, 1);
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
v_a_2178_ = v___x_2197_;
v_b_2179_ = v___x_2180_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2201_; lean_object* v_table_2202_; lean_object* v_stackPos_2203_; lean_object* v_needlePos_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2259_; 
v_needle_2201_ = lean_ctor_get(v_a_2178_, 0);
v_table_2202_ = lean_ctor_get(v_a_2178_, 1);
v_stackPos_2203_ = lean_ctor_get(v_a_2178_, 2);
v_needlePos_2204_ = lean_ctor_get(v_a_2178_, 3);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_a_2178_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2206_ = v_a_2178_;
v_isShared_2207_ = v_isSharedCheck_2259_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_needlePos_2204_);
lean_inc(v_stackPos_2203_);
lean_inc(v_table_2202_);
lean_inc(v_needle_2201_);
lean_dec(v_a_2178_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2259_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v_str_2208_; lean_object* v_startInclusive_2209_; lean_object* v_endExclusive_2210_; lean_object* v_str_2211_; lean_object* v_startInclusive_2212_; lean_object* v_endExclusive_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; 
v_str_2208_ = lean_ctor_get(v_needle_2201_, 0);
v_startInclusive_2209_ = lean_ctor_get(v_needle_2201_, 1);
v_endExclusive_2210_ = lean_ctor_get(v_needle_2201_, 2);
v_str_2211_ = lean_ctor_get(v_s_2177_, 0);
v_startInclusive_2212_ = lean_ctor_get(v_s_2177_, 1);
v_endExclusive_2213_ = lean_ctor_get(v_s_2177_, 2);
v___x_2214_ = lean_nat_sub(v_stackPos_2203_, v_needlePos_2204_);
v___x_2215_ = lean_nat_sub(v_endExclusive_2210_, v_startInclusive_2209_);
v___x_2216_ = lean_nat_add(v___x_2214_, v___x_2215_);
v___x_2217_ = lean_nat_sub(v_endExclusive_2213_, v_startInclusive_2212_);
v___x_2218_ = lean_nat_dec_le(v___x_2216_, v___x_2217_);
lean_dec(v___x_2216_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; 
lean_dec(v___x_2215_);
lean_del_object(v___x_2206_);
lean_dec(v_needlePos_2204_);
lean_dec(v_stackPos_2203_);
lean_dec_ref(v_table_2202_);
lean_dec_ref(v_needle_2201_);
v___x_2219_ = lean_unsigned_to_nat(1u);
v___x_2220_ = lean_nat_add(v___x_2214_, v___x_2219_);
lean_dec(v___x_2214_);
v___x_2221_ = lean_nat_dec_le(v___x_2220_, v___x_2217_);
lean_dec(v___x_2217_);
lean_dec(v___x_2220_);
if (v___x_2221_ == 0)
{
return v_b_2179_;
}
else
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_box(3);
v_a_2178_ = v___x_2222_;
v_b_2179_ = v___x_2180_;
goto _start;
}
}
else
{
lean_object* v___x_2224_; uint8_t v_stackByte_2225_; lean_object* v___x_2226_; uint8_t v_patByte_2227_; uint8_t v___x_2228_; 
lean_dec(v___x_2217_);
lean_dec(v___x_2214_);
v___x_2224_ = lean_nat_add(v_startInclusive_2212_, v_stackPos_2203_);
v_stackByte_2225_ = lean_string_get_byte_fast(v_str_2211_, v___x_2224_);
v___x_2226_ = lean_nat_add(v_startInclusive_2209_, v_needlePos_2204_);
v_patByte_2227_ = lean_string_get_byte_fast(v_str_2208_, v___x_2226_);
v___x_2228_ = lean_uint8_dec_eq(v_stackByte_2225_, v_patByte_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; uint8_t v_decide_2230_; 
lean_dec(v___x_2215_);
v___x_2229_ = lean_unsigned_to_nat(0u);
v_decide_2230_ = lean_nat_dec_eq(v_needlePos_2204_, v___x_2229_);
if (v_decide_2230_ == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v_newNeedlePos_2233_; uint8_t v___x_2234_; 
v___x_2231_ = lean_unsigned_to_nat(1u);
v___x_2232_ = lean_nat_sub(v_needlePos_2204_, v___x_2231_);
lean_dec(v_needlePos_2204_);
v_newNeedlePos_2233_ = lean_array_fget_borrowed(v_table_2202_, v___x_2232_);
lean_dec(v___x_2232_);
v___x_2234_ = lean_nat_dec_eq(v_newNeedlePos_2233_, v___x_2229_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2236_; 
lean_inc(v_newNeedlePos_2233_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 3, v_newNeedlePos_2233_);
v___x_2236_ = v___x_2206_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_needle_2201_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_table_2202_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_stackPos_2203_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_newNeedlePos_2233_);
v___x_2236_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
v_a_2178_ = v___x_2236_;
v_b_2179_ = v___x_2180_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2239_; lean_object* v___x_2241_; 
v_nextStackPos_2239_ = l_String_Slice_posGE___redArg(v_s_2177_, v_stackPos_2203_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 3, v___x_2229_);
lean_ctor_set(v___x_2206_, 2, v_nextStackPos_2239_);
v___x_2241_ = v___x_2206_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_needle_2201_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_table_2202_);
lean_ctor_set(v_reuseFailAlloc_2243_, 2, v_nextStackPos_2239_);
lean_ctor_set(v_reuseFailAlloc_2243_, 3, v___x_2229_);
v___x_2241_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
v_a_2178_ = v___x_2241_;
v_b_2179_ = v___x_2180_;
goto _start;
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v_nextStackPos_2246_; lean_object* v___x_2248_; 
lean_dec(v_needlePos_2204_);
v___x_2244_ = lean_unsigned_to_nat(1u);
v___x_2245_ = lean_nat_add(v_stackPos_2203_, v___x_2244_);
lean_dec(v_stackPos_2203_);
v_nextStackPos_2246_ = l_String_Slice_posGE___redArg(v_s_2177_, v___x_2245_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 3, v___x_2229_);
lean_ctor_set(v___x_2206_, 2, v_nextStackPos_2246_);
v___x_2248_ = v___x_2206_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_needle_2201_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_table_2202_);
lean_ctor_set(v_reuseFailAlloc_2250_, 2, v_nextStackPos_2246_);
lean_ctor_set(v_reuseFailAlloc_2250_, 3, v___x_2229_);
v___x_2248_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
v_a_2178_ = v___x_2248_;
v_b_2179_ = v___x_2180_;
goto _start;
}
}
}
else
{
lean_object* v___x_2251_; lean_object* v_nextNeedlePos_2252_; uint8_t v_decide_2253_; 
v___x_2251_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2252_ = lean_nat_add(v_needlePos_2204_, v___x_2251_);
lean_dec(v_needlePos_2204_);
v_decide_2253_ = lean_nat_dec_eq(v_nextNeedlePos_2252_, v___x_2215_);
lean_dec(v___x_2215_);
if (v_decide_2253_ == 0)
{
lean_object* v_nextStackPos_2254_; lean_object* v___x_2256_; 
v_nextStackPos_2254_ = lean_nat_add(v_stackPos_2203_, v___x_2251_);
lean_dec(v_stackPos_2203_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 3, v_nextNeedlePos_2252_);
lean_ctor_set(v___x_2206_, 2, v_nextStackPos_2254_);
v___x_2256_ = v___x_2206_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_needle_2201_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_table_2202_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_nextStackPos_2254_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_nextNeedlePos_2252_);
v___x_2256_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
v_a_2178_ = v___x_2256_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2252_);
lean_del_object(v___x_2206_);
lean_dec(v_stackPos_2203_);
lean_dec_ref(v_table_2202_);
lean_dec_ref(v_needle_2201_);
return v_decide_2253_;
}
}
}
}
}
default: 
{
return v_b_2179_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2260_, lean_object* v_a_2261_, lean_object* v_b_2262_){
_start:
{
uint8_t v_b_boxed_2263_; uint8_t v_res_2264_; lean_object* v_r_2265_; 
v_b_boxed_2263_ = lean_unbox(v_b_2262_);
v_res_2264_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2260_, v_a_2261_, v_b_boxed_2263_);
lean_dec_ref(v_s_2260_);
v_r_2265_ = lean_box(v_res_2264_);
return v_r_2265_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2266_, lean_object* v_s_2267_){
_start:
{
lean_object* v___y_2269_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2272_ = lean_unsigned_to_nat(0u);
v___x_2273_ = lean_string_utf8_byte_size(v___x_2266_);
v___x_2274_ = lean_nat_dec_eq(v___x_2273_, v___x_2272_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2266_);
lean_ctor_set(v___x_2275_, 1, v___x_2272_);
lean_ctor_set(v___x_2275_, 2, v___x_2273_);
v___x_2276_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2275_);
v___x_2277_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
lean_ctor_set(v___x_2277_, 2, v___x_2272_);
lean_ctor_set(v___x_2277_, 3, v___x_2272_);
v___y_2269_ = v___x_2277_;
goto v___jp_2268_;
}
else
{
lean_object* v___x_2278_; 
lean_dec_ref(v___x_2266_);
v___x_2278_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_2269_ = v___x_2278_;
goto v___jp_2268_;
}
v___jp_2268_:
{
uint8_t v___x_2270_; uint8_t v___x_2271_; 
v___x_2270_ = 0;
v___x_2271_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2267_, v___y_2269_, v___x_2270_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2279_, lean_object* v_s_2280_){
_start:
{
uint8_t v_res_2281_; lean_object* v_r_2282_; 
v_res_2281_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2279_, v_s_2280_);
lean_dec_ref(v_s_2280_);
v_r_2282_ = lean_box(v_res_2281_);
return v_r_2282_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v_suppressElabErrors_2283_, uint8_t v___y_2284_, lean_object* v_x_2285_){
_start:
{
if (lean_obj_tag(v_x_2285_) == 1)
{
lean_object* v_pre_2286_; 
v_pre_2286_ = lean_ctor_get(v_x_2285_, 0);
if (lean_obj_tag(v_pre_2286_) == 0)
{
lean_object* v_str_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_str_2287_ = lean_ctor_get(v_x_2285_, 1);
v___x_2288_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2289_ = lean_string_dec_eq(v_str_2287_, v___x_2288_);
if (v___x_2289_ == 0)
{
return v___x_2289_;
}
else
{
return v_suppressElabErrors_2283_;
}
}
else
{
return v___y_2284_;
}
}
else
{
return v___y_2284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_2290_, lean_object* v___y_2291_, lean_object* v_x_2292_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2293_; uint8_t v___y_26064__boxed_2294_; uint8_t v_res_2295_; lean_object* v_r_2296_; 
v_suppressElabErrors_boxed_2293_ = lean_unbox(v_suppressElabErrors_2290_);
v___y_26064__boxed_2294_ = lean_unbox(v___y_2291_);
v_res_2295_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v_suppressElabErrors_boxed_2293_, v___y_26064__boxed_2294_, v_x_2292_);
lean_dec(v_x_2292_);
v_r_2296_ = lean_box(v_res_2295_);
return v_r_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2297_, lean_object* v_msgData_2298_, uint8_t v_severity_2299_, uint8_t v_isSilent_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; uint8_t v___y_2309_; lean_object* v___y_2310_; uint8_t v___y_2311_; lean_object* v___y_2312_; uint8_t v___y_2370_; lean_object* v___y_2371_; uint8_t v___y_2372_; uint8_t v___y_2373_; lean_object* v___y_2374_; uint8_t v___y_2398_; lean_object* v___y_2399_; uint8_t v___y_2400_; uint8_t v___y_2401_; lean_object* v___y_2402_; uint8_t v___y_2406_; uint8_t v___y_2407_; uint8_t v___y_2408_; uint8_t v___x_2423_; uint8_t v___y_2425_; uint8_t v___y_2426_; uint8_t v___y_2427_; uint8_t v___y_2429_; uint8_t v___x_2441_; 
v___x_2423_ = 2;
v___x_2441_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2299_, v___x_2423_);
if (v___x_2441_ == 0)
{
v___y_2429_ = v___x_2441_;
goto v___jp_2428_;
}
else
{
uint8_t v___x_2442_; 
lean_inc_ref(v_msgData_2298_);
v___x_2442_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2298_);
v___y_2429_ = v___x_2442_;
goto v___jp_2428_;
}
v___jp_2304_:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_Elab_Command_getScope___redArg(v___y_2312_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2315_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2315_ = l_Lean_Elab_Command_getScope___redArg(v___y_2312_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2352_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2352_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2352_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; lean_object* v_currNamespace_2321_; lean_object* v_openDecls_2322_; lean_object* v_env_2323_; lean_object* v_messages_2324_; lean_object* v_scopes_2325_; lean_object* v_usedQuotCtxts_2326_; lean_object* v_nextMacroScope_2327_; lean_object* v_maxRecDepth_2328_; lean_object* v_ngen_2329_; lean_object* v_auxDeclNGen_2330_; lean_object* v_infoState_2331_; lean_object* v_traceState_2332_; lean_object* v_snapshotTasks_2333_; lean_object* v_prevLinterStates_2334_; lean_object* v_codeQualityEntryTasks_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2351_; 
v___x_2320_ = lean_st_ref_take(v___y_2312_);
v_currNamespace_2321_ = lean_ctor_get(v_a_2314_, 2);
lean_inc(v_currNamespace_2321_);
lean_dec(v_a_2314_);
v_openDecls_2322_ = lean_ctor_get(v_a_2316_, 3);
lean_inc(v_openDecls_2322_);
lean_dec(v_a_2316_);
v_env_2323_ = lean_ctor_get(v___x_2320_, 0);
v_messages_2324_ = lean_ctor_get(v___x_2320_, 1);
v_scopes_2325_ = lean_ctor_get(v___x_2320_, 2);
v_usedQuotCtxts_2326_ = lean_ctor_get(v___x_2320_, 3);
v_nextMacroScope_2327_ = lean_ctor_get(v___x_2320_, 4);
v_maxRecDepth_2328_ = lean_ctor_get(v___x_2320_, 5);
v_ngen_2329_ = lean_ctor_get(v___x_2320_, 6);
v_auxDeclNGen_2330_ = lean_ctor_get(v___x_2320_, 7);
v_infoState_2331_ = lean_ctor_get(v___x_2320_, 8);
v_traceState_2332_ = lean_ctor_get(v___x_2320_, 9);
v_snapshotTasks_2333_ = lean_ctor_get(v___x_2320_, 10);
v_prevLinterStates_2334_ = lean_ctor_get(v___x_2320_, 11);
v_codeQualityEntryTasks_2335_ = lean_ctor_get(v___x_2320_, 12);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2337_ = v___x_2320_;
v_isShared_2338_ = v_isSharedCheck_2351_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2335_);
lean_inc(v_prevLinterStates_2334_);
lean_inc(v_snapshotTasks_2333_);
lean_inc(v_traceState_2332_);
lean_inc(v_infoState_2331_);
lean_inc(v_auxDeclNGen_2330_);
lean_inc(v_ngen_2329_);
lean_inc(v_maxRecDepth_2328_);
lean_inc(v_nextMacroScope_2327_);
lean_inc(v_usedQuotCtxts_2326_);
lean_inc(v_scopes_2325_);
lean_inc(v_messages_2324_);
lean_inc(v_env_2323_);
lean_dec(v___x_2320_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2351_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2339_, 0, v_currNamespace_2321_);
lean_ctor_set(v___x_2339_, 1, v_openDecls_2322_);
v___x_2340_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v___y_2310_);
lean_inc_ref(v___y_2307_);
lean_inc_ref(v___y_2308_);
v___x_2341_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2341_, 0, v___y_2308_);
lean_ctor_set(v___x_2341_, 1, v___y_2305_);
lean_ctor_set(v___x_2341_, 2, v___y_2306_);
lean_ctor_set(v___x_2341_, 3, v___y_2307_);
lean_ctor_set(v___x_2341_, 4, v___x_2340_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*5, v___y_2311_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*5 + 1, v___y_2309_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*5 + 2, v_isSilent_2300_);
v___x_2342_ = l_Lean_MessageLog_add(v___x_2341_, v_messages_2324_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 1, v___x_2342_);
v___x_2344_ = v___x_2337_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_env_2323_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2350_, 2, v_scopes_2325_);
lean_ctor_set(v_reuseFailAlloc_2350_, 3, v_usedQuotCtxts_2326_);
lean_ctor_set(v_reuseFailAlloc_2350_, 4, v_nextMacroScope_2327_);
lean_ctor_set(v_reuseFailAlloc_2350_, 5, v_maxRecDepth_2328_);
lean_ctor_set(v_reuseFailAlloc_2350_, 6, v_ngen_2329_);
lean_ctor_set(v_reuseFailAlloc_2350_, 7, v_auxDeclNGen_2330_);
lean_ctor_set(v_reuseFailAlloc_2350_, 8, v_infoState_2331_);
lean_ctor_set(v_reuseFailAlloc_2350_, 9, v_traceState_2332_);
lean_ctor_set(v_reuseFailAlloc_2350_, 10, v_snapshotTasks_2333_);
lean_ctor_set(v_reuseFailAlloc_2350_, 11, v_prevLinterStates_2334_);
lean_ctor_set(v_reuseFailAlloc_2350_, 12, v_codeQualityEntryTasks_2335_);
v___x_2344_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2345_ = lean_st_ref_put(v___y_2312_, v___x_2344_);
v___x_2346_ = lean_box(0);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2346_);
v___x_2348_ = v___x_2318_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec(v_a_2314_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
v_a_2353_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2315_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2315_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
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
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
v_a_2361_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2313_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2313_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
v___jp_2369_:
{
lean_object* v_fileName_2375_; lean_object* v_fileMap_2376_; uint8_t v_suppressElabErrors_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2396_; 
v_fileName_2375_ = lean_ctor_get(v___y_2301_, 0);
v_fileMap_2376_ = lean_ctor_get(v___y_2301_, 1);
v_suppressElabErrors_2377_ = lean_ctor_get_uint8(v___y_2301_, sizeof(void*)*10);
v___x_2378_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2298_);
v___x_2379_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2378_, v___y_2302_);
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2396_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2396_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
lean_inc_ref_n(v_fileMap_2376_, 2);
v___x_2384_ = l_Lean_FileMap_toPosition(v_fileMap_2376_, v___y_2371_);
lean_dec(v___y_2371_);
v___x_2385_ = l_Lean_FileMap_toPosition(v_fileMap_2376_, v___y_2374_);
lean_dec(v___y_2374_);
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
v___x_2387_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
if (v_suppressElabErrors_2377_ == 0)
{
lean_del_object(v___x_2382_);
v___y_2305_ = v___x_2384_;
v___y_2306_ = v___x_2386_;
v___y_2307_ = v___x_2387_;
v___y_2308_ = v_fileName_2375_;
v___y_2309_ = v___y_2372_;
v___y_2310_ = v_a_2380_;
v___y_2311_ = v___y_2373_;
v___y_2312_ = v___y_2302_;
goto v___jp_2304_;
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___f_2390_; uint8_t v___x_2391_; 
v___x_2388_ = lean_box(v_suppressElabErrors_2377_);
v___x_2389_ = lean_box(v___y_2370_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2390_, 0, v___x_2388_);
lean_closure_set(v___f_2390_, 1, v___x_2389_);
lean_inc(v_a_2380_);
v___x_2391_ = l_Lean_MessageData_hasTag(v___f_2390_, v_a_2380_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
lean_dec_ref_known(v___x_2386_, 1);
lean_dec_ref(v___x_2384_);
lean_dec(v_a_2380_);
v___x_2392_ = lean_box(0);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2392_);
v___x_2394_ = v___x_2382_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
else
{
lean_del_object(v___x_2382_);
v___y_2305_ = v___x_2384_;
v___y_2306_ = v___x_2386_;
v___y_2307_ = v___x_2387_;
v___y_2308_ = v_fileName_2375_;
v___y_2309_ = v___y_2372_;
v___y_2310_ = v_a_2380_;
v___y_2311_ = v___y_2373_;
v___y_2312_ = v___y_2302_;
goto v___jp_2304_;
}
}
}
}
v___jp_2397_:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_Syntax_getTailPos_x3f(v___y_2399_, v___y_2401_);
lean_dec(v___y_2399_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_inc(v___y_2402_);
v___y_2370_ = v___y_2398_;
v___y_2371_ = v___y_2402_;
v___y_2372_ = v___y_2400_;
v___y_2373_ = v___y_2401_;
v___y_2374_ = v___y_2402_;
goto v___jp_2369_;
}
else
{
lean_object* v_val_2404_; 
v_val_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_val_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___y_2370_ = v___y_2398_;
v___y_2371_ = v___y_2402_;
v___y_2372_ = v___y_2400_;
v___y_2373_ = v___y_2401_;
v___y_2374_ = v_val_2404_;
goto v___jp_2369_;
}
}
v___jp_2405_:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Elab_Command_getRef___redArg(v___y_2301_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v_ref_2411_; lean_object* v___x_2412_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v_ref_2411_ = l_Lean_replaceRef(v_ref_2297_, v_a_2410_);
lean_dec(v_a_2410_);
v___x_2412_ = l_Lean_Syntax_getPos_x3f(v_ref_2411_, v___y_2407_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_unsigned_to_nat(0u);
v___y_2398_ = v___y_2406_;
v___y_2399_ = v_ref_2411_;
v___y_2400_ = v___y_2408_;
v___y_2401_ = v___y_2407_;
v___y_2402_ = v___x_2413_;
goto v___jp_2397_;
}
else
{
lean_object* v_val_2414_; 
v_val_2414_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_val_2414_);
lean_dec_ref_known(v___x_2412_, 1);
v___y_2398_ = v___y_2406_;
v___y_2399_ = v_ref_2411_;
v___y_2400_ = v___y_2408_;
v___y_2401_ = v___y_2407_;
v___y_2402_ = v_val_2414_;
goto v___jp_2397_;
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec_ref(v_msgData_2298_);
v_a_2415_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2409_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2409_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
v___jp_2424_:
{
if (v___y_2427_ == 0)
{
v___y_2406_ = v___y_2425_;
v___y_2407_ = v___y_2426_;
v___y_2408_ = v_severity_2299_;
goto v___jp_2405_;
}
else
{
v___y_2406_ = v___y_2425_;
v___y_2407_ = v___y_2426_;
v___y_2408_ = v___x_2423_;
goto v___jp_2405_;
}
}
v___jp_2428_:
{
if (v___y_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v_scopes_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_opts_2434_; uint8_t v___x_2435_; uint8_t v___x_2436_; 
v___x_2430_ = lean_st_ref_get(v___y_2302_);
v_scopes_2431_ = lean_ctor_get(v___x_2430_, 2);
lean_inc(v_scopes_2431_);
lean_dec(v___x_2430_);
v___x_2432_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2433_ = l_List_head_x21___redArg(v___x_2432_, v_scopes_2431_);
lean_dec(v_scopes_2431_);
v_opts_2434_ = lean_ctor_get(v___x_2433_, 1);
lean_inc_ref(v_opts_2434_);
lean_dec(v___x_2433_);
v___x_2435_ = 1;
v___x_2436_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2299_, v___x_2435_);
if (v___x_2436_ == 0)
{
lean_dec_ref(v_opts_2434_);
v___y_2425_ = v___y_2429_;
v___y_2426_ = v___y_2429_;
v___y_2427_ = v___x_2436_;
goto v___jp_2424_;
}
else
{
lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2437_ = l_Lean_warningAsError;
v___x_2438_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2434_, v___x_2437_);
lean_dec_ref(v_opts_2434_);
v___y_2425_ = v___y_2429_;
v___y_2426_ = v___y_2429_;
v___y_2427_ = v___x_2438_;
goto v___jp_2424_;
}
}
else
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
lean_dec_ref(v_msgData_2298_);
v___x_2439_ = lean_box(0);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2443_, lean_object* v_msgData_2444_, lean_object* v_severity_2445_, lean_object* v_isSilent_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
uint8_t v_severity_boxed_2450_; uint8_t v_isSilent_boxed_2451_; lean_object* v_res_2452_; 
v_severity_boxed_2450_ = lean_unbox(v_severity_2445_);
v_isSilent_boxed_2451_ = lean_unbox(v_isSilent_2446_);
v_res_2452_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2443_, v_msgData_2444_, v_severity_boxed_2450_, v_isSilent_boxed_2451_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v_ref_2443_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2453_, lean_object* v_msgData_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
uint8_t v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = 2;
v___x_2459_ = 0;
v___x_2460_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2453_, v_msgData_2454_, v___x_2458_, v___x_2459_, v___y_2455_, v___y_2456_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2461_, lean_object* v_msgData_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2461_, v_msgData_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v_ref_2461_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2467_, lean_object* v___x_2468_, lean_object* v___x_2469_, lean_object* v_a_2470_, lean_object* v_b_2471_){
_start:
{
lean_object* v_it_2473_; lean_object* v_startInclusive_2474_; lean_object* v_endExclusive_2475_; 
if (lean_obj_tag(v_a_2470_) == 0)
{
lean_object* v_currPos_2480_; lean_object* v_searcher_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2510_; 
v_currPos_2480_ = lean_ctor_get(v_a_2470_, 0);
v_searcher_2481_ = lean_ctor_get(v_a_2470_, 1);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_a_2470_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2483_ = v_a_2470_;
v_isShared_2484_ = v_isSharedCheck_2510_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_searcher_2481_);
lean_inc(v_currPos_2480_);
lean_dec(v_a_2470_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2510_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v_str_2485_; lean_object* v_startInclusive_2486_; lean_object* v_endExclusive_2487_; lean_object* v___x_2488_; uint8_t v_decide_2489_; 
v_str_2485_ = lean_ctor_get(v___x_2468_, 0);
v_startInclusive_2486_ = lean_ctor_get(v___x_2468_, 1);
v_endExclusive_2487_ = lean_ctor_get(v___x_2468_, 2);
v___x_2488_ = lean_nat_sub(v_endExclusive_2487_, v_startInclusive_2486_);
v_decide_2489_ = lean_nat_dec_eq(v_searcher_2481_, v___x_2488_);
lean_dec(v___x_2488_);
if (v_decide_2489_ == 0)
{
uint32_t v___x_2490_; lean_object* v___x_2491_; uint32_t v___x_2492_; uint8_t v___x_2493_; 
v___x_2490_ = 10;
v___x_2491_ = lean_nat_add(v_startInclusive_2486_, v_searcher_2481_);
v___x_2492_ = lean_string_utf8_get_fast(v_str_2485_, v___x_2491_);
v___x_2493_ = lean_uint32_dec_eq(v___x_2492_, v___x_2490_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
lean_dec(v_searcher_2481_);
v___x_2494_ = lean_string_utf8_next_fast(v_str_2485_, v___x_2491_);
lean_dec(v___x_2491_);
v___x_2495_ = lean_nat_sub(v___x_2494_, v_startInclusive_2486_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 1, v___x_2495_);
v___x_2497_ = v___x_2483_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_currPos_2480_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
v_a_2470_ = v___x_2497_;
goto _start;
}
}
else
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v_slice_2503_; lean_object* v_nextIt_2505_; 
v___x_2500_ = lean_string_utf8_next_fast(v_str_2485_, v___x_2491_);
v___x_2501_ = lean_nat_sub(v___x_2500_, v___x_2491_);
lean_dec(v___x_2491_);
v___x_2502_ = lean_nat_add(v_searcher_2481_, v___x_2501_);
lean_dec(v___x_2501_);
v_slice_2503_ = l_String_Slice_subslice_x21(v___x_2468_, v_currPos_2480_, v_searcher_2481_);
lean_inc(v___x_2502_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 1, v___x_2502_);
lean_ctor_set(v___x_2483_, 0, v___x_2502_);
v_nextIt_2505_ = v___x_2483_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v___x_2502_);
v_nextIt_2505_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v_startInclusive_2506_; lean_object* v_endExclusive_2507_; 
v_startInclusive_2506_ = lean_ctor_get(v_slice_2503_, 0);
lean_inc(v_startInclusive_2506_);
v_endExclusive_2507_ = lean_ctor_get(v_slice_2503_, 1);
lean_inc(v_endExclusive_2507_);
lean_dec_ref(v_slice_2503_);
v_it_2473_ = v_nextIt_2505_;
v_startInclusive_2474_ = v_startInclusive_2506_;
v_endExclusive_2475_ = v_endExclusive_2507_;
goto v___jp_2472_;
}
}
}
else
{
lean_object* v___x_2509_; 
lean_del_object(v___x_2483_);
lean_dec(v_searcher_2481_);
v___x_2509_ = lean_box(1);
lean_inc(v___x_2469_);
v_it_2473_ = v___x_2509_;
v_startInclusive_2474_ = v_currPos_2480_;
v_endExclusive_2475_ = v___x_2469_;
goto v___jp_2472_;
}
}
}
else
{
lean_dec(v___x_2469_);
lean_dec_ref(v___x_2467_);
return v_b_2471_;
}
v___jp_2472_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
lean_inc_ref(v___x_2467_);
v___x_2476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2467_);
lean_ctor_set(v___x_2476_, 1, v_startInclusive_2474_);
lean_ctor_set(v___x_2476_, 2, v_endExclusive_2475_);
v___x_2477_ = l_String_Slice_toString(v___x_2476_);
lean_dec_ref_known(v___x_2476_, 3);
v___x_2478_ = lean_array_push(v_b_2471_, v___x_2477_);
v_a_2470_ = v_it_2473_;
v_b_2471_ = v___x_2478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2511_, lean_object* v___x_2512_, lean_object* v___x_2513_, lean_object* v_a_2514_, lean_object* v_b_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2511_, v___x_2512_, v___x_2513_, v_a_2514_, v_b_2515_);
lean_dec_ref(v___x_2512_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2517_, lean_object* v___x_2518_, lean_object* v___x_2519_, lean_object* v_a_2520_, lean_object* v_b_2521_){
_start:
{
lean_object* v_it_2523_; lean_object* v_startInclusive_2524_; lean_object* v_endExclusive_2525_; 
if (lean_obj_tag(v_a_2520_) == 0)
{
lean_object* v_currPos_2530_; lean_object* v_searcher_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2560_; 
v_currPos_2530_ = lean_ctor_get(v_a_2520_, 0);
v_searcher_2531_ = lean_ctor_get(v_a_2520_, 1);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_a_2520_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2533_ = v_a_2520_;
v_isShared_2534_ = v_isSharedCheck_2560_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_searcher_2531_);
lean_inc(v_currPos_2530_);
lean_dec(v_a_2520_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2560_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v_str_2535_; lean_object* v_startInclusive_2536_; lean_object* v_endExclusive_2537_; lean_object* v___x_2538_; uint8_t v_decide_2539_; 
v_str_2535_ = lean_ctor_get(v___x_2518_, 0);
v_startInclusive_2536_ = lean_ctor_get(v___x_2518_, 1);
v_endExclusive_2537_ = lean_ctor_get(v___x_2518_, 2);
v___x_2538_ = lean_nat_sub(v_endExclusive_2537_, v_startInclusive_2536_);
v_decide_2539_ = lean_nat_dec_eq(v_searcher_2531_, v___x_2538_);
lean_dec(v___x_2538_);
if (v_decide_2539_ == 0)
{
lean_object* v___x_2540_; uint32_t v___x_2541_; uint32_t v___x_2542_; uint8_t v___x_2543_; 
v___x_2540_ = lean_nat_add(v_startInclusive_2536_, v_searcher_2531_);
v___x_2541_ = lean_string_utf8_get_fast(v_str_2535_, v___x_2540_);
v___x_2542_ = 10;
v___x_2543_ = lean_uint32_dec_eq(v___x_2541_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
lean_dec(v_searcher_2531_);
v___x_2544_ = lean_string_utf8_next_fast(v_str_2535_, v___x_2540_);
lean_dec(v___x_2540_);
v___x_2545_ = lean_nat_sub(v___x_2544_, v_startInclusive_2536_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v___x_2545_);
v___x_2547_ = v___x_2533_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_currPos_2530_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; 
v___x_2548_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2547_, v_b_2521_);
return v___x_2548_;
}
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v_slice_2553_; lean_object* v_nextIt_2555_; 
v___x_2550_ = lean_string_utf8_next_fast(v_str_2535_, v___x_2540_);
v___x_2551_ = lean_nat_sub(v___x_2550_, v___x_2540_);
lean_dec(v___x_2540_);
v___x_2552_ = lean_nat_add(v_searcher_2531_, v___x_2551_);
lean_dec(v___x_2551_);
v_slice_2553_ = l_String_Slice_subslice_x21(v___x_2518_, v_currPos_2530_, v_searcher_2531_);
lean_inc(v___x_2552_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v___x_2552_);
lean_ctor_set(v___x_2533_, 0, v___x_2552_);
v_nextIt_2555_ = v___x_2533_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___x_2552_);
v_nextIt_2555_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v_startInclusive_2556_; lean_object* v_endExclusive_2557_; 
v_startInclusive_2556_ = lean_ctor_get(v_slice_2553_, 0);
lean_inc(v_startInclusive_2556_);
v_endExclusive_2557_ = lean_ctor_get(v_slice_2553_, 1);
lean_inc(v_endExclusive_2557_);
lean_dec_ref(v_slice_2553_);
v_it_2523_ = v_nextIt_2555_;
v_startInclusive_2524_ = v_startInclusive_2556_;
v_endExclusive_2525_ = v_endExclusive_2557_;
goto v___jp_2522_;
}
}
}
else
{
lean_object* v___x_2559_; 
lean_del_object(v___x_2533_);
lean_dec(v_searcher_2531_);
v___x_2559_ = lean_box(1);
lean_inc(v___x_2519_);
v_it_2523_ = v___x_2559_;
v_startInclusive_2524_ = v_currPos_2530_;
v_endExclusive_2525_ = v___x_2519_;
goto v___jp_2522_;
}
}
}
else
{
lean_dec(v___x_2519_);
lean_dec_ref(v___x_2517_);
return v_b_2521_;
}
v___jp_2522_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_inc_ref(v___x_2517_);
v___x_2526_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2517_);
lean_ctor_set(v___x_2526_, 1, v_startInclusive_2524_);
lean_ctor_set(v___x_2526_, 2, v_endExclusive_2525_);
v___x_2527_ = l_String_Slice_toString(v___x_2526_);
lean_dec_ref_known(v___x_2526_, 3);
v___x_2528_ = lean_array_push(v_b_2521_, v___x_2527_);
v___x_2529_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2517_, v___x_2518_, v___x_2519_, v_it_2523_, v___x_2528_);
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2561_, lean_object* v___x_2562_, lean_object* v___x_2563_, lean_object* v_a_2564_, lean_object* v_b_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2561_, v___x_2562_, v___x_2563_, v_a_2564_, v_b_2565_);
lean_dec_ref(v___x_2562_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; lean_object* v_infoState_2571_; uint8_t v_enabled_2572_; 
v___x_2570_ = lean_st_ref_get(v___y_2568_);
v_infoState_2571_ = lean_ctor_get(v___x_2570_, 8);
lean_inc_ref(v_infoState_2571_);
lean_dec(v___x_2570_);
v_enabled_2572_ = lean_ctor_get_uint8(v_infoState_2571_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2571_);
if (v_enabled_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_dec_ref(v_t_2567_);
v___x_2573_ = lean_box(0);
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
return v___x_2574_;
}
else
{
lean_object* v___x_2575_; lean_object* v_infoState_2576_; lean_object* v_env_2577_; lean_object* v_messages_2578_; lean_object* v_scopes_2579_; lean_object* v_usedQuotCtxts_2580_; lean_object* v_nextMacroScope_2581_; lean_object* v_maxRecDepth_2582_; lean_object* v_ngen_2583_; lean_object* v_auxDeclNGen_2584_; lean_object* v_traceState_2585_; lean_object* v_snapshotTasks_2586_; lean_object* v_prevLinterStates_2587_; lean_object* v_codeQualityEntryTasks_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2610_; 
v___x_2575_ = lean_st_ref_take(v___y_2568_);
v_infoState_2576_ = lean_ctor_get(v___x_2575_, 8);
v_env_2577_ = lean_ctor_get(v___x_2575_, 0);
v_messages_2578_ = lean_ctor_get(v___x_2575_, 1);
v_scopes_2579_ = lean_ctor_get(v___x_2575_, 2);
v_usedQuotCtxts_2580_ = lean_ctor_get(v___x_2575_, 3);
v_nextMacroScope_2581_ = lean_ctor_get(v___x_2575_, 4);
v_maxRecDepth_2582_ = lean_ctor_get(v___x_2575_, 5);
v_ngen_2583_ = lean_ctor_get(v___x_2575_, 6);
v_auxDeclNGen_2584_ = lean_ctor_get(v___x_2575_, 7);
v_traceState_2585_ = lean_ctor_get(v___x_2575_, 9);
v_snapshotTasks_2586_ = lean_ctor_get(v___x_2575_, 10);
v_prevLinterStates_2587_ = lean_ctor_get(v___x_2575_, 11);
v_codeQualityEntryTasks_2588_ = lean_ctor_get(v___x_2575_, 12);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2590_ = v___x_2575_;
v_isShared_2591_ = v_isSharedCheck_2610_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2588_);
lean_inc(v_prevLinterStates_2587_);
lean_inc(v_snapshotTasks_2586_);
lean_inc(v_traceState_2585_);
lean_inc(v_infoState_2576_);
lean_inc(v_auxDeclNGen_2584_);
lean_inc(v_ngen_2583_);
lean_inc(v_maxRecDepth_2582_);
lean_inc(v_nextMacroScope_2581_);
lean_inc(v_usedQuotCtxts_2580_);
lean_inc(v_scopes_2579_);
lean_inc(v_messages_2578_);
lean_inc(v_env_2577_);
lean_dec(v___x_2575_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2610_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
uint8_t v_enabled_2592_; lean_object* v_assignment_2593_; lean_object* v_lazyAssignment_2594_; lean_object* v_trees_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2609_; 
v_enabled_2592_ = lean_ctor_get_uint8(v_infoState_2576_, sizeof(void*)*3);
v_assignment_2593_ = lean_ctor_get(v_infoState_2576_, 0);
v_lazyAssignment_2594_ = lean_ctor_get(v_infoState_2576_, 1);
v_trees_2595_ = lean_ctor_get(v_infoState_2576_, 2);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_infoState_2576_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2597_ = v_infoState_2576_;
v_isShared_2598_ = v_isSharedCheck_2609_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_trees_2595_);
lean_inc(v_lazyAssignment_2594_);
lean_inc(v_assignment_2593_);
lean_dec(v_infoState_2576_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2609_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2599_ = l_Lean_PersistentArray_push___redArg(v_trees_2595_, v_t_2567_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 2, v___x_2599_);
v___x_2601_ = v___x_2597_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_assignment_2593_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_lazyAssignment_2594_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v___x_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*3, v_enabled_2592_);
v___x_2601_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2603_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 8, v___x_2601_);
v___x_2603_ = v___x_2590_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_env_2577_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_messages_2578_);
lean_ctor_set(v_reuseFailAlloc_2607_, 2, v_scopes_2579_);
lean_ctor_set(v_reuseFailAlloc_2607_, 3, v_usedQuotCtxts_2580_);
lean_ctor_set(v_reuseFailAlloc_2607_, 4, v_nextMacroScope_2581_);
lean_ctor_set(v_reuseFailAlloc_2607_, 5, v_maxRecDepth_2582_);
lean_ctor_set(v_reuseFailAlloc_2607_, 6, v_ngen_2583_);
lean_ctor_set(v_reuseFailAlloc_2607_, 7, v_auxDeclNGen_2584_);
lean_ctor_set(v_reuseFailAlloc_2607_, 8, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2607_, 9, v_traceState_2585_);
lean_ctor_set(v_reuseFailAlloc_2607_, 10, v_snapshotTasks_2586_);
lean_ctor_set(v_reuseFailAlloc_2607_, 11, v_prevLinterStates_2587_);
lean_ctor_set(v_reuseFailAlloc_2607_, 12, v_codeQualityEntryTasks_2588_);
v___x_2603_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2604_ = lean_st_ref_put(v___y_2568_, v___x_2603_);
v___x_2605_ = lean_box(0);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
return v___x_2606_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2611_, v___y_2612_);
lean_dec(v___y_2612_);
return v_res_2614_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_unsigned_to_nat(32u);
v___x_2616_ = lean_mk_empty_array_with_capacity(v___x_2615_);
v___x_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2618_ = ((size_t)5ULL);
v___x_2619_ = lean_unsigned_to_nat(0u);
v___x_2620_ = lean_unsigned_to_nat(32u);
v___x_2621_ = lean_mk_empty_array_with_capacity(v___x_2620_);
v___x_2622_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2623_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v___x_2621_);
lean_ctor_set(v___x_2623_, 2, v___x_2619_);
lean_ctor_set(v___x_2623_, 3, v___x_2619_);
lean_ctor_set_usize(v___x_2623_, 4, v___x_2618_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v___x_2628_; lean_object* v_infoState_2629_; uint8_t v_enabled_2630_; 
v___x_2628_ = lean_st_ref_get(v___y_2626_);
v_infoState_2629_ = lean_ctor_get(v___x_2628_, 8);
lean_inc_ref(v_infoState_2629_);
lean_dec(v___x_2628_);
v_enabled_2630_ = lean_ctor_get_uint8(v_infoState_2629_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2629_);
if (v_enabled_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec_ref(v_t_2624_);
v___x_2631_ = lean_box(0);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
return v___x_2632_;
}
else
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2634_, 0, v_t_2624_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2634_, v___y_2626_);
return v___x_2635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v___x_2641_, lean_object* v_edited_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v_fst_2645_; lean_object* v_snd_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2670_; 
v_fst_2645_ = lean_ctor_get(v_a_2644_, 0);
v_snd_2646_ = lean_ctor_get(v_a_2644_, 1);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_a_2644_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2648_ = v_a_2644_;
v_isShared_2649_ = v_isSharedCheck_2670_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_snd_2646_);
lean_inc(v_fst_2645_);
lean_dec(v_a_2644_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2670_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_nat_dec_lt(v_snd_2646_, v___x_2641_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2652_; 
if (v_isShared_2649_ == 0)
{
v___x_2652_ = v___x_2648_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_fst_2645_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_snd_2646_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2654_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2655_ = lean_array_get_borrowed(v___x_2654_, v_edited_2642_, v_snd_2646_);
v___x_2656_ = lean_string_dec_eq(v___x_2655_, v_a_2643_);
if (v___x_2656_ == 0)
{
uint8_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2657_ = 0;
v___x_2658_ = lean_box(v___x_2657_);
lean_inc(v___x_2655_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 1, v___x_2655_);
lean_ctor_set(v___x_2648_, 0, v___x_2658_);
v___x_2660_ = v___x_2648_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v___x_2655_);
v___x_2660_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2661_ = lean_array_push(v_fst_2645_, v___x_2660_);
v___x_2662_ = lean_unsigned_to_nat(1u);
v___x_2663_ = lean_nat_add(v_snd_2646_, v___x_2662_);
lean_dec(v_snd_2646_);
v___x_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2661_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
v_a_2644_ = v___x_2664_;
goto _start;
}
}
else
{
lean_object* v___x_2668_; 
if (v_isShared_2649_ == 0)
{
v___x_2668_ = v___x_2648_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_fst_2645_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_snd_2646_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v___x_2671_, lean_object* v_edited_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2671_, v_edited_2672_, v_a_2673_, v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec_ref(v_edited_2672_);
lean_dec(v___x_2671_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(lean_object* v___x_2676_, lean_object* v_original_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v_fst_2680_; lean_object* v_snd_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2705_; 
v_fst_2680_ = lean_ctor_get(v_a_2679_, 0);
v_snd_2681_ = lean_ctor_get(v_a_2679_, 1);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_a_2679_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2683_ = v_a_2679_;
v_isShared_2684_ = v_isSharedCheck_2705_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_snd_2681_);
lean_inc(v_fst_2680_);
lean_dec(v_a_2679_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2705_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
uint8_t v___x_2685_; 
v___x_2685_ = lean_nat_dec_lt(v_snd_2681_, v___x_2676_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2687_; 
if (v_isShared_2684_ == 0)
{
v___x_2687_ = v___x_2683_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_fst_2680_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_snd_2681_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2689_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___x_2690_ = lean_array_get_borrowed(v___x_2689_, v_original_2677_, v_snd_2681_);
v___x_2691_ = lean_string_dec_eq(v___x_2690_, v_a_2678_);
if (v___x_2691_ == 0)
{
uint8_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2692_ = 1;
v___x_2693_ = lean_box(v___x_2692_);
lean_inc(v___x_2690_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 1, v___x_2690_);
lean_ctor_set(v___x_2683_, 0, v___x_2693_);
v___x_2695_ = v___x_2683_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v___x_2690_);
v___x_2695_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2696_ = lean_array_push(v_fst_2680_, v___x_2695_);
v___x_2697_ = lean_unsigned_to_nat(1u);
v___x_2698_ = lean_nat_add(v_snd_2681_, v___x_2697_);
lean_dec(v_snd_2681_);
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2696_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v_a_2679_ = v___x_2699_;
goto _start;
}
}
else
{
lean_object* v___x_2703_; 
if (v_isShared_2684_ == 0)
{
v___x_2703_ = v___x_2683_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_fst_2680_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_snd_2681_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg___boxed(lean_object* v___x_2706_, lean_object* v_original_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2706_, v_original_2707_, v_a_2708_, v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec_ref(v_original_2707_);
lean_dec(v___x_2706_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v___x_2711_, lean_object* v_original_2712_, lean_object* v___x_2713_, lean_object* v_edited_2714_, lean_object* v_as_2715_, size_t v_sz_2716_, size_t v_i_2717_, lean_object* v_b_2718_){
_start:
{
uint8_t v___x_2719_; 
v___x_2719_ = lean_usize_dec_lt(v_i_2717_, v_sz_2716_);
if (v___x_2719_ == 0)
{
return v_b_2718_;
}
else
{
lean_object* v_snd_2720_; lean_object* v_fst_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2768_; 
v_snd_2720_ = lean_ctor_get(v_b_2718_, 1);
v_fst_2721_ = lean_ctor_get(v_b_2718_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_b_2718_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2723_ = v_b_2718_;
v_isShared_2724_ = v_isSharedCheck_2768_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_snd_2720_);
lean_inc(v_fst_2721_);
lean_dec(v_b_2718_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2768_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v_fst_2725_; lean_object* v_snd_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2767_; 
v_fst_2725_ = lean_ctor_get(v_snd_2720_, 0);
v_snd_2726_ = lean_ctor_get(v_snd_2720_, 1);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_snd_2720_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2728_ = v_snd_2720_;
v_isShared_2729_ = v_isSharedCheck_2767_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_snd_2726_);
lean_inc(v_fst_2725_);
lean_dec(v_snd_2720_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2767_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v_a_2730_; lean_object* v___x_2732_; 
v_a_2730_ = lean_array_uget_borrowed(v_as_2715_, v_i_2717_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 1, v_fst_2725_);
lean_ctor_set(v___x_2728_, 0, v_fst_2721_);
v___x_2732_ = v___x_2728_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_fst_2721_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_fst_2725_);
v___x_2732_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; lean_object* v_fst_2734_; lean_object* v_snd_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2765_; 
v___x_2733_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2711_, v_original_2712_, v_a_2730_, v___x_2732_);
v_fst_2734_ = lean_ctor_get(v___x_2733_, 0);
v_snd_2735_ = lean_ctor_get(v___x_2733_, 1);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2737_ = v___x_2733_;
v_isShared_2738_ = v_isSharedCheck_2765_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_snd_2735_);
lean_inc(v_fst_2734_);
lean_dec(v___x_2733_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2765_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 1, v_snd_2726_);
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_fst_2734_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_snd_2726_);
v___x_2740_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; lean_object* v_fst_2742_; lean_object* v_snd_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2763_; 
v___x_2741_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2713_, v_edited_2714_, v_a_2730_, v___x_2740_);
v_fst_2742_ = lean_ctor_get(v___x_2741_, 0);
v_snd_2743_ = lean_ctor_get(v___x_2741_, 1);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2745_ = v___x_2741_;
v_isShared_2746_ = v_isSharedCheck_2763_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_snd_2743_);
lean_inc(v_fst_2742_);
lean_dec(v___x_2741_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2763_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
uint8_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2747_ = 2;
v___x_2748_ = lean_box(v___x_2747_);
lean_inc(v_a_2730_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 1, v_a_2730_);
lean_ctor_set(v___x_2745_, 0, v___x_2748_);
v___x_2750_ = v___x_2745_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2748_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_a_2730_);
v___x_2750_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2751_ = lean_array_push(v_fst_2742_, v___x_2750_);
v___x_2752_ = lean_unsigned_to_nat(1u);
v___x_2753_ = lean_nat_add(v_snd_2735_, v___x_2752_);
lean_dec(v_snd_2735_);
v___x_2754_ = lean_nat_add(v_snd_2743_, v___x_2752_);
lean_dec(v_snd_2743_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 1, v___x_2754_);
lean_ctor_set(v___x_2723_, 0, v___x_2753_);
v___x_2756_ = v___x_2723_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
lean_object* v___x_2757_; size_t v___x_2758_; size_t v___x_2759_; 
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2751_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = ((size_t)1ULL);
v___x_2759_ = lean_usize_add(v_i_2717_, v___x_2758_);
v_i_2717_ = v___x_2759_;
v_b_2718_ = v___x_2757_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v___x_2769_, lean_object* v_original_2770_, lean_object* v___x_2771_, lean_object* v_edited_2772_, lean_object* v_as_2773_, lean_object* v_sz_2774_, lean_object* v_i_2775_, lean_object* v_b_2776_){
_start:
{
size_t v_sz_boxed_2777_; size_t v_i_boxed_2778_; lean_object* v_res_2779_; 
v_sz_boxed_2777_ = lean_unbox_usize(v_sz_2774_);
lean_dec(v_sz_2774_);
v_i_boxed_2778_ = lean_unbox_usize(v_i_2775_);
lean_dec(v_i_2775_);
v_res_2779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2769_, v_original_2770_, v___x_2771_, v_edited_2772_, v_as_2773_, v_sz_boxed_2777_, v_i_boxed_2778_, v_b_2776_);
lean_dec_ref(v_as_2773_);
lean_dec_ref(v_edited_2772_);
lean_dec(v___x_2771_);
lean_dec_ref(v_original_2770_);
lean_dec(v___x_2769_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v___x_2780_, lean_object* v_edited_2781_, lean_object* v___x_2782_, lean_object* v_original_2783_, lean_object* v_as_2784_, size_t v_sz_2785_, size_t v_i_2786_, lean_object* v_b_2787_){
_start:
{
uint8_t v___x_2788_; 
v___x_2788_ = lean_usize_dec_lt(v_i_2786_, v_sz_2785_);
if (v___x_2788_ == 0)
{
return v_b_2787_;
}
else
{
lean_object* v_snd_2789_; lean_object* v_fst_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2837_; 
v_snd_2789_ = lean_ctor_get(v_b_2787_, 1);
v_fst_2790_ = lean_ctor_get(v_b_2787_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_b_2787_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2792_ = v_b_2787_;
v_isShared_2793_ = v_isSharedCheck_2837_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_snd_2789_);
lean_inc(v_fst_2790_);
lean_dec(v_b_2787_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2837_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v_fst_2794_; lean_object* v_snd_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2836_; 
v_fst_2794_ = lean_ctor_get(v_snd_2789_, 0);
v_snd_2795_ = lean_ctor_get(v_snd_2789_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_snd_2789_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2797_ = v_snd_2789_;
v_isShared_2798_ = v_isSharedCheck_2836_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_snd_2795_);
lean_inc(v_fst_2794_);
lean_dec(v_snd_2789_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2836_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v_a_2799_; lean_object* v___x_2801_; 
v_a_2799_ = lean_array_uget_borrowed(v_as_2784_, v_i_2786_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 1, v_fst_2794_);
lean_ctor_set(v___x_2797_, 0, v_fst_2790_);
v___x_2801_ = v___x_2797_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_fst_2790_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_fst_2794_);
v___x_2801_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v_fst_2803_; lean_object* v_snd_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2834_; 
v___x_2802_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2782_, v_original_2783_, v_a_2799_, v___x_2801_);
v_fst_2803_ = lean_ctor_get(v___x_2802_, 0);
v_snd_2804_ = lean_ctor_get(v___x_2802_, 1);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2806_ = v___x_2802_;
v_isShared_2807_ = v_isSharedCheck_2834_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_snd_2804_);
lean_inc(v_fst_2803_);
lean_dec(v___x_2802_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2834_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 1, v_snd_2795_);
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_fst_2803_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_snd_2795_);
v___x_2809_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v_fst_2811_; lean_object* v_snd_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2832_; 
v___x_2810_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2780_, v_edited_2781_, v_a_2799_, v___x_2809_);
v_fst_2811_ = lean_ctor_get(v___x_2810_, 0);
v_snd_2812_ = lean_ctor_get(v___x_2810_, 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2814_ = v___x_2810_;
v_isShared_2815_ = v_isSharedCheck_2832_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_snd_2812_);
lean_inc(v_fst_2811_);
lean_dec(v___x_2810_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2832_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2816_ = 2;
v___x_2817_ = lean_box(v___x_2816_);
lean_inc(v_a_2799_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 1, v_a_2799_);
lean_ctor_set(v___x_2814_, 0, v___x_2817_);
v___x_2819_ = v___x_2814_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_a_2799_);
v___x_2819_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2820_ = lean_array_push(v_fst_2811_, v___x_2819_);
v___x_2821_ = lean_unsigned_to_nat(1u);
v___x_2822_ = lean_nat_add(v_snd_2804_, v___x_2821_);
lean_dec(v_snd_2804_);
v___x_2823_ = lean_nat_add(v_snd_2812_, v___x_2821_);
lean_dec(v_snd_2812_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2823_);
lean_ctor_set(v___x_2792_, 0, v___x_2822_);
v___x_2825_ = v___x_2792_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2822_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2826_; size_t v___x_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2820_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = ((size_t)1ULL);
v___x_2828_ = lean_usize_add(v_i_2786_, v___x_2827_);
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2782_, v_original_2783_, v___x_2780_, v_edited_2781_, v_as_2784_, v_sz_2785_, v___x_2828_, v___x_2826_);
return v___x_2829_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v___x_2838_, lean_object* v_edited_2839_, lean_object* v___x_2840_, lean_object* v_original_2841_, lean_object* v_as_2842_, lean_object* v_sz_2843_, lean_object* v_i_2844_, lean_object* v_b_2845_){
_start:
{
size_t v_sz_boxed_2846_; size_t v_i_boxed_2847_; lean_object* v_res_2848_; 
v_sz_boxed_2846_ = lean_unbox_usize(v_sz_2843_);
lean_dec(v_sz_2843_);
v_i_boxed_2847_ = lean_unbox_usize(v_i_2844_);
lean_dec(v_i_2844_);
v_res_2848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_2838_, v_edited_2839_, v___x_2840_, v_original_2841_, v_as_2842_, v_sz_boxed_2846_, v_i_boxed_2847_, v_b_2845_);
lean_dec_ref(v_as_2842_);
lean_dec_ref(v_original_2841_);
lean_dec(v___x_2840_);
lean_dec_ref(v_edited_2839_);
lean_dec(v___x_2838_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_2849_, lean_object* v_original_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_fst_2852_; lean_object* v_snd_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2872_; 
v_fst_2852_ = lean_ctor_get(v_a_2851_, 0);
v_snd_2853_ = lean_ctor_get(v_a_2851_, 1);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_a_2851_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2855_ = v_a_2851_;
v_isShared_2856_ = v_isSharedCheck_2872_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_snd_2853_);
lean_inc(v_fst_2852_);
lean_dec(v_a_2851_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2872_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
uint8_t v___x_2857_; 
v___x_2857_ = lean_nat_dec_lt(v_snd_2853_, v___x_2849_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2859_; 
if (v_isShared_2856_ == 0)
{
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_fst_2852_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_snd_2853_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
else
{
uint8_t v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2861_ = 1;
v___x_2862_ = lean_array_fget_borrowed(v_original_2850_, v_snd_2853_);
v___x_2863_ = lean_box(v___x_2861_);
lean_inc(v___x_2862_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 1, v___x_2862_);
lean_ctor_set(v___x_2855_, 0, v___x_2863_);
v___x_2865_ = v___x_2855_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2863_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v___x_2862_);
v___x_2865_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2866_ = lean_array_push(v_fst_2852_, v___x_2865_);
v___x_2867_ = lean_unsigned_to_nat(1u);
v___x_2868_ = lean_nat_add(v_snd_2853_, v___x_2867_);
lean_dec(v_snd_2853_);
v___x_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2866_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v_a_2851_ = v___x_2869_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_2873_, lean_object* v_original_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_2873_, v_original_2874_, v_a_2875_);
lean_dec_ref(v_original_2874_);
lean_dec(v___x_2873_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_2877_, size_t v_i_2878_, lean_object* v_bs_2879_){
_start:
{
uint8_t v___x_2880_; 
v___x_2880_ = lean_usize_dec_lt(v_i_2878_, v_sz_2877_);
if (v___x_2880_ == 0)
{
return v_bs_2879_;
}
else
{
lean_object* v_v_2881_; lean_object* v___x_2882_; lean_object* v_bs_x27_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; size_t v___x_2887_; size_t v___x_2888_; lean_object* v___x_2889_; 
v_v_2881_ = lean_array_uget(v_bs_2879_, v_i_2878_);
v___x_2882_ = lean_unsigned_to_nat(0u);
v_bs_x27_2883_ = lean_array_uset(v_bs_2879_, v_i_2878_, v___x_2882_);
v___x_2884_ = 0;
v___x_2885_ = lean_box(v___x_2884_);
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
lean_ctor_set(v___x_2886_, 1, v_v_2881_);
v___x_2887_ = ((size_t)1ULL);
v___x_2888_ = lean_usize_add(v_i_2878_, v___x_2887_);
v___x_2889_ = lean_array_uset(v_bs_x27_2883_, v_i_2878_, v___x_2886_);
v_i_2878_ = v___x_2888_;
v_bs_2879_ = v___x_2889_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_2891_, lean_object* v_i_2892_, lean_object* v_bs_2893_){
_start:
{
size_t v_sz_boxed_2894_; size_t v_i_boxed_2895_; lean_object* v_res_2896_; 
v_sz_boxed_2894_ = lean_unbox_usize(v_sz_2891_);
lean_dec(v_sz_2891_);
v_i_boxed_2895_ = lean_unbox_usize(v_i_2892_);
lean_dec(v_i_2892_);
v_res_2896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_2894_, v_i_boxed_2895_, v_bs_2893_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_2897_, lean_object* v_edited_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_fst_2900_; lean_object* v_snd_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2920_; 
v_fst_2900_ = lean_ctor_get(v_a_2899_, 0);
v_snd_2901_ = lean_ctor_get(v_a_2899_, 1);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_a_2899_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2903_ = v_a_2899_;
v_isShared_2904_ = v_isSharedCheck_2920_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_snd_2901_);
lean_inc(v_fst_2900_);
lean_dec(v_a_2899_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2920_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
uint8_t v___x_2905_; 
v___x_2905_ = lean_nat_dec_lt(v_snd_2901_, v___x_2897_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2907_; 
if (v_isShared_2904_ == 0)
{
v___x_2907_ = v___x_2903_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_fst_2900_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_snd_2901_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
else
{
uint8_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2909_ = 0;
v___x_2910_ = lean_array_fget_borrowed(v_edited_2898_, v_snd_2901_);
v___x_2911_ = lean_box(v___x_2909_);
lean_inc(v___x_2910_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 1, v___x_2910_);
lean_ctor_set(v___x_2903_, 0, v___x_2911_);
v___x_2913_ = v___x_2903_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v___x_2910_);
v___x_2913_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2914_ = lean_array_push(v_fst_2900_, v___x_2913_);
v___x_2915_ = lean_unsigned_to_nat(1u);
v___x_2916_ = lean_nat_add(v_snd_2901_, v___x_2915_);
lean_dec(v_snd_2901_);
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2914_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
v_a_2899_ = v___x_2917_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_2921_, lean_object* v_edited_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_2921_, v_edited_2922_, v_a_2923_);
lean_dec_ref(v_edited_2922_);
lean_dec(v___x_2921_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(lean_object* v_x_2925_, lean_object* v_x_2926_){
_start:
{
if (lean_obj_tag(v_x_2926_) == 0)
{
lean_inc(v_x_2925_);
return v_x_2925_;
}
else
{
lean_object* v_key_2927_; lean_object* v_value_2928_; lean_object* v_tail_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v_key_2927_ = lean_ctor_get(v_x_2926_, 0);
v_value_2928_ = lean_ctor_get(v_x_2926_, 1);
v_tail_2929_ = lean_ctor_get(v_x_2926_, 2);
v___x_2930_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2925_, v_tail_2929_);
lean_inc(v_value_2928_);
lean_inc(v_key_2927_);
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v_key_2927_);
lean_ctor_set(v___x_2931_, 1, v_value_2928_);
v___x_2932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
lean_ctor_set(v___x_2932_, 1, v___x_2930_);
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17___boxed(lean_object* v_x_2933_, lean_object* v_x_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2933_, v_x_2934_);
lean_dec(v_x_2934_);
lean_dec(v_x_2933_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(lean_object* v_as_2936_, size_t v_i_2937_, size_t v_stop_2938_, lean_object* v_b_2939_){
_start:
{
uint8_t v___x_2940_; 
v___x_2940_ = lean_usize_dec_eq(v_i_2937_, v_stop_2938_);
if (v___x_2940_ == 0)
{
size_t v___x_2941_; size_t v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2941_ = ((size_t)1ULL);
v___x_2942_ = lean_usize_sub(v_i_2937_, v___x_2941_);
v___x_2943_ = lean_array_uget_borrowed(v_as_2936_, v___x_2942_);
v___x_2944_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_b_2939_, v___x_2943_);
lean_dec(v_b_2939_);
v_i_2937_ = v___x_2942_;
v_b_2939_ = v___x_2944_;
goto _start;
}
else
{
return v_b_2939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18___boxed(lean_object* v_as_2946_, lean_object* v_i_2947_, lean_object* v_stop_2948_, lean_object* v_b_2949_){
_start:
{
size_t v_i_boxed_2950_; size_t v_stop_boxed_2951_; lean_object* v_res_2952_; 
v_i_boxed_2950_ = lean_unbox_usize(v_i_2947_);
lean_dec(v_i_2947_);
v_stop_boxed_2951_ = lean_unbox_usize(v_stop_2948_);
lean_dec(v_stop_2948_);
v_res_2952_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_as_2946_, v_i_boxed_2950_, v_stop_boxed_2951_, v_b_2949_);
lean_dec_ref(v_as_2946_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(lean_object* v_left_2953_, lean_object* v_right_2954_, lean_object* v_pref_2955_){
_start:
{
lean_object* v_start_2956_; lean_object* v_stop_2957_; lean_object* v_start_2958_; lean_object* v_stop_2959_; lean_object* v_i_2960_; uint8_t v___y_2962_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v_start_2956_ = lean_ctor_get(v_left_2953_, 1);
v_stop_2957_ = lean_ctor_get(v_left_2953_, 2);
v_start_2958_ = lean_ctor_get(v_right_2954_, 1);
v_stop_2959_ = lean_ctor_get(v_right_2954_, 2);
v_i_2960_ = lean_array_get_size(v_pref_2955_);
v___x_2976_ = lean_nat_sub(v_stop_2957_, v_start_2956_);
v___x_2977_ = lean_nat_dec_lt(v_i_2960_, v___x_2976_);
lean_dec(v___x_2976_);
if (v___x_2977_ == 0)
{
v___y_2962_ = v___x_2977_;
goto v___jp_2961_;
}
else
{
lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2978_ = lean_nat_sub(v_stop_2959_, v_start_2958_);
v___x_2979_ = lean_nat_dec_lt(v_i_2960_, v___x_2978_);
lean_dec(v___x_2978_);
v___y_2962_ = v___x_2979_;
goto v___jp_2961_;
}
v___jp_2961_:
{
if (v___y_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2963_ = l_Subarray_drop___redArg(v_left_2953_, v_i_2960_);
v___x_2964_ = l_Subarray_drop___redArg(v_right_2954_, v_i_2960_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v_pref_2955_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
return v___x_2966_;
}
else
{
lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2967_ = l_Subarray_get___redArg(v_left_2953_, v_i_2960_);
v___x_2968_ = l_Subarray_get___redArg(v_right_2954_, v_i_2960_);
v___x_2969_ = lean_string_dec_eq(v___x_2967_, v___x_2968_);
lean_dec(v___x_2968_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_dec(v___x_2967_);
v___x_2970_ = l_Subarray_drop___redArg(v_left_2953_, v_i_2960_);
v___x_2971_ = l_Subarray_drop___redArg(v_right_2954_, v_i_2960_);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2970_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v_pref_2955_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
return v___x_2973_;
}
else
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_array_push(v_pref_2955_, v___x_2967_);
v_pref_2955_ = v___x_2974_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(lean_object* v_left_2982_, lean_object* v_right_2983_){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_2985_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(v_left_2982_, v_right_2983_, v___x_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(lean_object* v_a_2986_, lean_object* v_b_2987_, lean_object* v_x_2988_){
_start:
{
if (lean_obj_tag(v_x_2988_) == 0)
{
lean_dec(v_b_2987_);
lean_dec_ref(v_a_2986_);
return v_x_2988_;
}
else
{
lean_object* v_key_2989_; lean_object* v_value_2990_; lean_object* v_tail_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3003_; 
v_key_2989_ = lean_ctor_get(v_x_2988_, 0);
v_value_2990_ = lean_ctor_get(v_x_2988_, 1);
v_tail_2991_ = lean_ctor_get(v_x_2988_, 2);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_x_2988_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2993_ = v_x_2988_;
v_isShared_2994_ = v_isSharedCheck_3003_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_tail_2991_);
lean_inc(v_value_2990_);
lean_inc(v_key_2989_);
lean_dec(v_x_2988_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3003_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
uint8_t v___x_2995_; 
v___x_2995_ = lean_string_dec_eq(v_key_2989_, v_a_2986_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2996_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_2986_, v_b_2987_, v_tail_2991_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 2, v___x_2996_);
v___x_2998_ = v___x_2993_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_key_2989_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_value_2990_);
lean_ctor_set(v_reuseFailAlloc_2999_, 2, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
else
{
lean_object* v___x_3001_; 
lean_dec(v_value_2990_);
lean_dec(v_key_2989_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v_b_2987_);
lean_ctor_set(v___x_2993_, 0, v_a_2986_);
v___x_3001_ = v___x_2993_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2986_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_b_2987_);
lean_ctor_set(v_reuseFailAlloc_3002_, 2, v_tail_2991_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(lean_object* v_x_3004_, lean_object* v_x_3005_){
_start:
{
if (lean_obj_tag(v_x_3005_) == 0)
{
return v_x_3004_;
}
else
{
lean_object* v_key_3006_; lean_object* v_value_3007_; lean_object* v_tail_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3031_; 
v_key_3006_ = lean_ctor_get(v_x_3005_, 0);
v_value_3007_ = lean_ctor_get(v_x_3005_, 1);
v_tail_3008_ = lean_ctor_get(v_x_3005_, 2);
v_isSharedCheck_3031_ = !lean_is_exclusive(v_x_3005_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3010_ = v_x_3005_;
v_isShared_3011_ = v_isSharedCheck_3031_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_tail_3008_);
lean_inc(v_value_3007_);
lean_inc(v_key_3006_);
lean_dec(v_x_3005_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3031_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; uint64_t v___x_3013_; uint64_t v___x_3014_; uint64_t v___x_3015_; uint64_t v_fold_3016_; uint64_t v___x_3017_; uint64_t v___x_3018_; uint64_t v___x_3019_; size_t v___x_3020_; size_t v___x_3021_; size_t v___x_3022_; size_t v___x_3023_; size_t v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3027_; 
v___x_3012_ = lean_array_get_size(v_x_3004_);
v___x_3013_ = lean_string_hash(v_key_3006_);
v___x_3014_ = 32ULL;
v___x_3015_ = lean_uint64_shift_right(v___x_3013_, v___x_3014_);
v_fold_3016_ = lean_uint64_xor(v___x_3013_, v___x_3015_);
v___x_3017_ = 16ULL;
v___x_3018_ = lean_uint64_shift_right(v_fold_3016_, v___x_3017_);
v___x_3019_ = lean_uint64_xor(v_fold_3016_, v___x_3018_);
v___x_3020_ = lean_uint64_to_usize(v___x_3019_);
v___x_3021_ = lean_usize_of_nat(v___x_3012_);
v___x_3022_ = ((size_t)1ULL);
v___x_3023_ = lean_usize_sub(v___x_3021_, v___x_3022_);
v___x_3024_ = lean_usize_land(v___x_3020_, v___x_3023_);
v___x_3025_ = lean_array_uget_borrowed(v_x_3004_, v___x_3024_);
lean_inc(v___x_3025_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 2, v___x_3025_);
v___x_3027_ = v___x_3010_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_key_3006_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_value_3007_);
lean_ctor_set(v_reuseFailAlloc_3030_, 2, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3028_; 
v___x_3028_ = lean_array_uset(v_x_3004_, v___x_3024_, v___x_3027_);
v_x_3004_ = v___x_3028_;
v_x_3005_ = v_tail_3008_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(lean_object* v_i_3032_, lean_object* v_source_3033_, lean_object* v_target_3034_){
_start:
{
lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = lean_array_get_size(v_source_3033_);
v___x_3036_ = lean_nat_dec_lt(v_i_3032_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_dec_ref(v_source_3033_);
lean_dec(v_i_3032_);
return v_target_3034_;
}
else
{
lean_object* v_es_3037_; lean_object* v___x_3038_; lean_object* v_source_3039_; lean_object* v_target_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_es_3037_ = lean_array_fget(v_source_3033_, v_i_3032_);
v___x_3038_ = lean_box(0);
v_source_3039_ = lean_array_fset(v_source_3033_, v_i_3032_, v___x_3038_);
v_target_3040_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_target_3034_, v_es_3037_);
v___x_3041_ = lean_unsigned_to_nat(1u);
v___x_3042_ = lean_nat_add(v_i_3032_, v___x_3041_);
lean_dec(v_i_3032_);
v_i_3032_ = v___x_3042_;
v_source_3033_ = v_source_3039_;
v_target_3034_ = v_target_3040_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(lean_object* v_data_3044_){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v_nbuckets_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3045_ = lean_array_get_size(v_data_3044_);
v___x_3046_ = lean_unsigned_to_nat(2u);
v_nbuckets_3047_ = lean_nat_mul(v___x_3045_, v___x_3046_);
v___x_3048_ = lean_unsigned_to_nat(0u);
v___x_3049_ = lean_box(0);
v___x_3050_ = lean_mk_array(v_nbuckets_3047_, v___x_3049_);
v___x_3051_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v___x_3048_, v_data_3044_, v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(lean_object* v_a_3052_, lean_object* v_x_3053_){
_start:
{
if (lean_obj_tag(v_x_3053_) == 0)
{
uint8_t v___x_3054_; 
v___x_3054_ = 0;
return v___x_3054_;
}
else
{
lean_object* v_key_3055_; lean_object* v_tail_3056_; uint8_t v___x_3057_; 
v_key_3055_ = lean_ctor_get(v_x_3053_, 0);
v_tail_3056_ = lean_ctor_get(v_x_3053_, 2);
v___x_3057_ = lean_string_dec_eq(v_key_3055_, v_a_3052_);
if (v___x_3057_ == 0)
{
v_x_3053_ = v_tail_3056_;
goto _start;
}
else
{
return v___x_3057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg___boxed(lean_object* v_a_3059_, lean_object* v_x_3060_){
_start:
{
uint8_t v_res_3061_; lean_object* v_r_3062_; 
v_res_3061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_3059_, v_x_3060_);
lean_dec(v_x_3060_);
lean_dec_ref(v_a_3059_);
v_r_3062_ = lean_box(v_res_3061_);
return v_r_3062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(lean_object* v_m_3063_, lean_object* v_a_3064_, lean_object* v_b_3065_){
_start:
{
lean_object* v_size_3066_; lean_object* v_buckets_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3110_; 
v_size_3066_ = lean_ctor_get(v_m_3063_, 0);
v_buckets_3067_ = lean_ctor_get(v_m_3063_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_m_3063_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3069_ = v_m_3063_;
v_isShared_3070_ = v_isSharedCheck_3110_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_buckets_3067_);
lean_inc(v_size_3066_);
lean_dec(v_m_3063_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3110_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; uint64_t v___x_3072_; uint64_t v___x_3073_; uint64_t v___x_3074_; uint64_t v_fold_3075_; uint64_t v___x_3076_; uint64_t v___x_3077_; uint64_t v___x_3078_; size_t v___x_3079_; size_t v___x_3080_; size_t v___x_3081_; size_t v___x_3082_; size_t v___x_3083_; lean_object* v_bkt_3084_; uint8_t v___x_3085_; 
v___x_3071_ = lean_array_get_size(v_buckets_3067_);
v___x_3072_ = lean_string_hash(v_a_3064_);
v___x_3073_ = 32ULL;
v___x_3074_ = lean_uint64_shift_right(v___x_3072_, v___x_3073_);
v_fold_3075_ = lean_uint64_xor(v___x_3072_, v___x_3074_);
v___x_3076_ = 16ULL;
v___x_3077_ = lean_uint64_shift_right(v_fold_3075_, v___x_3076_);
v___x_3078_ = lean_uint64_xor(v_fold_3075_, v___x_3077_);
v___x_3079_ = lean_uint64_to_usize(v___x_3078_);
v___x_3080_ = lean_usize_of_nat(v___x_3071_);
v___x_3081_ = ((size_t)1ULL);
v___x_3082_ = lean_usize_sub(v___x_3080_, v___x_3081_);
v___x_3083_ = lean_usize_land(v___x_3079_, v___x_3082_);
v_bkt_3084_ = lean_array_uget_borrowed(v_buckets_3067_, v___x_3083_);
v___x_3085_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_3064_, v_bkt_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v_size_x27_3087_; lean_object* v___x_3088_; lean_object* v_buckets_x27_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3086_ = lean_unsigned_to_nat(1u);
v_size_x27_3087_ = lean_nat_add(v_size_3066_, v___x_3086_);
lean_dec(v_size_3066_);
lean_inc(v_bkt_3084_);
v___x_3088_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3088_, 0, v_a_3064_);
lean_ctor_set(v___x_3088_, 1, v_b_3065_);
lean_ctor_set(v___x_3088_, 2, v_bkt_3084_);
v_buckets_x27_3089_ = lean_array_uset(v_buckets_3067_, v___x_3083_, v___x_3088_);
v___x_3090_ = lean_unsigned_to_nat(4u);
v___x_3091_ = lean_nat_mul(v_size_x27_3087_, v___x_3090_);
v___x_3092_ = lean_unsigned_to_nat(3u);
v___x_3093_ = lean_nat_div(v___x_3091_, v___x_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_array_get_size(v_buckets_x27_3089_);
v___x_3095_ = lean_nat_dec_le(v___x_3093_, v___x_3094_);
lean_dec(v___x_3093_);
if (v___x_3095_ == 0)
{
lean_object* v_val_3096_; lean_object* v___x_3098_; 
v_val_3096_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_buckets_x27_3089_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v_val_3096_);
lean_ctor_set(v___x_3069_, 0, v_size_x27_3087_);
v___x_3098_ = v___x_3069_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_size_x27_3087_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_val_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
else
{
lean_object* v___x_3101_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v_buckets_x27_3089_);
lean_ctor_set(v___x_3069_, 0, v_size_x27_3087_);
v___x_3101_ = v___x_3069_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_size_x27_3087_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_buckets_x27_3089_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
else
{
lean_object* v___x_3103_; lean_object* v_buckets_x27_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
lean_inc(v_bkt_3084_);
v___x_3103_ = lean_box(0);
v_buckets_x27_3104_ = lean_array_uset(v_buckets_3067_, v___x_3083_, v___x_3103_);
v___x_3105_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_3064_, v_b_3065_, v_bkt_3084_);
v___x_3106_ = lean_array_uset(v_buckets_x27_3104_, v___x_3083_, v___x_3105_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v___x_3106_);
v___x_3108_ = v___x_3069_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_size_3066_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(lean_object* v_a_3111_, lean_object* v_x_3112_){
_start:
{
if (lean_obj_tag(v_x_3112_) == 0)
{
lean_object* v___x_3113_; 
v___x_3113_ = lean_box(0);
return v___x_3113_;
}
else
{
lean_object* v_key_3114_; lean_object* v_value_3115_; lean_object* v_tail_3116_; uint8_t v___x_3117_; 
v_key_3114_ = lean_ctor_get(v_x_3112_, 0);
v_value_3115_ = lean_ctor_get(v_x_3112_, 1);
v_tail_3116_ = lean_ctor_get(v_x_3112_, 2);
v___x_3117_ = lean_string_dec_eq(v_key_3114_, v_a_3111_);
if (v___x_3117_ == 0)
{
v_x_3112_ = v_tail_3116_;
goto _start;
}
else
{
lean_object* v___x_3119_; 
lean_inc(v_value_3115_);
v___x_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3119_, 0, v_value_3115_);
return v___x_3119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg___boxed(lean_object* v_a_3120_, lean_object* v_x_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3120_, v_x_3121_);
lean_dec(v_x_3121_);
lean_dec_ref(v_a_3120_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(lean_object* v_m_3123_, lean_object* v_a_3124_){
_start:
{
lean_object* v_buckets_3125_; lean_object* v___x_3126_; uint64_t v___x_3127_; uint64_t v___x_3128_; uint64_t v___x_3129_; uint64_t v_fold_3130_; uint64_t v___x_3131_; uint64_t v___x_3132_; uint64_t v___x_3133_; size_t v___x_3134_; size_t v___x_3135_; size_t v___x_3136_; size_t v___x_3137_; size_t v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_buckets_3125_ = lean_ctor_get(v_m_3123_, 1);
v___x_3126_ = lean_array_get_size(v_buckets_3125_);
v___x_3127_ = lean_string_hash(v_a_3124_);
v___x_3128_ = 32ULL;
v___x_3129_ = lean_uint64_shift_right(v___x_3127_, v___x_3128_);
v_fold_3130_ = lean_uint64_xor(v___x_3127_, v___x_3129_);
v___x_3131_ = 16ULL;
v___x_3132_ = lean_uint64_shift_right(v_fold_3130_, v___x_3131_);
v___x_3133_ = lean_uint64_xor(v_fold_3130_, v___x_3132_);
v___x_3134_ = lean_uint64_to_usize(v___x_3133_);
v___x_3135_ = lean_usize_of_nat(v___x_3126_);
v___x_3136_ = ((size_t)1ULL);
v___x_3137_ = lean_usize_sub(v___x_3135_, v___x_3136_);
v___x_3138_ = lean_usize_land(v___x_3134_, v___x_3137_);
v___x_3139_ = lean_array_uget_borrowed(v_buckets_3125_, v___x_3138_);
v___x_3140_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3124_, v___x_3139_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg___boxed(lean_object* v_m_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_3141_, v_a_3142_);
lean_dec_ref(v_a_3142_);
lean_dec_ref(v_m_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(lean_object* v_histogram_3144_, lean_object* v_index_3145_, lean_object* v_val_3146_){
_start:
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3144_, v_val_3146_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3148_ = lean_unsigned_to_nat(1u);
v___x_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3149_, 0, v_index_3145_);
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = lean_box(0);
v___x_3152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3148_);
lean_ctor_set(v___x_3152_, 1, v___x_3149_);
lean_ctor_set(v___x_3152_, 2, v___x_3150_);
lean_ctor_set(v___x_3152_, 3, v___x_3151_);
v___x_3153_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3144_, v_val_3146_, v___x_3152_);
return v___x_3153_;
}
else
{
lean_object* v_val_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3175_; 
v_val_3154_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3156_ = v___x_3147_;
v_isShared_3157_ = v_isSharedCheck_3175_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_val_3154_);
lean_dec(v___x_3147_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3175_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v_leftCount_3158_; lean_object* v_rightCount_3159_; lean_object* v_rightIndex_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3173_; 
v_leftCount_3158_ = lean_ctor_get(v_val_3154_, 0);
v_rightCount_3159_ = lean_ctor_get(v_val_3154_, 2);
v_rightIndex_3160_ = lean_ctor_get(v_val_3154_, 3);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_val_3154_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v_val_3154_, 1);
lean_dec(v_unused_3174_);
v___x_3162_ = v_val_3154_;
v_isShared_3163_ = v_isSharedCheck_3173_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_rightIndex_3160_);
lean_inc(v_rightCount_3159_);
lean_inc(v_leftCount_3158_);
lean_dec(v_val_3154_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3173_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3164_ = lean_unsigned_to_nat(1u);
v___x_3165_ = lean_nat_add(v_leftCount_3158_, v___x_3164_);
lean_dec(v_leftCount_3158_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 0, v_index_3145_);
v___x_3167_ = v___x_3156_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_index_3145_);
v___x_3167_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3169_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3167_);
lean_ctor_set(v___x_3162_, 0, v___x_3165_);
v___x_3169_ = v___x_3162_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v_rightCount_3159_);
lean_ctor_set(v_reuseFailAlloc_3171_, 3, v_rightIndex_3160_);
v___x_3169_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3144_, v_val_3146_, v___x_3169_);
return v___x_3170_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(lean_object* v_upperBound_3176_, lean_object* v_fst_3177_, lean_object* v___x_3178_, lean_object* v_fst_3179_, lean_object* v_a_3180_, lean_object* v_b_3181_){
_start:
{
uint8_t v___x_3182_; 
v___x_3182_ = lean_nat_dec_lt(v_a_3180_, v_upperBound_3176_);
if (v___x_3182_ == 0)
{
lean_dec(v_a_3180_);
return v_b_3181_;
}
else
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3183_ = l_Subarray_get___redArg(v_fst_3179_, v_a_3180_);
lean_inc(v_a_3180_);
v___x_3184_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_b_3181_, v_a_3180_, v___x_3183_);
v___x_3185_ = lean_unsigned_to_nat(1u);
v___x_3186_ = lean_nat_add(v_a_3180_, v___x_3185_);
lean_dec(v_a_3180_);
v_a_3180_ = v___x_3186_;
v_b_3181_ = v___x_3184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_upperBound_3188_, lean_object* v_fst_3189_, lean_object* v___x_3190_, lean_object* v_fst_3191_, lean_object* v_a_3192_, lean_object* v_b_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3188_, v_fst_3189_, v___x_3190_, v_fst_3191_, v_a_3192_, v_b_3193_);
lean_dec_ref(v_fst_3191_);
lean_dec(v___x_3190_);
lean_dec_ref(v_fst_3189_);
lean_dec(v_upperBound_3188_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(lean_object* v_as_x27_3195_, lean_object* v_b_3196_){
_start:
{
if (lean_obj_tag(v_as_x27_3195_) == 0)
{
return v_b_3196_;
}
else
{
lean_object* v_head_3197_; lean_object* v_snd_3198_; lean_object* v_leftIndex_3199_; 
v_head_3197_ = lean_ctor_get(v_as_x27_3195_, 0);
v_snd_3198_ = lean_ctor_get(v_head_3197_, 1);
v_leftIndex_3199_ = lean_ctor_get(v_snd_3198_, 1);
if (lean_obj_tag(v_leftIndex_3199_) == 1)
{
lean_object* v_rightIndex_3200_; 
v_rightIndex_3200_ = lean_ctor_get(v_snd_3198_, 3);
if (lean_obj_tag(v_rightIndex_3200_) == 1)
{
if (lean_obj_tag(v_b_3196_) == 0)
{
lean_object* v_tail_3201_; lean_object* v_fst_3202_; lean_object* v_leftCount_3203_; lean_object* v_rightCount_3204_; lean_object* v_val_3205_; lean_object* v_val_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_tail_3201_ = lean_ctor_get(v_as_x27_3195_, 1);
v_fst_3202_ = lean_ctor_get(v_head_3197_, 0);
v_leftCount_3203_ = lean_ctor_get(v_snd_3198_, 0);
v_rightCount_3204_ = lean_ctor_get(v_snd_3198_, 2);
v_val_3205_ = lean_ctor_get(v_leftIndex_3199_, 0);
v_val_3206_ = lean_ctor_get(v_rightIndex_3200_, 0);
v___x_3207_ = lean_nat_add(v_leftCount_3203_, v_rightCount_3204_);
lean_inc(v_val_3206_);
lean_inc(v_val_3205_);
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v_val_3205_);
lean_ctor_set(v___x_3208_, 1, v_val_3206_);
lean_inc(v_fst_3202_);
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v_fst_3202_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3207_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
v_as_x27_3195_ = v_tail_3201_;
v_b_3196_ = v___x_3211_;
goto _start;
}
else
{
lean_object* v_val_3213_; lean_object* v_tail_3214_; lean_object* v_fst_3215_; lean_object* v_leftCount_3216_; lean_object* v_rightCount_3217_; lean_object* v_val_3218_; lean_object* v_val_3219_; lean_object* v_fst_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3241_; 
v_val_3213_ = lean_ctor_get(v_b_3196_, 0);
lean_inc(v_val_3213_);
v_tail_3214_ = lean_ctor_get(v_as_x27_3195_, 1);
v_fst_3215_ = lean_ctor_get(v_head_3197_, 0);
v_leftCount_3216_ = lean_ctor_get(v_snd_3198_, 0);
v_rightCount_3217_ = lean_ctor_get(v_snd_3198_, 2);
v_val_3218_ = lean_ctor_get(v_leftIndex_3199_, 0);
v_val_3219_ = lean_ctor_get(v_rightIndex_3200_, 0);
v_fst_3220_ = lean_ctor_get(v_val_3213_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_val_3213_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; 
v_unused_3242_ = lean_ctor_get(v_val_3213_, 1);
lean_dec(v_unused_3242_);
v___x_3222_ = v_val_3213_;
v_isShared_3223_ = v_isSharedCheck_3241_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_fst_3220_);
lean_dec(v_val_3213_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3241_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = lean_nat_add(v_leftCount_3216_, v_rightCount_3217_);
v___x_3225_ = lean_nat_dec_lt(v___x_3224_, v_fst_3220_);
lean_dec(v_fst_3220_);
if (v___x_3225_ == 0)
{
lean_dec(v___x_3224_);
lean_del_object(v___x_3222_);
v_as_x27_3195_ = v_tail_3214_;
goto _start;
}
else
{
lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3239_; 
v_isSharedCheck_3239_ = !lean_is_exclusive(v_b_3196_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v_b_3196_, 0);
lean_dec(v_unused_3240_);
v___x_3228_ = v_b_3196_;
v_isShared_3229_ = v_isSharedCheck_3239_;
goto v_resetjp_3227_;
}
else
{
lean_dec(v_b_3196_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3239_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
lean_inc(v_val_3219_);
lean_inc(v_val_3218_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 1, v_val_3219_);
lean_ctor_set(v___x_3222_, 0, v_val_3218_);
v___x_3231_ = v___x_3222_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_val_3218_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_val_3219_);
v___x_3231_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3235_; 
lean_inc(v_fst_3215_);
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v_fst_3215_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3224_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3233_);
v___x_3235_ = v___x_3228_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3233_);
v___x_3235_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
v_as_x27_3195_ = v_tail_3214_;
v_b_3196_ = v___x_3235_;
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
lean_object* v_tail_3243_; 
v_tail_3243_ = lean_ctor_get(v_as_x27_3195_, 1);
v_as_x27_3195_ = v_tail_3243_;
goto _start;
}
}
else
{
lean_object* v_tail_3245_; 
v_tail_3245_ = lean_ctor_get(v_as_x27_3195_, 1);
v_as_x27_3195_ = v_tail_3245_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg___boxed(lean_object* v_as_x27_3247_, lean_object* v_b_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3247_, v_b_3248_);
lean_dec(v_as_x27_3247_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(lean_object* v_histogram_3250_, lean_object* v_index_3251_, lean_object* v_val_3252_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3250_, v_val_3252_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3254_ = lean_unsigned_to_nat(0u);
v___x_3255_ = lean_box(0);
v___x_3256_ = lean_unsigned_to_nat(1u);
v___x_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_index_3251_);
v___x_3258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3254_);
lean_ctor_set(v___x_3258_, 1, v___x_3255_);
lean_ctor_set(v___x_3258_, 2, v___x_3256_);
lean_ctor_set(v___x_3258_, 3, v___x_3257_);
v___x_3259_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3250_, v_val_3252_, v___x_3258_);
return v___x_3259_;
}
else
{
lean_object* v_val_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3281_; 
v_val_3260_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3262_ = v___x_3253_;
v_isShared_3263_ = v_isSharedCheck_3281_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_val_3260_);
lean_dec(v___x_3253_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3281_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v_leftCount_3264_; lean_object* v_leftIndex_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3278_; 
v_leftCount_3264_ = lean_ctor_get(v_val_3260_, 0);
v_leftIndex_3265_ = lean_ctor_get(v_val_3260_, 1);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_val_3260_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; lean_object* v_unused_3280_; 
v_unused_3279_ = lean_ctor_get(v_val_3260_, 3);
lean_dec(v_unused_3279_);
v_unused_3280_ = lean_ctor_get(v_val_3260_, 2);
lean_dec(v_unused_3280_);
v___x_3267_ = v_val_3260_;
v_isShared_3268_ = v_isSharedCheck_3278_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_leftIndex_3265_);
lean_inc(v_leftCount_3264_);
lean_dec(v_val_3260_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3278_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3269_ = lean_unsigned_to_nat(1u);
v___x_3270_ = lean_nat_add(v_leftCount_3264_, v___x_3269_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v_index_3251_);
v___x_3272_ = v___x_3262_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_index_3251_);
v___x_3272_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3274_; 
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 3, v___x_3272_);
lean_ctor_set(v___x_3267_, 2, v___x_3270_);
v___x_3274_ = v___x_3267_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_leftCount_3264_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_leftIndex_3265_);
lean_ctor_set(v_reuseFailAlloc_3276_, 2, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3276_, 3, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3250_, v_val_3252_, v___x_3274_);
return v___x_3275_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(lean_object* v_upperBound_3282_, lean_object* v___x_3283_, lean_object* v_fst_3284_, lean_object* v___x_3285_, lean_object* v_a_3286_, lean_object* v_b_3287_){
_start:
{
uint8_t v___x_3288_; 
v___x_3288_ = lean_nat_dec_lt(v_a_3286_, v_upperBound_3282_);
if (v___x_3288_ == 0)
{
lean_dec(v_a_3286_);
return v_b_3287_;
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3289_ = l_Subarray_get___redArg(v_fst_3284_, v_a_3286_);
lean_inc(v_a_3286_);
v___x_3290_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_b_3287_, v_a_3286_, v___x_3289_);
v___x_3291_ = lean_unsigned_to_nat(1u);
v___x_3292_ = lean_nat_add(v_a_3286_, v___x_3291_);
lean_dec(v_a_3286_);
v_a_3286_ = v___x_3292_;
v_b_3287_ = v___x_3290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg___boxed(lean_object* v_upperBound_3294_, lean_object* v___x_3295_, lean_object* v_fst_3296_, lean_object* v___x_3297_, lean_object* v_a_3298_, lean_object* v_b_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3294_, v___x_3295_, v_fst_3296_, v___x_3297_, v_a_3298_, v_b_3299_);
lean_dec(v___x_3297_);
lean_dec_ref(v_fst_3296_);
lean_dec(v___x_3295_);
lean_dec(v_upperBound_3294_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(lean_object* v_a_3301_, lean_object* v_b_3302_){
_start:
{
lean_object* v_array_3303_; lean_object* v_start_3304_; lean_object* v_stop_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3318_; 
v_array_3303_ = lean_ctor_get(v_a_3301_, 0);
v_start_3304_ = lean_ctor_get(v_a_3301_, 1);
v_stop_3305_ = lean_ctor_get(v_a_3301_, 2);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_a_3301_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3307_ = v_a_3301_;
v_isShared_3308_ = v_isSharedCheck_3318_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_stop_3305_);
lean_inc(v_start_3304_);
lean_inc(v_array_3303_);
lean_dec(v_a_3301_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3318_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
uint8_t v___x_3309_; 
v___x_3309_ = lean_nat_dec_lt(v_start_3304_, v_stop_3305_);
if (v___x_3309_ == 0)
{
lean_del_object(v___x_3307_);
lean_dec(v_stop_3305_);
lean_dec(v_start_3304_);
lean_dec_ref(v_array_3303_);
return v_b_3302_;
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3310_ = lean_unsigned_to_nat(1u);
v___x_3311_ = lean_nat_add(v_start_3304_, v___x_3310_);
lean_inc_ref(v_array_3303_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 1, v___x_3311_);
v___x_3313_ = v___x_3307_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_array_3303_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3317_, 2, v_stop_3305_);
v___x_3313_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = lean_array_fget(v_array_3303_, v_start_3304_);
lean_dec(v_start_3304_);
lean_dec_ref(v_array_3303_);
v___x_3315_ = lean_array_push(v_b_3302_, v___x_3314_);
v_a_3301_ = v___x_3313_;
v_b_3302_ = v___x_3315_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(lean_object* v_left_3319_, lean_object* v_right_3320_, lean_object* v_i_3321_){
_start:
{
lean_object* v_start_3322_; lean_object* v_stop_3323_; lean_object* v_start_3324_; lean_object* v_stop_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; lean_object* v___x_3328_; uint8_t v___y_3330_; 
v_start_3322_ = lean_ctor_get(v_left_3319_, 1);
v_stop_3323_ = lean_ctor_get(v_left_3319_, 2);
v_start_3324_ = lean_ctor_get(v_right_3320_, 1);
v_stop_3325_ = lean_ctor_get(v_right_3320_, 2);
v___x_3326_ = lean_nat_sub(v_stop_3323_, v_start_3322_);
v___x_3327_ = lean_nat_dec_lt(v_i_3321_, v___x_3326_);
v___x_3328_ = lean_nat_sub(v_stop_3325_, v_start_3324_);
if (v___x_3327_ == 0)
{
v___y_3330_ = v___x_3327_;
goto v___jp_3329_;
}
else
{
uint8_t v___x_3357_; 
v___x_3357_ = lean_nat_dec_lt(v_i_3321_, v___x_3328_);
v___y_3330_ = v___x_3357_;
goto v___jp_3329_;
}
v___jp_3329_:
{
if (v___y_3330_ == 0)
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3331_ = lean_nat_sub(v___x_3326_, v_i_3321_);
lean_dec(v___x_3326_);
lean_inc_ref(v_left_3319_);
v___x_3332_ = l_Subarray_take___redArg(v_left_3319_, v___x_3331_);
v___x_3333_ = lean_nat_sub(v___x_3328_, v_i_3321_);
lean_dec(v_i_3321_);
lean_dec(v___x_3328_);
v___x_3334_ = l_Subarray_take___redArg(v_right_3320_, v___x_3333_);
lean_dec(v___x_3333_);
v___x_3335_ = l_Subarray_drop___redArg(v_left_3319_, v___x_3331_);
lean_dec(v___x_3331_);
v___x_3336_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3337_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3335_, v___x_3336_);
v___x_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3334_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3332_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
return v___x_3339_;
}
else
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v___x_3340_ = lean_nat_sub(v___x_3326_, v_i_3321_);
lean_dec(v___x_3326_);
v___x_3341_ = lean_unsigned_to_nat(1u);
v___x_3342_ = lean_nat_sub(v___x_3340_, v___x_3341_);
v___x_3343_ = l_Subarray_get___redArg(v_left_3319_, v___x_3342_);
lean_dec(v___x_3342_);
v___x_3344_ = lean_nat_sub(v___x_3328_, v_i_3321_);
lean_dec(v___x_3328_);
v___x_3345_ = lean_nat_sub(v___x_3344_, v___x_3341_);
v___x_3346_ = l_Subarray_get___redArg(v_right_3320_, v___x_3345_);
lean_dec(v___x_3345_);
v___x_3347_ = lean_string_dec_eq(v___x_3343_, v___x_3346_);
lean_dec(v___x_3346_);
lean_dec(v___x_3343_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
lean_dec(v_i_3321_);
lean_inc_ref(v_left_3319_);
v___x_3348_ = l_Subarray_take___redArg(v_left_3319_, v___x_3340_);
v___x_3349_ = l_Subarray_take___redArg(v_right_3320_, v___x_3344_);
lean_dec(v___x_3344_);
v___x_3350_ = l_Subarray_drop___redArg(v_left_3319_, v___x_3340_);
lean_dec(v___x_3340_);
v___x_3351_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3352_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3350_, v___x_3351_);
v___x_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3349_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3348_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
return v___x_3354_;
}
else
{
lean_object* v___x_3355_; 
lean_dec(v___x_3344_);
lean_dec(v___x_3340_);
v___x_3355_ = lean_nat_add(v_i_3321_, v___x_3341_);
lean_dec(v_i_3321_);
v_i_3321_ = v___x_3355_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(lean_object* v_left_3358_, lean_object* v_right_3359_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = lean_unsigned_to_nat(0u);
v___x_3361_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(v_left_3358_, v_right_3359_, v___x_3360_);
return v___x_3361_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3362_ = lean_box(0);
v___x_3363_ = lean_unsigned_to_nat(16u);
v___x_3364_ = lean_mk_array(v___x_3363_, v___x_3362_);
return v___x_3364_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1(void){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v_hist_3367_; 
v___x_3365_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0);
v___x_3366_ = lean_unsigned_to_nat(0u);
v_hist_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3367_, 0, v___x_3366_);
lean_ctor_set(v_hist_3367_, 1, v___x_3365_);
return v_hist_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_left_3368_, lean_object* v_right_3369_){
_start:
{
lean_object* v___x_3370_; lean_object* v_snd_3371_; lean_object* v_fst_3372_; lean_object* v_fst_3373_; lean_object* v_snd_3374_; lean_object* v___x_3375_; lean_object* v_snd_3376_; lean_object* v_fst_3377_; lean_object* v_fst_3378_; lean_object* v_snd_3379_; lean_object* v_start_3380_; lean_object* v_stop_3381_; lean_object* v___x_3382_; lean_object* v_hist_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v_start_3386_; lean_object* v_stop_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v_buckets_3390_; lean_object* v___x_3391_; lean_object* v___y_3393_; lean_object* v___x_3419_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3370_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(v_left_3368_, v_right_3369_);
v_snd_3371_ = lean_ctor_get(v___x_3370_, 1);
lean_inc(v_snd_3371_);
v_fst_3372_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_fst_3372_);
lean_dec_ref(v___x_3370_);
v_fst_3373_ = lean_ctor_get(v_snd_3371_, 0);
lean_inc(v_fst_3373_);
v_snd_3374_ = lean_ctor_get(v_snd_3371_, 1);
lean_inc(v_snd_3374_);
lean_dec(v_snd_3371_);
v___x_3375_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(v_fst_3373_, v_snd_3374_);
v_snd_3376_ = lean_ctor_get(v___x_3375_, 1);
lean_inc(v_snd_3376_);
v_fst_3377_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_fst_3377_);
lean_dec_ref(v___x_3375_);
v_fst_3378_ = lean_ctor_get(v_snd_3376_, 0);
lean_inc(v_fst_3378_);
v_snd_3379_ = lean_ctor_get(v_snd_3376_, 1);
lean_inc(v_snd_3379_);
lean_dec(v_snd_3376_);
v_start_3380_ = lean_ctor_get(v_fst_3377_, 1);
v_stop_3381_ = lean_ctor_get(v_fst_3377_, 2);
v___x_3382_ = lean_unsigned_to_nat(0u);
v_hist_3383_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1);
v___x_3384_ = lean_nat_sub(v_stop_3381_, v_start_3380_);
v___x_3385_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v___x_3384_, v_fst_3378_, v___x_3384_, v_fst_3377_, v___x_3382_, v_hist_3383_);
v_start_3386_ = lean_ctor_get(v_fst_3378_, 1);
v_stop_3387_ = lean_ctor_get(v_fst_3378_, 2);
v___x_3388_ = lean_nat_sub(v_stop_3387_, v_start_3386_);
v___x_3389_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v___x_3388_, v___x_3388_, v_fst_3378_, v___x_3384_, v___x_3382_, v___x_3385_);
lean_dec(v___x_3384_);
lean_dec(v___x_3388_);
v_buckets_3390_ = lean_ctor_get(v___x_3389_, 1);
lean_inc_ref(v_buckets_3390_);
lean_dec_ref(v___x_3389_);
v___x_3391_ = lean_box(0);
v___x_3419_ = lean_box(0);
v___x_3420_ = lean_array_get_size(v_buckets_3390_);
v___x_3421_ = lean_nat_dec_lt(v___x_3382_, v___x_3420_);
if (v___x_3421_ == 0)
{
lean_dec_ref(v_buckets_3390_);
v___y_3393_ = v___x_3419_;
goto v___jp_3392_;
}
else
{
size_t v___x_3422_; size_t v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = lean_usize_of_nat(v___x_3420_);
v___x_3423_ = ((size_t)0ULL);
v___x_3424_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_buckets_3390_, v___x_3422_, v___x_3423_, v___x_3419_);
lean_dec_ref(v_buckets_3390_);
v___y_3393_ = v___x_3424_;
goto v___jp_3392_;
}
v___jp_3392_:
{
lean_object* v___x_3394_; 
v___x_3394_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v___y_3393_, v___x_3391_);
lean_dec(v___y_3393_);
if (lean_obj_tag(v___x_3394_) == 1)
{
lean_object* v_val_3395_; lean_object* v_snd_3396_; lean_object* v_snd_3397_; lean_object* v_fst_3398_; lean_object* v_fst_3399_; lean_object* v_snd_3400_; lean_object* v___x_3401_; lean_object* v_fst_3402_; lean_object* v_snd_3403_; lean_object* v___x_3404_; lean_object* v_fst_3405_; lean_object* v_snd_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v_val_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_val_3395_);
lean_dec_ref_known(v___x_3394_, 1);
v_snd_3396_ = lean_ctor_get(v_val_3395_, 1);
lean_inc(v_snd_3396_);
lean_dec(v_val_3395_);
v_snd_3397_ = lean_ctor_get(v_snd_3396_, 1);
lean_inc(v_snd_3397_);
v_fst_3398_ = lean_ctor_get(v_snd_3396_, 0);
lean_inc(v_fst_3398_);
lean_dec(v_snd_3396_);
v_fst_3399_ = lean_ctor_get(v_snd_3397_, 0);
lean_inc(v_fst_3399_);
v_snd_3400_ = lean_ctor_get(v_snd_3397_, 1);
lean_inc(v_snd_3400_);
lean_dec(v_snd_3397_);
v___x_3401_ = l_Subarray_split___redArg(v_fst_3377_, v_fst_3399_);
lean_dec(v_fst_3399_);
v_fst_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_fst_3402_);
v_snd_3403_ = lean_ctor_get(v___x_3401_, 1);
lean_inc(v_snd_3403_);
lean_dec_ref(v___x_3401_);
v___x_3404_ = l_Subarray_split___redArg(v_fst_3378_, v_snd_3400_);
lean_dec(v_snd_3400_);
v_fst_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_fst_3405_);
v_snd_3406_ = lean_ctor_get(v___x_3404_, 1);
lean_inc(v_snd_3406_);
lean_dec_ref(v___x_3404_);
v___x_3407_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_fst_3402_, v_fst_3405_);
v___x_3408_ = l_Array_append___redArg(v_fst_3372_, v___x_3407_);
lean_dec_ref(v___x_3407_);
v___x_3409_ = lean_unsigned_to_nat(1u);
v___x_3410_ = lean_mk_empty_array_with_capacity(v___x_3409_);
v___x_3411_ = lean_array_push(v___x_3410_, v_fst_3398_);
v___x_3412_ = l_Array_append___redArg(v___x_3408_, v___x_3411_);
lean_dec_ref(v___x_3411_);
v___x_3413_ = l_Subarray_drop___redArg(v_snd_3403_, v___x_3409_);
v___x_3414_ = l_Subarray_drop___redArg(v_snd_3406_, v___x_3409_);
v___x_3415_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3413_, v___x_3414_);
v___x_3416_ = l_Array_append___redArg(v___x_3412_, v___x_3415_);
lean_dec_ref(v___x_3415_);
v___x_3417_ = l_Array_append___redArg(v___x_3416_, v_snd_3379_);
lean_dec(v_snd_3379_);
return v___x_3417_;
}
else
{
lean_object* v___x_3418_; 
lean_dec(v___x_3394_);
lean_dec(v_fst_3378_);
lean_dec(v_fst_3377_);
v___x_3418_ = l_Array_append___redArg(v_fst_3372_, v_snd_3379_);
lean_dec(v_snd_3379_);
return v___x_3418_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3425_, size_t v_i_3426_, lean_object* v_bs_3427_){
_start:
{
uint8_t v___x_3428_; 
v___x_3428_ = lean_usize_dec_lt(v_i_3426_, v_sz_3425_);
if (v___x_3428_ == 0)
{
return v_bs_3427_;
}
else
{
lean_object* v_v_3429_; lean_object* v___x_3430_; lean_object* v_bs_x27_3431_; uint8_t v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; size_t v___x_3435_; size_t v___x_3436_; lean_object* v___x_3437_; 
v_v_3429_ = lean_array_uget(v_bs_3427_, v_i_3426_);
v___x_3430_ = lean_unsigned_to_nat(0u);
v_bs_x27_3431_ = lean_array_uset(v_bs_3427_, v_i_3426_, v___x_3430_);
v___x_3432_ = 1;
v___x_3433_ = lean_box(v___x_3432_);
v___x_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
lean_ctor_set(v___x_3434_, 1, v_v_3429_);
v___x_3435_ = ((size_t)1ULL);
v___x_3436_ = lean_usize_add(v_i_3426_, v___x_3435_);
v___x_3437_ = lean_array_uset(v_bs_x27_3431_, v_i_3426_, v___x_3434_);
v_i_3426_ = v___x_3436_;
v_bs_3427_ = v___x_3437_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3439_, lean_object* v_i_3440_, lean_object* v_bs_3441_){
_start:
{
size_t v_sz_boxed_3442_; size_t v_i_boxed_3443_; lean_object* v_res_3444_; 
v_sz_boxed_3442_ = lean_unbox_usize(v_sz_3439_);
lean_dec(v_sz_3439_);
v_i_boxed_3443_ = lean_unbox_usize(v_i_3440_);
lean_dec(v_i_3440_);
v_res_3444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3442_, v_i_boxed_3443_, v_bs_3441_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3452_, lean_object* v_edited_3453_){
_start:
{
lean_object* v_i_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v_i_3454_ = lean_unsigned_to_nat(0u);
v___x_3455_ = lean_array_get_size(v_original_3452_);
v___x_3456_ = lean_nat_dec_lt(v_i_3454_, v___x_3455_);
if (v___x_3456_ == 0)
{
size_t v_sz_3457_; size_t v___x_3458_; lean_object* v___x_3459_; 
lean_dec_ref(v_original_3452_);
v_sz_3457_ = lean_array_size(v_edited_3453_);
v___x_3458_ = ((size_t)0ULL);
v___x_3459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3457_, v___x_3458_, v_edited_3453_);
return v___x_3459_;
}
else
{
lean_object* v___x_3460_; uint8_t v___x_3461_; 
v___x_3460_ = lean_array_get_size(v_edited_3453_);
v___x_3461_ = lean_nat_dec_lt(v_i_3454_, v___x_3460_);
if (v___x_3461_ == 0)
{
size_t v_sz_3462_; size_t v___x_3463_; lean_object* v___x_3464_; 
lean_dec_ref(v_edited_3453_);
v_sz_3462_ = lean_array_size(v_original_3452_);
v___x_3463_ = ((size_t)0ULL);
v___x_3464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3462_, v___x_3463_, v_original_3452_);
return v___x_3464_;
}
else
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v_ds_3467_; lean_object* v___x_3468_; size_t v_sz_3469_; size_t v___x_3470_; lean_object* v___x_3471_; lean_object* v_snd_3472_; lean_object* v_fst_3473_; lean_object* v_fst_3474_; lean_object* v_snd_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3494_; 
lean_inc_ref(v_original_3452_);
v___x_3465_ = l_Array_toSubarray___redArg(v_original_3452_, v_i_3454_, v___x_3455_);
lean_inc_ref(v_edited_3453_);
v___x_3466_ = l_Array_toSubarray___redArg(v_edited_3453_, v_i_3454_, v___x_3460_);
v_ds_3467_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3465_, v___x_3466_);
v___x_3468_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3469_ = lean_array_size(v_ds_3467_);
v___x_3470_ = ((size_t)0ULL);
v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_3460_, v_edited_3453_, v___x_3455_, v_original_3452_, v_ds_3467_, v_sz_3469_, v___x_3470_, v___x_3468_);
lean_dec_ref(v_ds_3467_);
v_snd_3472_ = lean_ctor_get(v___x_3471_, 1);
lean_inc(v_snd_3472_);
v_fst_3473_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_fst_3473_);
lean_dec_ref(v___x_3471_);
v_fst_3474_ = lean_ctor_get(v_snd_3472_, 0);
v_snd_3475_ = lean_ctor_get(v_snd_3472_, 1);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_snd_3472_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3477_ = v_snd_3472_;
v_isShared_3478_ = v_isSharedCheck_3494_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_snd_3475_);
lean_inc(v_fst_3474_);
lean_dec(v_snd_3472_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3494_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 1, v_fst_3474_);
lean_ctor_set(v___x_3477_, 0, v_fst_3473_);
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_fst_3473_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_fst_3474_);
v___x_3480_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3481_; lean_object* v_fst_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3491_; 
v___x_3481_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3455_, v_original_3452_, v___x_3480_);
lean_dec_ref(v_original_3452_);
v_fst_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3491_ == 0)
{
lean_object* v_unused_3492_; 
v_unused_3492_ = lean_ctor_get(v___x_3481_, 1);
lean_dec(v_unused_3492_);
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3491_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_fst_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3491_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 1, v_snd_3475_);
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_fst_3482_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_snd_3475_);
v___x_3487_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
lean_object* v___x_3488_; lean_object* v_fst_3489_; 
v___x_3488_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3460_, v_edited_3453_, v___x_3487_);
lean_dec_ref(v_edited_3453_);
v_fst_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_fst_3489_);
lean_dec_ref(v___x_3488_);
return v_fst_3489_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3495_, lean_object* v_x_3496_, lean_object* v_x_3497_){
_start:
{
if (lean_obj_tag(v_x_3496_) == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = l_List_reverse___redArg(v_x_3497_);
v___x_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
return v___x_3500_;
}
else
{
lean_object* v_head_3501_; lean_object* v_tail_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3511_; 
v_head_3501_ = lean_ctor_get(v_x_3496_, 0);
v_tail_3502_ = lean_ctor_get(v_x_3496_, 1);
v_isSharedCheck_3511_ = !lean_is_exclusive(v_x_3496_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3504_ = v_x_3496_;
v_isShared_3505_ = v_isSharedCheck_3511_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_tail_3502_);
lean_inc(v_head_3501_);
lean_dec(v_x_3496_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3511_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
v___x_3506_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3501_, v___y_3495_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 1, v_x_3497_);
lean_ctor_set(v___x_3504_, 0, v___x_3506_);
v___x_3508_ = v___x_3504_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3506_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_x_3497_);
v___x_3508_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
v_x_3496_ = v_tail_3502_;
v_x_3497_ = v___x_3508_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3512_, lean_object* v_x_3513_, lean_object* v_x_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3512_, v_x_3513_, v_x_3514_);
lean_dec(v___y_3512_);
return v_res_3516_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3523_ = l_Lean_stringToMessageData(v___x_3522_);
return v___x_3523_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5(void){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v___x_3537_; uint8_t v___x_3538_; 
v___x_3537_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
lean_inc(v_x_3533_);
v___x_3538_ = l_Lean_Syntax_isOfKind(v_x_3533_, v___x_3537_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; 
lean_dec(v_x_3533_);
v___x_3539_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3539_;
}
else
{
lean_object* v___x_3540_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; uint8_t v___y_3581_; uint8_t v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; uint8_t v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; uint8_t v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v_dc_x3f_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___x_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v___x_3540_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3788_ = lean_unsigned_to_nat(0u);
v___x_3789_ = l_Lean_Syntax_getArg(v_x_3533_, v___x_3788_);
v___x_3790_ = l_Lean_Syntax_isNone(v___x_3789_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3791_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3789_);
v___x_3792_ = l_Lean_Syntax_matchesNull(v___x_3789_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; 
lean_dec(v___x_3789_);
lean_dec(v_x_3533_);
v___x_3793_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3793_;
}
else
{
lean_object* v_dc_x3f_3794_; 
v_dc_x3f_3794_ = l_Lean_Syntax_getArg(v___x_3789_, v___x_3788_);
lean_dec(v___x_3789_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3797_; uint8_t v___x_3798_; 
v___x_3797_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3794_);
v___x_3798_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3794_, v___x_3797_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; 
lean_dec(v_dc_x3f_3794_);
lean_dec(v_x_3533_);
v___x_3799_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3799_;
}
else
{
goto v___jp_3795_;
}
}
else
{
goto v___jp_3795_;
}
v___jp_3795_:
{
lean_object* v___x_3796_; 
v___x_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3796_, 0, v_dc_x3f_3794_);
v_dc_x3f_3769_ = v___x_3796_;
v___y_3770_ = v_a_3534_;
v___y_3771_ = v_a_3535_;
goto v___jp_3768_;
}
}
}
else
{
lean_object* v___x_3800_; 
lean_dec(v___x_3789_);
v___x_3800_ = lean_box(0);
v_dc_x3f_3769_ = v___x_3800_;
v___y_3770_ = v_a_3534_;
v___y_3771_ = v_a_3535_;
goto v___jp_3768_;
}
v___jp_3541_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3547_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3548_ = l_Lean_stringToMessageData(v___y_3546_);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3544_, v___x_3549_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3544_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3570_; 
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; 
v_unused_3571_ = lean_ctor_get(v___x_3550_, 0);
lean_dec(v_unused_3571_);
v___x_3552_ = v___x_3550_;
v_isShared_3553_ = v_isSharedCheck_3570_;
goto v_resetjp_3551_;
}
else
{
lean_dec(v___x_3550_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3570_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_Elab_Command_getRef___redArg(v___y_3542_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3554_, 1);
v___x_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3540_);
lean_ctor_set(v___x_3556_, 1, v___y_3545_);
v___x_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3557_, 0, v_a_3555_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set_tag(v___x_3552_, 10);
lean_ctor_set(v___x_3552_, 0, v___x_3557_);
v___x_3559_ = v___x_3552_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3559_, v___y_3542_, v___y_3543_);
return v___x_3560_;
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_del_object(v___x_3552_);
lean_dec_ref(v___y_3545_);
v_a_3562_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3554_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3554_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3545_);
return v___x_3550_;
}
}
v___jp_3572_:
{
if (v___y_3581_ == 0)
{
lean_object* v___x_3582_; lean_object* v_env_3583_; lean_object* v_scopes_3584_; lean_object* v_usedQuotCtxts_3585_; lean_object* v_nextMacroScope_3586_; lean_object* v_maxRecDepth_3587_; lean_object* v_ngen_3588_; lean_object* v_auxDeclNGen_3589_; lean_object* v_infoState_3590_; lean_object* v_traceState_3591_; lean_object* v_snapshotTasks_3592_; lean_object* v_prevLinterStates_3593_; lean_object* v_codeQualityEntryTasks_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3620_; 
lean_dec(v___y_3574_);
v___x_3582_ = lean_st_ref_take(v___y_3576_);
v_env_3583_ = lean_ctor_get(v___x_3582_, 0);
v_scopes_3584_ = lean_ctor_get(v___x_3582_, 2);
v_usedQuotCtxts_3585_ = lean_ctor_get(v___x_3582_, 3);
v_nextMacroScope_3586_ = lean_ctor_get(v___x_3582_, 4);
v_maxRecDepth_3587_ = lean_ctor_get(v___x_3582_, 5);
v_ngen_3588_ = lean_ctor_get(v___x_3582_, 6);
v_auxDeclNGen_3589_ = lean_ctor_get(v___x_3582_, 7);
v_infoState_3590_ = lean_ctor_get(v___x_3582_, 8);
v_traceState_3591_ = lean_ctor_get(v___x_3582_, 9);
v_snapshotTasks_3592_ = lean_ctor_get(v___x_3582_, 10);
v_prevLinterStates_3593_ = lean_ctor_get(v___x_3582_, 11);
v_codeQualityEntryTasks_3594_ = lean_ctor_get(v___x_3582_, 12);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v___x_3582_, 1);
lean_dec(v_unused_3621_);
v___x_3596_ = v___x_3582_;
v_isShared_3597_ = v_isSharedCheck_3620_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3594_);
lean_inc(v_prevLinterStates_3593_);
lean_inc(v_snapshotTasks_3592_);
lean_inc(v_traceState_3591_);
lean_inc(v_infoState_3590_);
lean_inc(v_auxDeclNGen_3589_);
lean_inc(v_ngen_3588_);
lean_inc(v_maxRecDepth_3587_);
lean_inc(v_nextMacroScope_3586_);
lean_inc(v_usedQuotCtxts_3585_);
lean_inc(v_scopes_3584_);
lean_inc(v_env_3583_);
lean_dec(v___x_3582_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3620_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 1, v___y_3580_);
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_env_3583_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v___y_3580_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_scopes_3584_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v_usedQuotCtxts_3585_);
lean_ctor_set(v_reuseFailAlloc_3619_, 4, v_nextMacroScope_3586_);
lean_ctor_set(v_reuseFailAlloc_3619_, 5, v_maxRecDepth_3587_);
lean_ctor_set(v_reuseFailAlloc_3619_, 6, v_ngen_3588_);
lean_ctor_set(v_reuseFailAlloc_3619_, 7, v_auxDeclNGen_3589_);
lean_ctor_set(v_reuseFailAlloc_3619_, 8, v_infoState_3590_);
lean_ctor_set(v_reuseFailAlloc_3619_, 9, v_traceState_3591_);
lean_ctor_set(v_reuseFailAlloc_3619_, 10, v_snapshotTasks_3592_);
lean_ctor_set(v_reuseFailAlloc_3619_, 11, v_prevLinterStates_3593_);
lean_ctor_set(v_reuseFailAlloc_3619_, 12, v_codeQualityEntryTasks_3594_);
v___x_3599_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v_scopes_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v_opts_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3600_ = lean_st_ref_put(v___y_3576_, v___x_3599_);
v___x_3601_ = lean_st_ref_get(v___y_3576_);
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
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3575_);
lean_inc_ref(v___y_3579_);
v___y_3542_ = v___y_3573_;
v___y_3543_ = v___y_3576_;
v___y_3544_ = v___y_3578_;
v___y_3545_ = v___y_3579_;
v___y_3546_ = v___y_3579_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3608_ = lean_string_utf8_byte_size(v___y_3575_);
lean_inc(v___y_3577_);
lean_inc_ref(v___y_3575_);
v___x_3609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3609_, 0, v___y_3575_);
lean_ctor_set(v___x_3609_, 1, v___y_3577_);
lean_ctor_set(v___x_3609_, 2, v___x_3608_);
v___x_3610_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3609_);
v___x_3611_ = lean_mk_empty_array_with_capacity(v___y_3577_);
lean_inc_ref(v___x_3611_);
v___x_3612_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3575_, v___x_3609_, v___x_3608_, v___x_3610_, v___x_3611_);
lean_dec_ref_known(v___x_3609_, 3);
v___x_3613_ = lean_string_utf8_byte_size(v___y_3579_);
lean_inc_ref_n(v___y_3579_, 2);
v___x_3614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3614_, 0, v___y_3579_);
lean_ctor_set(v___x_3614_, 1, v___y_3577_);
lean_ctor_set(v___x_3614_, 2, v___x_3613_);
v___x_3615_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v___x_3614_);
v___x_3616_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3579_, v___x_3614_, v___x_3613_, v___x_3615_, v___x_3611_);
lean_dec_ref_known(v___x_3614_, 3);
v___x_3617_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3612_, v___x_3616_);
v___x_3618_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3617_);
lean_dec_ref(v___x_3617_);
v___y_3542_ = v___y_3573_;
v___y_3543_ = v___y_3576_;
v___y_3544_ = v___y_3578_;
v___y_3545_ = v___y_3579_;
v___y_3546_ = v___x_3618_;
goto v___jp_3541_;
}
}
}
}
else
{
lean_object* v___x_3622_; lean_object* v_env_3623_; lean_object* v_scopes_3624_; lean_object* v_usedQuotCtxts_3625_; lean_object* v_nextMacroScope_3626_; lean_object* v_maxRecDepth_3627_; lean_object* v_ngen_3628_; lean_object* v_auxDeclNGen_3629_; lean_object* v_infoState_3630_; lean_object* v_traceState_3631_; lean_object* v_snapshotTasks_3632_; lean_object* v_prevLinterStates_3633_; lean_object* v_codeQualityEntryTasks_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3644_; 
lean_dec_ref(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3575_);
v___x_3622_ = lean_st_ref_take(v___y_3576_);
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
v_codeQualityEntryTasks_3634_ = lean_ctor_get(v___x_3622_, 12);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3644_ == 0)
{
lean_object* v_unused_3645_; 
v_unused_3645_ = lean_ctor_get(v___x_3622_, 1);
lean_dec(v_unused_3645_);
v___x_3636_ = v___x_3622_;
v_isShared_3637_ = v_isSharedCheck_3644_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3634_);
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
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3644_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 1, v___y_3574_);
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_env_3623_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v___y_3574_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_scopes_3624_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v_usedQuotCtxts_3625_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v_nextMacroScope_3626_);
lean_ctor_set(v_reuseFailAlloc_3643_, 5, v_maxRecDepth_3627_);
lean_ctor_set(v_reuseFailAlloc_3643_, 6, v_ngen_3628_);
lean_ctor_set(v_reuseFailAlloc_3643_, 7, v_auxDeclNGen_3629_);
lean_ctor_set(v_reuseFailAlloc_3643_, 8, v_infoState_3630_);
lean_ctor_set(v_reuseFailAlloc_3643_, 9, v_traceState_3631_);
lean_ctor_set(v_reuseFailAlloc_3643_, 10, v_snapshotTasks_3632_);
lean_ctor_set(v_reuseFailAlloc_3643_, 11, v_prevLinterStates_3633_);
lean_ctor_set(v_reuseFailAlloc_3643_, 12, v_codeQualityEntryTasks_3634_);
v___x_3639_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = lean_st_ref_put(v___y_3576_, v___x_3639_);
v___x_3641_ = lean_box(0);
v___x_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
return v___x_3642_;
}
}
}
}
v___jp_3646_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v_a_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v_str_3669_; lean_object* v_startInclusive_3670_; lean_object* v_endExclusive_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3686_; 
v___x_3659_ = l_Lean_MessageLog_toList(v___y_3652_);
lean_dec(v___y_3652_);
v___x_3660_ = lean_box(0);
v___x_3661_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3658_, v___x_3659_, v___x_3660_);
lean_dec(v___y_3658_);
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v___x_3661_);
v___x_3663_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3657_, v_a_3662_);
v___x_3664_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4));
v___x_3665_ = l_String_intercalate(v___x_3664_, v___x_3663_);
v___x_3666_ = lean_string_utf8_byte_size(v___x_3665_);
lean_inc(v___y_3654_);
v___x_3667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3665_);
lean_ctor_set(v___x_3667_, 1, v___y_3654_);
lean_ctor_set(v___x_3667_, 2, v___x_3666_);
v___x_3668_ = l_String_Slice_trimAscii(v___x_3667_);
v_str_3669_ = lean_ctor_get(v___x_3668_, 0);
v_startInclusive_3670_ = lean_ctor_get(v___x_3668_, 1);
v_endExclusive_3671_ = lean_ctor_get(v___x_3668_, 2);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3673_ = v___x_3668_;
v_isShared_3674_ = v_isSharedCheck_3686_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_endExclusive_3671_);
lean_inc(v_startInclusive_3670_);
lean_inc(v_str_3669_);
lean_dec(v___x_3668_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3686_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; 
v___x_3675_ = lean_string_utf8_extract_fast(v_str_3669_, v_startInclusive_3670_, v_endExclusive_3671_);
lean_dec(v_endExclusive_3671_);
lean_dec(v_startInclusive_3670_);
lean_dec_ref(v_str_3669_);
if (v___y_3647_ == 0)
{
lean_object* v___x_3676_; lean_object* v___x_3677_; uint8_t v___x_3678_; 
lean_del_object(v___x_3673_);
lean_inc_ref(v___y_3651_);
v___x_3676_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3650_, v___y_3651_);
lean_inc_ref(v___x_3675_);
v___x_3677_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3650_, v___x_3675_);
v___x_3678_ = lean_string_dec_eq(v___x_3676_, v___x_3677_);
lean_dec_ref(v___x_3677_);
lean_dec_ref(v___x_3676_);
v___y_3573_ = v___y_3648_;
v___y_3574_ = v___y_3649_;
v___y_3575_ = v___y_3651_;
v___y_3576_ = v___y_3653_;
v___y_3577_ = v___y_3654_;
v___y_3578_ = v___y_3655_;
v___y_3579_ = v___x_3675_;
v___y_3580_ = v___y_3656_;
v___y_3581_ = v___x_3678_;
goto v___jp_3572_;
}
else
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3683_; 
lean_inc_ref(v___x_3675_);
v___x_3679_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3650_, v___x_3675_);
lean_inc_ref(v___y_3651_);
v___x_3680_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3650_, v___y_3651_);
v___x_3681_ = lean_string_utf8_byte_size(v___x_3679_);
lean_inc(v___y_3654_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 2, v___x_3681_);
lean_ctor_set(v___x_3673_, 1, v___y_3654_);
lean_ctor_set(v___x_3673_, 0, v___x_3679_);
v___x_3683_ = v___x_3673_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v___y_3654_);
lean_ctor_set(v_reuseFailAlloc_3685_, 2, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
uint8_t v___x_3684_; 
v___x_3684_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3680_, v___x_3683_);
lean_dec_ref(v___x_3683_);
v___y_3573_ = v___y_3648_;
v___y_3574_ = v___y_3649_;
v___y_3575_ = v___y_3651_;
v___y_3576_ = v___y_3653_;
v___y_3577_ = v___y_3654_;
v___y_3578_ = v___y_3655_;
v___y_3579_ = v___x_3675_;
v___y_3580_ = v___y_3656_;
v___y_3581_ = v___x_3684_;
goto v___jp_3572_;
}
}
}
}
v___jp_3687_:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3688_, v___y_3689_, v___y_3691_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v_filterFn_3696_; uint8_t v_whitespace_3697_; uint8_t v_ordering_3698_; uint8_t v_reportPositions_3699_; uint8_t v_substring_3700_; lean_object* v___x_3701_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3694_, 1);
v_filterFn_3696_ = lean_ctor_get(v_a_3695_, 0);
lean_inc_ref(v_filterFn_3696_);
v_whitespace_3697_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*1);
v_ordering_3698_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*1 + 1);
v_reportPositions_3699_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*1 + 2);
v_substring_3700_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*1 + 3);
lean_dec(v_a_3695_);
v___x_3701_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3690_, v___y_3689_, v___y_3691_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v_a_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v_str_3711_; lean_object* v_startInclusive_3712_; lean_object* v_endExclusive_3713_; lean_object* v_fst_3714_; lean_object* v_snd_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref_known(v___x_3701_, 1);
v___x_3703_ = l_Lean_MessageLog_toList(v_a_3702_);
v___x_3704_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5);
v___x_3705_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3696_, v___x_3703_, v___x_3704_);
lean_dec(v___x_3703_);
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref(v___x_3705_);
v___x_3707_ = lean_unsigned_to_nat(0u);
v___x_3708_ = lean_string_utf8_byte_size(v___y_3693_);
v___x_3709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3709_, 0, v___y_3693_);
lean_ctor_set(v___x_3709_, 1, v___x_3707_);
lean_ctor_set(v___x_3709_, 2, v___x_3708_);
v___x_3710_ = l_String_Slice_trimAscii(v___x_3709_);
v_str_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc_ref(v_str_3711_);
v_startInclusive_3712_ = lean_ctor_get(v___x_3710_, 1);
lean_inc(v_startInclusive_3712_);
v_endExclusive_3713_ = lean_ctor_get(v___x_3710_, 2);
lean_inc(v_endExclusive_3713_);
lean_dec_ref(v___x_3710_);
v_fst_3714_ = lean_ctor_get(v_a_3706_, 0);
lean_inc(v_fst_3714_);
v_snd_3715_ = lean_ctor_get(v_a_3706_, 1);
lean_inc(v_snd_3715_);
lean_dec(v_a_3706_);
v___x_3716_ = lean_string_utf8_extract_fast(v_str_3711_, v_startInclusive_3712_, v_endExclusive_3713_);
lean_dec(v_endExclusive_3713_);
lean_dec(v_startInclusive_3712_);
lean_dec_ref(v_str_3711_);
v___x_3717_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3716_);
if (v_reportPositions_3699_ == 0)
{
lean_object* v___x_3718_; 
v___x_3718_ = lean_box(0);
v___y_3647_ = v_substring_3700_;
v___y_3648_ = v___y_3689_;
v___y_3649_ = v_snd_3715_;
v___y_3650_ = v_whitespace_3697_;
v___y_3651_ = v___x_3717_;
v___y_3652_ = v_fst_3714_;
v___y_3653_ = v___y_3691_;
v___y_3654_ = v___x_3707_;
v___y_3655_ = v___y_3692_;
v___y_3656_ = v_a_3702_;
v___y_3657_ = v_ordering_3698_;
v___y_3658_ = v___x_3718_;
goto v___jp_3646_;
}
else
{
uint8_t v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = 0;
v___x_3720_ = l_Lean_Syntax_getPos_x3f(v___y_3692_, v___x_3719_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_box(0);
v___y_3647_ = v_substring_3700_;
v___y_3648_ = v___y_3689_;
v___y_3649_ = v_snd_3715_;
v___y_3650_ = v_whitespace_3697_;
v___y_3651_ = v___x_3717_;
v___y_3652_ = v_fst_3714_;
v___y_3653_ = v___y_3691_;
v___y_3654_ = v___x_3707_;
v___y_3655_ = v___y_3692_;
v___y_3656_ = v_a_3702_;
v___y_3657_ = v_ordering_3698_;
v___y_3658_ = v___x_3721_;
goto v___jp_3646_;
}
else
{
lean_object* v_val_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3732_; 
v_val_3722_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3724_ = v___x_3720_;
v_isShared_3725_ = v_isSharedCheck_3732_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_val_3722_);
lean_dec(v___x_3720_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3732_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v_fileMap_3726_; lean_object* v___x_3727_; lean_object* v_line_3728_; lean_object* v___x_3730_; 
v_fileMap_3726_ = lean_ctor_get(v___y_3689_, 1);
lean_inc_ref(v_fileMap_3726_);
v___x_3727_ = l_Lean_FileMap_toPosition(v_fileMap_3726_, v_val_3722_);
lean_dec(v_val_3722_);
v_line_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_line_3728_);
lean_dec_ref(v___x_3727_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v_line_3728_);
v___x_3730_ = v___x_3724_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_line_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
v___y_3647_ = v_substring_3700_;
v___y_3648_ = v___y_3689_;
v___y_3649_ = v_snd_3715_;
v___y_3650_ = v_whitespace_3697_;
v___y_3651_ = v___x_3717_;
v___y_3652_ = v_fst_3714_;
v___y_3653_ = v___y_3691_;
v___y_3654_ = v___x_3707_;
v___y_3655_ = v___y_3692_;
v___y_3656_ = v_a_3702_;
v___y_3657_ = v_ordering_3698_;
v___y_3658_ = v___x_3730_;
goto v___jp_3646_;
}
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec_ref(v_filterFn_3696_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
v_a_3733_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3701_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3701_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec(v___y_3690_);
v_a_3741_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3694_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3694_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
v___jp_3749_:
{
if (lean_obj_tag(v___y_3751_) == 0)
{
lean_object* v___x_3756_; 
v___x_3756_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_3688_ = v___y_3755_;
v___y_3689_ = v___y_3750_;
v___y_3690_ = v___y_3752_;
v___y_3691_ = v___y_3753_;
v___y_3692_ = v___y_3754_;
v___y_3693_ = v___x_3756_;
goto v___jp_3687_;
}
else
{
lean_object* v_val_3757_; lean_object* v___x_3758_; 
v_val_3757_ = lean_ctor_get(v___y_3751_, 0);
lean_inc(v_val_3757_);
lean_dec_ref_known(v___y_3751_, 1);
v___x_3758_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3757_, v___y_3750_, v___y_3753_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref_known(v___x_3758_, 1);
v___y_3688_ = v___y_3755_;
v___y_3689_ = v___y_3750_;
v___y_3690_ = v___y_3752_;
v___y_3691_ = v___y_3753_;
v___y_3692_ = v___y_3754_;
v___y_3693_ = v_a_3759_;
goto v___jp_3687_;
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_dec(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec(v___y_3752_);
v_a_3760_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3758_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3758_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
}
v___jp_3768_:
{
lean_object* v___x_3772_; lean_object* v_tk_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3772_ = lean_unsigned_to_nat(1u);
v_tk_3773_ = l_Lean_Syntax_getArg(v_x_3533_, v___x_3772_);
v___x_3774_ = lean_unsigned_to_nat(2u);
v___x_3775_ = l_Lean_Syntax_getArg(v_x_3533_, v___x_3774_);
v___x_3776_ = lean_unsigned_to_nat(4u);
v___x_3777_ = l_Lean_Syntax_getArg(v_x_3533_, v___x_3776_);
lean_dec(v_x_3533_);
v___x_3778_ = l_Lean_Syntax_getOptional_x3f(v___x_3775_);
lean_dec(v___x_3775_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v___x_3779_; 
v___x_3779_ = lean_box(0);
v___y_3750_ = v___y_3770_;
v___y_3751_ = v_dc_x3f_3769_;
v___y_3752_ = v___x_3777_;
v___y_3753_ = v___y_3771_;
v___y_3754_ = v_tk_3773_;
v___y_3755_ = v___x_3779_;
goto v___jp_3749_;
}
else
{
lean_object* v_val_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
v_val_3780_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3778_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_val_3780_);
lean_dec(v___x_3778_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_val_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
v___y_3750_ = v___y_3770_;
v___y_3751_ = v_dc_x3f_3769_;
v___y_3752_ = v___x_3777_;
v___y_3753_ = v___y_3771_;
v___y_3754_ = v_tk_3773_;
v___y_3755_ = v___x_3785_;
goto v___jp_3749_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3801_, v_a_3802_, v_a_3803_);
lean_dec(v_a_3803_);
lean_dec_ref(v_a_3802_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3806_, lean_object* v_as_3807_, lean_object* v_as_x27_3808_, lean_object* v_b_3809_, lean_object* v_a_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3806_, v_as_x27_3808_, v_b_3809_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3815_, lean_object* v_as_3816_, lean_object* v_as_x27_3817_, lean_object* v_b_3818_, lean_object* v_a_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3815_, v_as_3816_, v_as_x27_3817_, v_b_3818_, v_a_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v_as_x27_3817_);
lean_dec(v_as_3816_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3824_, lean_object* v_x_3825_, lean_object* v_x_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3824_, v_x_3825_, v_x_3826_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3831_, lean_object* v_x_3832_, lean_object* v_x_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3831_, v_x_3832_, v_x_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3831_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3838_, v___y_3840_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3848_, lean_object* v___x_3849_, lean_object* v___x_3850_, lean_object* v_inst_3851_, lean_object* v_R_3852_, lean_object* v_a_3853_, lean_object* v_b_3854_){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3848_, v___x_3849_, v___x_3850_, v_a_3853_, v_b_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3856_, lean_object* v___x_3857_, lean_object* v___x_3858_, lean_object* v_inst_3859_, lean_object* v_R_3860_, lean_object* v_a_3861_, lean_object* v_b_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3856_, v___x_3857_, v___x_3858_, v_inst_3859_, v_R_3860_, v_a_3861_, v_b_3862_);
lean_dec_ref(v___x_3857_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3864_, v___y_3866_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3869_, v___y_3870_, v___y_3871_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3874_, lean_object* v___x_3875_, lean_object* v___x_3876_, lean_object* v_inst_3877_, lean_object* v_R_3878_, lean_object* v_a_3879_, lean_object* v_b_3880_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3874_, v___x_3875_, v___x_3876_, v_a_3879_, v_b_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3882_, lean_object* v___x_3883_, lean_object* v___x_3884_, lean_object* v_inst_3885_, lean_object* v_R_3886_, lean_object* v_a_3887_, lean_object* v_b_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3882_, v___x_3883_, v___x_3884_, v_inst_3885_, v_R_3886_, v_a_3887_, v_b_3888_);
lean_dec_ref(v___x_3883_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v___x_3890_, lean_object* v_original_3891_, lean_object* v_a_3892_, lean_object* v_inst_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_3890_, v_original_3891_, v_a_3892_, v_a_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___boxed(lean_object* v___x_3896_, lean_object* v_original_3897_, lean_object* v_a_3898_, lean_object* v_inst_3899_, lean_object* v_a_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3896_, v_original_3897_, v_a_3898_, v_inst_3899_, v_a_3900_);
lean_dec_ref(v_a_3898_);
lean_dec_ref(v_original_3897_);
lean_dec(v___x_3896_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v___x_3902_, lean_object* v_edited_3903_, lean_object* v_a_3904_, lean_object* v_inst_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_3902_, v_edited_3903_, v_a_3904_, v_a_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v___x_3908_, lean_object* v_edited_3909_, lean_object* v_a_3910_, lean_object* v_inst_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v___x_3908_, v_edited_3909_, v_a_3910_, v_inst_3911_, v_a_3912_);
lean_dec_ref(v_a_3910_);
lean_dec_ref(v_edited_3909_);
lean_dec(v___x_3908_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3914_, lean_object* v_original_3915_, lean_object* v_inst_3916_, lean_object* v_a_3917_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3914_, v_original_3915_, v_a_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3919_, lean_object* v_original_3920_, lean_object* v_inst_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3919_, v_original_3920_, v_inst_3921_, v_a_3922_);
lean_dec_ref(v_original_3920_);
lean_dec(v___x_3919_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3924_, lean_object* v_edited_3925_, lean_object* v_inst_3926_, lean_object* v_a_3927_){
_start:
{
lean_object* v___x_3928_; 
v___x_3928_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3924_, v_edited_3925_, v_a_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3929_, lean_object* v_edited_3930_, lean_object* v_inst_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3929_, v_edited_3930_, v_inst_3931_, v_a_3932_);
lean_dec_ref(v_edited_3930_);
lean_dec(v___x_3929_);
return v_res_3933_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3934_, lean_object* v_inst_3935_, lean_object* v_R_3936_, lean_object* v_a_3937_, uint8_t v_b_3938_, lean_object* v_c_3939_){
_start:
{
uint8_t v___x_3940_; 
v___x_3940_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3934_, v_a_3937_, v_b_3938_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3941_, lean_object* v_inst_3942_, lean_object* v_R_3943_, lean_object* v_a_3944_, lean_object* v_b_3945_, lean_object* v_c_3946_){
_start:
{
uint8_t v_b_boxed_3947_; uint8_t v_res_3948_; lean_object* v_r_3949_; 
v_b_boxed_3947_ = lean_unbox(v_b_3945_);
v_res_3948_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3941_, v_inst_3942_, v_R_3943_, v_a_3944_, v_b_boxed_3947_, v_c_3946_);
lean_dec_ref(v_s_3941_);
v_r_3949_ = lean_box(v_res_3948_);
return v_r_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3950_, lean_object* v_ref_3951_, lean_object* v_msg_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3951_, v_msg_3952_, v___y_3953_, v___y_3954_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3957_, lean_object* v_ref_3958_, lean_object* v_msg_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3957_, v_ref_3958_, v_msg_3959_, v___y_3960_, v___y_3961_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec(v_ref_3958_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(lean_object* v_as_3964_, lean_object* v_as_x27_3965_, lean_object* v_b_3966_, lean_object* v_a_3967_){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3965_, v_b_3966_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___boxed(lean_object* v_as_3969_, lean_object* v_as_x27_3970_, lean_object* v_b_3971_, lean_object* v_a_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(v_as_3969_, v_as_x27_3970_, v_b_3971_, v_a_3972_);
lean_dec(v_as_x27_3970_);
lean_dec(v_as_3969_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(lean_object* v_lsize_3974_, lean_object* v_rsize_3975_, lean_object* v_histogram_3976_, lean_object* v_index_3977_, lean_object* v_val_3978_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_histogram_3976_, v_index_3977_, v_val_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___boxed(lean_object* v_lsize_3980_, lean_object* v_rsize_3981_, lean_object* v_histogram_3982_, lean_object* v_index_3983_, lean_object* v_val_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(v_lsize_3980_, v_rsize_3981_, v_histogram_3982_, v_index_3983_, v_val_3984_);
lean_dec(v_rsize_3981_);
lean_dec(v_lsize_3980_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(lean_object* v_upperBound_3986_, lean_object* v___x_3987_, lean_object* v_fst_3988_, lean_object* v___x_3989_, lean_object* v_inst_3990_, lean_object* v_R_3991_, lean_object* v_a_3992_, lean_object* v_b_3993_, lean_object* v_c_3994_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3986_, v___x_3987_, v_fst_3988_, v___x_3989_, v_a_3992_, v_b_3993_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___boxed(lean_object* v_upperBound_3996_, lean_object* v___x_3997_, lean_object* v_fst_3998_, lean_object* v___x_3999_, lean_object* v_inst_4000_, lean_object* v_R_4001_, lean_object* v_a_4002_, lean_object* v_b_4003_, lean_object* v_c_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(v_upperBound_3996_, v___x_3997_, v_fst_3998_, v___x_3999_, v_inst_4000_, v_R_4001_, v_a_4002_, v_b_4003_, v_c_4004_);
lean_dec(v___x_3999_);
lean_dec_ref(v_fst_3998_);
lean_dec(v___x_3997_);
lean_dec(v_upperBound_3996_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(lean_object* v_lsize_4006_, lean_object* v_rsize_4007_, lean_object* v_histogram_4008_, lean_object* v_index_4009_, lean_object* v_val_4010_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_histogram_4008_, v_index_4009_, v_val_4010_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___boxed(lean_object* v_lsize_4012_, lean_object* v_rsize_4013_, lean_object* v_histogram_4014_, lean_object* v_index_4015_, lean_object* v_val_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(v_lsize_4012_, v_rsize_4013_, v_histogram_4014_, v_index_4015_, v_val_4016_);
lean_dec(v_rsize_4013_);
lean_dec(v_lsize_4012_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(lean_object* v_upperBound_4018_, lean_object* v_fst_4019_, lean_object* v___x_4020_, lean_object* v_fst_4021_, lean_object* v_inst_4022_, lean_object* v_R_4023_, lean_object* v_a_4024_, lean_object* v_b_4025_, lean_object* v_c_4026_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_4018_, v_fst_4019_, v___x_4020_, v_fst_4021_, v_a_4024_, v_b_4025_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___boxed(lean_object* v_upperBound_4028_, lean_object* v_fst_4029_, lean_object* v___x_4030_, lean_object* v_fst_4031_, lean_object* v_inst_4032_, lean_object* v_R_4033_, lean_object* v_a_4034_, lean_object* v_b_4035_, lean_object* v_c_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(v_upperBound_4028_, v_fst_4029_, v___x_4030_, v_fst_4031_, v_inst_4032_, v_R_4033_, v_a_4034_, v_b_4035_, v_c_4036_);
lean_dec_ref(v_fst_4031_);
lean_dec(v___x_4030_);
lean_dec_ref(v_fst_4029_);
lean_dec(v_upperBound_4028_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_4038_, lean_object* v_msg_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v___x_4043_; 
v___x_4043_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_4039_, v___y_4040_, v___y_4041_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_4044_, lean_object* v_msg_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_4044_, v_msg_4045_, v___y_4046_, v___y_4047_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(lean_object* v_00_u03b2_4050_, lean_object* v_m_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_4051_, v_a_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___boxed(lean_object* v_00_u03b2_4054_, lean_object* v_m_4055_, lean_object* v_a_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(v_00_u03b2_4054_, v_m_4055_, v_a_4056_);
lean_dec_ref(v_a_4056_);
lean_dec_ref(v_m_4055_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26(lean_object* v_00_u03b2_4058_, lean_object* v_m_4059_, lean_object* v_a_4060_, lean_object* v_b_4061_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_m_4059_, v_a_4060_, v_b_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_4063_, lean_object* v_macroStack_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_4063_, v_macroStack_4064_, v___y_4066_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4069_, lean_object* v_macroStack_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4069_, v_macroStack_4070_, v___y_4071_, v___y_4072_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29(lean_object* v_inst_4075_, lean_object* v_R_4076_, lean_object* v_a_4077_, lean_object* v_b_4078_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v_a_4077_, v_b_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(lean_object* v_00_u03b2_4080_, lean_object* v_a_4081_, lean_object* v_x_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_4081_, v_x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___boxed(lean_object* v_00_u03b2_4084_, lean_object* v_a_4085_, lean_object* v_x_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(v_00_u03b2_4084_, v_a_4085_, v_x_4086_);
lean_dec(v_x_4086_);
lean_dec_ref(v_a_4085_);
return v_res_4087_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(lean_object* v_00_u03b2_4088_, lean_object* v_a_4089_, lean_object* v_x_4090_){
_start:
{
uint8_t v___x_4091_; 
v___x_4091_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_4089_, v_x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___boxed(lean_object* v_00_u03b2_4092_, lean_object* v_a_4093_, lean_object* v_x_4094_){
_start:
{
uint8_t v_res_4095_; lean_object* v_r_4096_; 
v_res_4095_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(v_00_u03b2_4092_, v_a_4093_, v_x_4094_);
lean_dec(v_x_4094_);
lean_dec_ref(v_a_4093_);
v_r_4096_ = lean_box(v_res_4095_);
return v_r_4096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38(lean_object* v_00_u03b2_4097_, lean_object* v_data_4098_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_data_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39(lean_object* v_00_u03b2_4100_, lean_object* v_a_4101_, lean_object* v_b_4102_, lean_object* v_x_4103_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_4101_, v_b_4102_, v_x_4103_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44(lean_object* v_00_u03b2_4105_, lean_object* v_i_4106_, lean_object* v_source_4107_, lean_object* v_target_4108_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v_i_4106_, v_source_4107_, v_target_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4110_, lean_object* v_x_4111_, lean_object* v_x_4112_){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_x_4111_, v_x_4112_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4122_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4123_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
v___x_4124_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4125_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4126_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4122_, v___x_4123_, v___x_4124_, v___x_4125_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4155_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4156_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4157_ = l_Lean_addBuiltinDeclarationRanges(v___x_4155_, v___x_4156_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4160_){
_start:
{
lean_object* v_doc_4162_; lean_object* v___x_4163_; 
v_doc_4162_ = lean_ctor_get(v___y_4160_, 1);
lean_inc_ref(v_doc_4162_);
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v_doc_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4164_);
lean_dec_ref(v___y_4164_);
return v_res_4166_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4167_, lean_object* v_a_4168_, uint8_t v_b_4169_){
_start:
{
lean_object* v_str_4170_; lean_object* v_startInclusive_4171_; lean_object* v_endExclusive_4172_; lean_object* v___x_4173_; uint8_t v_decide_4174_; 
v_str_4170_ = lean_ctor_get(v_s_4167_, 0);
v_startInclusive_4171_ = lean_ctor_get(v_s_4167_, 1);
v_endExclusive_4172_ = lean_ctor_get(v_s_4167_, 2);
v___x_4173_ = lean_nat_sub(v_endExclusive_4172_, v_startInclusive_4171_);
v_decide_4174_ = lean_nat_dec_eq(v_a_4168_, v___x_4173_);
lean_dec(v___x_4173_);
if (v_decide_4174_ == 0)
{
lean_object* v___x_4175_; uint32_t v___x_4176_; uint32_t v___x_4177_; uint8_t v___x_4178_; 
v___x_4175_ = lean_nat_add(v_startInclusive_4171_, v_a_4168_);
lean_dec(v_a_4168_);
v___x_4176_ = lean_string_utf8_get_fast(v_str_4170_, v___x_4175_);
v___x_4177_ = 10;
v___x_4178_ = lean_uint32_dec_eq(v___x_4176_, v___x_4177_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = lean_string_utf8_next_fast(v_str_4170_, v___x_4175_);
lean_dec(v___x_4175_);
v___x_4180_ = lean_nat_sub(v___x_4179_, v_startInclusive_4171_);
v_a_4168_ = v___x_4180_;
v_b_4169_ = v___x_4178_;
goto _start;
}
else
{
lean_dec(v___x_4175_);
return v___x_4178_;
}
}
else
{
lean_dec(v_a_4168_);
return v_b_4169_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4182_, lean_object* v_a_4183_, lean_object* v_b_4184_){
_start:
{
uint8_t v_b_boxed_4185_; uint8_t v_res_4186_; lean_object* v_r_4187_; 
v_b_boxed_4185_ = lean_unbox(v_b_4184_);
v_res_4186_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4182_, v_a_4183_, v_b_boxed_4185_);
lean_dec_ref(v_s_4182_);
v_r_4187_ = lean_box(v_res_4186_);
return v_r_4187_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4188_){
_start:
{
lean_object* v_searcher_4189_; uint8_t v___x_4190_; uint8_t v___x_4191_; 
v_searcher_4189_ = lean_unsigned_to_nat(0u);
v___x_4190_ = 0;
v___x_4191_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4188_, v_searcher_4189_, v___x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4192_){
_start:
{
uint8_t v_res_4193_; lean_object* v_r_4194_; 
v_res_4193_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4192_);
lean_dec_ref(v_s_4192_);
v_r_4194_ = lean_box(v_res_4193_);
return v_r_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4206_, lean_object* v_fst_4207_, uint8_t v___x_4208_, lean_object* v_a_4209_, lean_object* v___x_4210_, lean_object* v___x_4211_, lean_object* v___x_4212_, lean_object* v___x_4213_, lean_object* v___x_4214_, lean_object* v___x_4215_, lean_object* v___x_4216_, lean_object* v___x_4217_, lean_object* v_snd_4218_, lean_object* v___x_4219_){
_start:
{
if (lean_obj_tag(v___x_4206_) == 1)
{
lean_object* v_val_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4282_; 
v_val_4221_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4223_ = v___x_4206_;
v_isShared_4224_ = v_isSharedCheck_4282_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_val_4221_);
lean_dec(v___x_4206_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4282_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4225_ = lean_unsigned_to_nat(0u);
v___x_4226_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4227_ = l_Lean_Syntax_setArg(v_fst_4207_, v___x_4225_, v___x_4226_);
v___x_4228_ = l_Lean_Syntax_getPos_x3f(v___x_4227_, v___x_4208_);
lean_dec(v___x_4227_);
if (lean_obj_tag(v___x_4228_) == 1)
{
lean_object* v_val_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4278_; 
lean_dec_ref(v___x_4219_);
v_val_4229_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4231_ = v___x_4228_;
v_isShared_4232_ = v_isSharedCheck_4278_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_val_4229_);
lean_dec(v___x_4228_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4278_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___y_4234_; lean_object* v___x_4260_; lean_object* v___x_4266_; uint8_t v___x_4267_; 
v___x_4260_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4218_);
v___x_4266_ = lean_string_utf8_byte_size(v___x_4260_);
v___x_4267_ = lean_nat_dec_eq(v___x_4266_, v___x_4225_);
if (v___x_4267_ == 0)
{
lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v___x_4268_ = lean_string_length(v___x_4260_);
v___x_4269_ = lean_unsigned_to_nat(93u);
v___x_4270_ = lean_nat_dec_le(v___x_4268_, v___x_4269_);
if (v___x_4270_ == 0)
{
goto v___jp_4261_;
}
else
{
lean_object* v___x_4271_; uint8_t v___x_4272_; 
lean_inc_ref(v___x_4260_);
v___x_4271_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4260_);
lean_ctor_set(v___x_4271_, 1, v___x_4225_);
lean_ctor_set(v___x_4271_, 2, v___x_4266_);
v___x_4272_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4271_);
lean_dec_ref_known(v___x_4271_, 3);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4273_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4274_ = lean_string_append(v___x_4273_, v___x_4260_);
lean_dec_ref(v___x_4260_);
v___x_4275_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4276_ = lean_string_append(v___x_4274_, v___x_4275_);
v___y_4234_ = v___x_4276_;
goto v___jp_4233_;
}
else
{
goto v___jp_4261_;
}
}
}
else
{
lean_object* v___x_4277_; 
lean_dec_ref(v___x_4260_);
v___x_4277_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
v___y_4234_ = v___x_4277_;
goto v___jp_4233_;
}
v___jp_4233_:
{
lean_object* v_toEditableDocumentCore_4235_; lean_object* v_meta_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4256_; 
v_toEditableDocumentCore_4235_ = lean_ctor_get(v_a_4209_, 0);
lean_inc_ref(v_toEditableDocumentCore_4235_);
v_meta_4236_ = lean_ctor_get(v_toEditableDocumentCore_4235_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v_toEditableDocumentCore_4235_);
if (v_isSharedCheck_4256_ == 0)
{
lean_object* v_unused_4257_; lean_object* v_unused_4258_; lean_object* v_unused_4259_; 
v_unused_4257_ = lean_ctor_get(v_toEditableDocumentCore_4235_, 3);
lean_dec(v_unused_4257_);
v_unused_4258_ = lean_ctor_get(v_toEditableDocumentCore_4235_, 2);
lean_dec(v_unused_4258_);
v_unused_4259_ = lean_ctor_get(v_toEditableDocumentCore_4235_, 1);
lean_dec(v_unused_4259_);
v___x_4238_ = v_toEditableDocumentCore_4235_;
v_isShared_4239_ = v_isSharedCheck_4256_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_meta_4236_);
lean_dec(v_toEditableDocumentCore_4235_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4256_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v_text_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4246_; 
v_text_4240_ = lean_ctor_get(v_meta_4236_, 3);
lean_inc_ref(v_text_4240_);
lean_dec_ref(v_meta_4236_);
v___x_4241_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4209_);
v___x_4242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4242_, 0, v_val_4221_);
lean_ctor_set(v___x_4242_, 1, v_val_4229_);
v___x_4243_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4240_, v___x_4242_);
v___x_4244_ = lean_box(0);
lean_inc(v___x_4210_);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 3, v___x_4210_);
lean_ctor_set(v___x_4238_, 2, v___x_4244_);
lean_ctor_set(v___x_4238_, 1, v___y_4234_);
lean_ctor_set(v___x_4238_, 0, v___x_4243_);
v___x_4246_ = v___x_4238_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4243_);
lean_ctor_set(v_reuseFailAlloc_4255_, 1, v___y_4234_);
lean_ctor_set(v_reuseFailAlloc_4255_, 2, v___x_4244_);
lean_ctor_set(v_reuseFailAlloc_4255_, 3, v___x_4210_);
v___x_4246_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
lean_object* v___x_4247_; lean_object* v___x_4249_; 
v___x_4247_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4241_, v___x_4246_);
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v___x_4247_);
v___x_4249_ = v___x_4231_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4247_);
v___x_4249_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4250_; lean_object* v___x_4252_; 
lean_inc(v___x_4210_);
v___x_4250_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4210_);
lean_ctor_set(v___x_4250_, 1, v___x_4210_);
lean_ctor_set(v___x_4250_, 2, v___x_4211_);
lean_ctor_set(v___x_4250_, 3, v___x_4212_);
lean_ctor_set(v___x_4250_, 4, v___x_4213_);
lean_ctor_set(v___x_4250_, 5, v___x_4214_);
lean_ctor_set(v___x_4250_, 6, v___x_4215_);
lean_ctor_set(v___x_4250_, 7, v___x_4249_);
lean_ctor_set(v___x_4250_, 8, v___x_4216_);
lean_ctor_set(v___x_4250_, 9, v___x_4217_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set_tag(v___x_4223_, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4250_);
v___x_4252_ = v___x_4223_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4250_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
}
v___jp_4261_:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4262_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4263_ = lean_string_append(v___x_4262_, v___x_4260_);
lean_dec_ref(v___x_4260_);
v___x_4264_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4265_ = lean_string_append(v___x_4263_, v___x_4264_);
v___y_4234_ = v___x_4265_;
goto v___jp_4233_;
}
}
}
else
{
lean_object* v___x_4280_; 
lean_dec(v___x_4228_);
lean_dec(v_val_4221_);
lean_dec_ref(v_snd_4218_);
lean_dec(v___x_4217_);
lean_dec(v___x_4216_);
lean_dec(v___x_4215_);
lean_dec(v___x_4214_);
lean_dec(v___x_4213_);
lean_dec(v___x_4212_);
lean_dec_ref(v___x_4211_);
lean_dec(v___x_4210_);
lean_dec_ref(v_a_4209_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set_tag(v___x_4223_, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4219_);
v___x_4280_ = v___x_4223_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4219_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
else
{
lean_object* v___x_4283_; 
lean_dec_ref(v_snd_4218_);
lean_dec(v___x_4217_);
lean_dec(v___x_4216_);
lean_dec(v___x_4215_);
lean_dec(v___x_4214_);
lean_dec(v___x_4213_);
lean_dec(v___x_4212_);
lean_dec_ref(v___x_4211_);
lean_dec(v___x_4210_);
lean_dec_ref(v_a_4209_);
lean_dec(v_fst_4207_);
lean_dec(v___x_4206_);
v___x_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4219_);
return v___x_4283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4284_, lean_object* v_fst_4285_, lean_object* v___x_4286_, lean_object* v_a_4287_, lean_object* v___x_4288_, lean_object* v___x_4289_, lean_object* v___x_4290_, lean_object* v___x_4291_, lean_object* v___x_4292_, lean_object* v___x_4293_, lean_object* v___x_4294_, lean_object* v___x_4295_, lean_object* v_snd_4296_, lean_object* v___x_4297_, lean_object* v___y_4298_){
_start:
{
uint8_t v___x_4487__boxed_4299_; lean_object* v_res_4300_; 
v___x_4487__boxed_4299_ = lean_unbox(v___x_4286_);
v_res_4300_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4284_, v_fst_4285_, v___x_4487__boxed_4299_, v_a_4287_, v___x_4288_, v___x_4289_, v___x_4290_, v___x_4291_, v___x_4292_, v___x_4293_, v___x_4294_, v___x_4295_, v_snd_4296_, v___x_4297_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4304_, size_t v_sz_4305_, size_t v_i_4306_, lean_object* v_b_4307_){
_start:
{
lean_object* v_a_4309_; uint8_t v___x_4313_; 
v___x_4313_ = lean_usize_dec_lt(v_i_4306_, v_sz_4305_);
if (v___x_4313_ == 0)
{
lean_inc_ref(v_b_4307_);
return v_b_4307_;
}
else
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v_a_4316_; 
v___x_4314_ = lean_box(0);
v___x_4315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4316_ = lean_array_uget(v_as_4304_, v_i_4306_);
if (lean_obj_tag(v_a_4316_) == 1)
{
lean_object* v_i_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4351_; 
v_i_4317_ = lean_ctor_get(v_a_4316_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v_a_4316_);
if (v_isSharedCheck_4351_ == 0)
{
lean_object* v_unused_4352_; 
v_unused_4352_ = lean_ctor_get(v_a_4316_, 1);
lean_dec(v_unused_4352_);
v___x_4319_ = v_a_4316_;
v_isShared_4320_ = v_isSharedCheck_4351_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_i_4317_);
lean_dec(v_a_4316_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4351_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
if (lean_obj_tag(v_i_4317_) == 10)
{
lean_object* v_i_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4350_; 
v_i_4321_ = lean_ctor_get(v_i_4317_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v_i_4317_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4323_ = v_i_4317_;
v_isShared_4324_ = v_isSharedCheck_4350_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_i_4321_);
lean_dec(v_i_4317_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4350_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v_stx_4325_; lean_object* v_value_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4349_; 
v_stx_4325_ = lean_ctor_get(v_i_4321_, 0);
v_value_4326_ = lean_ctor_get(v_i_4321_, 1);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_i_4321_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4328_ = v_i_4321_;
v_isShared_4329_ = v_isSharedCheck_4349_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_value_4326_);
lean_inc(v_stx_4325_);
lean_dec(v_i_4321_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4349_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4330_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4331_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4326_, v___x_4330_);
lean_dec(v_value_4326_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_del_object(v___x_4328_);
lean_dec(v_stx_4325_);
lean_del_object(v___x_4323_);
lean_del_object(v___x_4319_);
v_a_4309_ = v___x_4315_;
goto v___jp_4308_;
}
else
{
lean_object* v_val_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4348_; 
v_val_4332_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4334_ = v___x_4331_;
v_isShared_4335_ = v_isSharedCheck_4348_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_val_4332_);
lean_dec(v___x_4331_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4348_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 1, v_val_4332_);
v___x_4337_ = v___x_4328_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_stx_4325_);
lean_ctor_set(v_reuseFailAlloc_4347_, 1, v_val_4332_);
v___x_4337_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
lean_object* v___x_4339_; 
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 0, v___x_4337_);
v___x_4339_ = v___x_4334_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4337_);
v___x_4339_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4341_; 
if (v_isShared_4324_ == 0)
{
lean_ctor_set_tag(v___x_4323_, 1);
lean_ctor_set(v___x_4323_, 0, v___x_4339_);
v___x_4341_ = v___x_4323_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4339_);
v___x_4341_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
lean_object* v___x_4343_; 
if (v_isShared_4320_ == 0)
{
lean_ctor_set_tag(v___x_4319_, 0);
lean_ctor_set(v___x_4319_, 1, v___x_4314_);
lean_ctor_set(v___x_4319_, 0, v___x_4341_);
v___x_4343_ = v___x_4319_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4341_);
lean_ctor_set(v_reuseFailAlloc_4344_, 1, v___x_4314_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
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
lean_del_object(v___x_4319_);
lean_dec_ref(v_i_4317_);
v_a_4309_ = v___x_4315_;
goto v___jp_4308_;
}
}
}
else
{
lean_dec(v_a_4316_);
v_a_4309_ = v___x_4315_;
goto v___jp_4308_;
}
}
v___jp_4308_:
{
size_t v___x_4310_; size_t v___x_4311_; 
v___x_4310_ = ((size_t)1ULL);
v___x_4311_ = lean_usize_add(v_i_4306_, v___x_4310_);
v_i_4306_ = v___x_4311_;
v_b_4307_ = v_a_4309_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4353_, lean_object* v_sz_4354_, lean_object* v_i_4355_, lean_object* v_b_4356_){
_start:
{
size_t v_sz_boxed_4357_; size_t v_i_boxed_4358_; lean_object* v_res_4359_; 
v_sz_boxed_4357_ = lean_unbox_usize(v_sz_4354_);
lean_dec(v_sz_4354_);
v_i_boxed_4358_ = lean_unbox_usize(v_i_4355_);
lean_dec(v_i_4355_);
v_res_4359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4353_, v_sz_boxed_4357_, v_i_boxed_4358_, v_b_4356_);
lean_dec_ref(v_b_4356_);
lean_dec_ref(v_as_4353_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4360_, size_t v_sz_4361_, size_t v_i_4362_, lean_object* v_b_4363_){
_start:
{
lean_object* v_a_4365_; uint8_t v___x_4369_; 
v___x_4369_ = lean_usize_dec_lt(v_i_4362_, v_sz_4361_);
if (v___x_4369_ == 0)
{
lean_inc_ref(v_b_4363_);
return v_b_4363_;
}
else
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v_a_4372_; 
v___x_4370_ = lean_box(0);
v___x_4371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4372_ = lean_array_uget(v_as_4360_, v_i_4362_);
if (lean_obj_tag(v_a_4372_) == 1)
{
lean_object* v_i_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4407_; 
v_i_4373_ = lean_ctor_get(v_a_4372_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v_a_4372_);
if (v_isSharedCheck_4407_ == 0)
{
lean_object* v_unused_4408_; 
v_unused_4408_ = lean_ctor_get(v_a_4372_, 1);
lean_dec(v_unused_4408_);
v___x_4375_ = v_a_4372_;
v_isShared_4376_ = v_isSharedCheck_4407_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_i_4373_);
lean_dec(v_a_4372_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4407_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
if (lean_obj_tag(v_i_4373_) == 10)
{
lean_object* v_i_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4406_; 
v_i_4377_ = lean_ctor_get(v_i_4373_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v_i_4373_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4379_ = v_i_4373_;
v_isShared_4380_ = v_isSharedCheck_4406_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_i_4377_);
lean_dec(v_i_4373_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4406_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v_stx_4381_; lean_object* v_value_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4405_; 
v_stx_4381_ = lean_ctor_get(v_i_4377_, 0);
v_value_4382_ = lean_ctor_get(v_i_4377_, 1);
v_isSharedCheck_4405_ = !lean_is_exclusive(v_i_4377_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4384_ = v_i_4377_;
v_isShared_4385_ = v_isSharedCheck_4405_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_value_4382_);
lean_inc(v_stx_4381_);
lean_dec(v_i_4377_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4405_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4387_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4382_, v___x_4386_);
lean_dec(v_value_4382_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_del_object(v___x_4384_);
lean_dec(v_stx_4381_);
lean_del_object(v___x_4379_);
lean_del_object(v___x_4375_);
v_a_4365_ = v___x_4371_;
goto v___jp_4364_;
}
else
{
lean_object* v_val_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4404_; 
v_val_4388_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4390_ = v___x_4387_;
v_isShared_4391_ = v_isSharedCheck_4404_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_val_4388_);
lean_dec(v___x_4387_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4404_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 1, v_val_4388_);
v___x_4393_ = v___x_4384_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_stx_4381_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_val_4388_);
v___x_4393_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4395_; 
if (v_isShared_4391_ == 0)
{
lean_ctor_set(v___x_4390_, 0, v___x_4393_);
v___x_4395_ = v___x_4390_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v___x_4393_);
v___x_4395_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
lean_object* v___x_4397_; 
if (v_isShared_4380_ == 0)
{
lean_ctor_set_tag(v___x_4379_, 1);
lean_ctor_set(v___x_4379_, 0, v___x_4395_);
v___x_4397_ = v___x_4379_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4395_);
v___x_4397_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4399_; 
if (v_isShared_4376_ == 0)
{
lean_ctor_set_tag(v___x_4375_, 0);
lean_ctor_set(v___x_4375_, 1, v___x_4370_);
lean_ctor_set(v___x_4375_, 0, v___x_4397_);
v___x_4399_ = v___x_4375_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4397_);
lean_ctor_set(v_reuseFailAlloc_4400_, 1, v___x_4370_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
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
lean_del_object(v___x_4375_);
lean_dec_ref(v_i_4373_);
v_a_4365_ = v___x_4371_;
goto v___jp_4364_;
}
}
}
else
{
lean_dec(v_a_4372_);
v_a_4365_ = v___x_4371_;
goto v___jp_4364_;
}
}
v___jp_4364_:
{
size_t v___x_4366_; size_t v___x_4367_; lean_object* v___x_4368_; 
v___x_4366_ = ((size_t)1ULL);
v___x_4367_ = lean_usize_add(v_i_4362_, v___x_4366_);
v___x_4368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4360_, v_sz_4361_, v___x_4367_, v_a_4365_);
return v___x_4368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4409_, lean_object* v_sz_4410_, lean_object* v_i_4411_, lean_object* v_b_4412_){
_start:
{
size_t v_sz_boxed_4413_; size_t v_i_boxed_4414_; lean_object* v_res_4415_; 
v_sz_boxed_4413_ = lean_unbox_usize(v_sz_4410_);
lean_dec(v_sz_4410_);
v_i_boxed_4414_ = lean_unbox_usize(v_i_4411_);
lean_dec(v_i_4411_);
v_res_4415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4409_, v_sz_boxed_4413_, v_i_boxed_4414_, v_b_4412_);
lean_dec_ref(v_b_4412_);
lean_dec_ref(v_as_4409_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4416_){
_start:
{
if (lean_obj_tag(v_x_4416_) == 0)
{
lean_object* v_cs_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; size_t v_sz_4420_; size_t v___x_4421_; lean_object* v___x_4422_; lean_object* v_fst_4423_; 
v_cs_4417_ = lean_ctor_get(v_x_4416_, 0);
v___x_4418_ = lean_box(0);
v___x_4419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4420_ = lean_array_size(v_cs_4417_);
v___x_4421_ = ((size_t)0ULL);
v___x_4422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4417_, v_sz_4420_, v___x_4421_, v___x_4419_);
v_fst_4423_ = lean_ctor_get(v___x_4422_, 0);
lean_inc(v_fst_4423_);
lean_dec_ref(v___x_4422_);
if (lean_obj_tag(v_fst_4423_) == 0)
{
return v___x_4418_;
}
else
{
lean_object* v_val_4424_; 
v_val_4424_ = lean_ctor_get(v_fst_4423_, 0);
lean_inc(v_val_4424_);
lean_dec_ref_known(v_fst_4423_, 1);
return v_val_4424_;
}
}
else
{
lean_object* v_vs_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; size_t v_sz_4428_; size_t v___x_4429_; lean_object* v___x_4430_; lean_object* v_fst_4431_; 
v_vs_4425_ = lean_ctor_get(v_x_4416_, 0);
v___x_4426_ = lean_box(0);
v___x_4427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4428_ = lean_array_size(v_vs_4425_);
v___x_4429_ = ((size_t)0ULL);
v___x_4430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4425_, v_sz_4428_, v___x_4429_, v___x_4427_);
v_fst_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc(v_fst_4431_);
lean_dec_ref(v___x_4430_);
if (lean_obj_tag(v_fst_4431_) == 0)
{
return v___x_4426_;
}
else
{
lean_object* v_val_4432_; 
v_val_4432_ = lean_ctor_get(v_fst_4431_, 0);
lean_inc(v_val_4432_);
lean_dec_ref_known(v_fst_4431_, 1);
return v_val_4432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4433_, size_t v_sz_4434_, size_t v_i_4435_, lean_object* v_b_4436_){
_start:
{
uint8_t v___x_4437_; 
v___x_4437_ = lean_usize_dec_lt(v_i_4435_, v_sz_4434_);
if (v___x_4437_ == 0)
{
lean_inc_ref(v_b_4436_);
return v_b_4436_;
}
else
{
lean_object* v___x_4438_; lean_object* v_a_4439_; lean_object* v___x_4440_; 
v___x_4438_ = lean_box(0);
v_a_4439_ = lean_array_uget_borrowed(v_as_4433_, v_i_4435_);
v___x_4440_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4439_);
if (lean_obj_tag(v___x_4440_) == 1)
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
v___x_4442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
lean_ctor_set(v___x_4442_, 1, v___x_4438_);
return v___x_4442_;
}
else
{
lean_object* v___x_4443_; size_t v___x_4444_; size_t v___x_4445_; 
lean_dec(v___x_4440_);
v___x_4443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4444_ = ((size_t)1ULL);
v___x_4445_ = lean_usize_add(v_i_4435_, v___x_4444_);
v_i_4435_ = v___x_4445_;
v_b_4436_ = v___x_4443_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4447_, lean_object* v_sz_4448_, lean_object* v_i_4449_, lean_object* v_b_4450_){
_start:
{
size_t v_sz_boxed_4451_; size_t v_i_boxed_4452_; lean_object* v_res_4453_; 
v_sz_boxed_4451_ = lean_unbox_usize(v_sz_4448_);
lean_dec(v_sz_4448_);
v_i_boxed_4452_ = lean_unbox_usize(v_i_4449_);
lean_dec(v_i_4449_);
v_res_4453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4447_, v_sz_boxed_4451_, v_i_boxed_4452_, v_b_4450_);
lean_dec_ref(v_b_4450_);
lean_dec_ref(v_as_4447_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4454_);
lean_dec_ref(v_x_4454_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4456_){
_start:
{
lean_object* v_root_4457_; lean_object* v_tail_4458_; lean_object* v___x_4459_; 
v_root_4457_ = lean_ctor_get(v_t_4456_, 0);
v_tail_4458_ = lean_ctor_get(v_t_4456_, 1);
v___x_4459_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4457_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v___x_4460_; size_t v_sz_4461_; size_t v___x_4462_; lean_object* v___x_4463_; lean_object* v_fst_4464_; 
v___x_4460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4461_ = lean_array_size(v_tail_4458_);
v___x_4462_ = ((size_t)0ULL);
v___x_4463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4458_, v_sz_4461_, v___x_4462_, v___x_4460_);
v_fst_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_fst_4464_);
lean_dec_ref(v___x_4463_);
if (lean_obj_tag(v_fst_4464_) == 0)
{
return v___x_4459_;
}
else
{
lean_object* v_val_4465_; 
v_val_4465_ = lean_ctor_get(v_fst_4464_, 0);
lean_inc(v_val_4465_);
lean_dec_ref_known(v_fst_4464_, 1);
return v_val_4465_;
}
}
else
{
return v___x_4459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4466_);
lean_dec_ref(v_t_4466_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4482_, lean_object* v_a_4483_){
_start:
{
if (lean_obj_tag(v_node_4482_) == 1)
{
lean_object* v_children_4485_; lean_object* v_res_4486_; 
v_children_4485_ = lean_ctor_get(v_node_4482_, 1);
v_res_4486_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4485_);
if (lean_obj_tag(v_res_4486_) == 1)
{
lean_object* v_val_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4524_; 
v_val_4487_ = lean_ctor_get(v_res_4486_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v_res_4486_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4489_ = v_res_4486_;
v_isShared_4490_ = v_isSharedCheck_4524_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_val_4487_);
lean_dec(v_res_4486_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4524_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v_fst_4491_; lean_object* v_snd_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4523_; 
v_fst_4491_ = lean_ctor_get(v_val_4487_, 0);
v_snd_4492_ = lean_ctor_get(v_val_4487_, 1);
v_isSharedCheck_4523_ = !lean_is_exclusive(v_val_4487_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4494_ = v_val_4487_;
v_isShared_4495_ = v_isSharedCheck_4523_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_snd_4492_);
lean_inc(v_fst_4491_);
lean_dec(v_val_4487_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4523_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4496_; lean_object* v_a_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4522_; 
v___x_4496_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4483_);
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4499_ = v___x_4496_;
v_isShared_4500_ = v_isSharedCheck_4522_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_a_4497_);
lean_dec(v___x_4496_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4522_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; uint8_t v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___y_4509_; lean_object* v___x_4511_; 
v___x_4501_ = lean_box(0);
v___x_4502_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4503_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4504_ = 1;
v___x_4505_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4506_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4507_ = l_Lean_Syntax_getPos_x3f(v_fst_4491_, v___x_4504_);
v___x_4508_ = lean_box(v___x_4504_);
v___y_4509_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4509_, 0, v___x_4507_);
lean_closure_set(v___y_4509_, 1, v_fst_4491_);
lean_closure_set(v___y_4509_, 2, v___x_4508_);
lean_closure_set(v___y_4509_, 3, v_a_4497_);
lean_closure_set(v___y_4509_, 4, v___x_4501_);
lean_closure_set(v___y_4509_, 5, v___x_4502_);
lean_closure_set(v___y_4509_, 6, v___x_4503_);
lean_closure_set(v___y_4509_, 7, v___x_4501_);
lean_closure_set(v___y_4509_, 8, v___x_4505_);
lean_closure_set(v___y_4509_, 9, v___x_4501_);
lean_closure_set(v___y_4509_, 10, v___x_4501_);
lean_closure_set(v___y_4509_, 11, v___x_4501_);
lean_closure_set(v___y_4509_, 12, v_snd_4492_);
lean_closure_set(v___y_4509_, 13, v___x_4506_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 0, v___y_4509_);
v___x_4511_ = v___x_4489_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___y_4509_);
v___x_4511_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
lean_object* v___x_4513_; 
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 1, v___x_4511_);
lean_ctor_set(v___x_4494_, 0, v___x_4506_);
v___x_4513_ = v___x_4494_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4520_, 1, v___x_4511_);
v___x_4513_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4518_; 
v___x_4514_ = lean_unsigned_to_nat(1u);
v___x_4515_ = lean_mk_empty_array_with_capacity(v___x_4514_);
v___x_4516_ = lean_array_push(v___x_4515_, v___x_4513_);
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 0, v___x_4516_);
v___x_4518_ = v___x_4499_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v___x_4516_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
lean_dec(v_res_4486_);
v___x_4525_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
return v___x_4526_;
}
}
else
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4527_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4527_);
return v___x_4528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4529_, v_a_4530_);
lean_dec_ref(v_a_4530_);
lean_dec_ref(v_node_4529_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4533_, lean_object* v_x_4534_, lean_object* v_x_4535_, lean_object* v_node_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4536_, v_a_4537_);
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4540_, lean_object* v_x_4541_, lean_object* v_x_4542_, lean_object* v_node_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4540_, v_x_4541_, v_x_4542_, v_node_4543_, v_a_4544_);
lean_dec_ref(v_a_4544_);
lean_dec_ref(v_node_4543_);
lean_dec_ref(v_x_4542_);
lean_dec_ref(v_x_4541_);
lean_dec_ref(v_x_4540_);
return v_res_4546_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4547_, lean_object* v_inst_4548_, lean_object* v_R_4549_, lean_object* v_a_4550_, uint8_t v_b_4551_, lean_object* v_c_4552_){
_start:
{
uint8_t v___x_4553_; 
v___x_4553_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4547_, v_a_4550_, v_b_4551_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4554_, lean_object* v_inst_4555_, lean_object* v_R_4556_, lean_object* v_a_4557_, lean_object* v_b_4558_, lean_object* v_c_4559_){
_start:
{
uint8_t v_b_boxed_4560_; uint8_t v_res_4561_; lean_object* v_r_4562_; 
v_b_boxed_4560_ = lean_unbox(v_b_4558_);
v_res_4561_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4554_, v_inst_4555_, v_R_4556_, v_a_4557_, v_b_boxed_4560_, v_c_4559_);
lean_dec_ref(v_s_4554_);
v_r_4562_ = lean_box(v_res_4561_);
return v_r_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_(){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4568_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_));
v___x_4569_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4570_ = l_Lean_CodeAction_insertBuiltin(v___x_4568_, v___x_4569_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355____boxed(lean_object* v_a_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_355_();
return v_res_4572_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4574_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4575_ = lean_string_utf8_byte_size(v___x_4574_);
return v___x_4575_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; 
v___x_4576_ = lean_unsigned_to_nat(0u);
v___x_4577_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4578_ = lean_nat_dec_eq(v___x_4577_, v___x_4576_);
return v___x_4578_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4579_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1);
v___x_4580_ = lean_unsigned_to_nat(0u);
v___x_4581_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__0));
v___x_4582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
lean_ctor_set(v___x_4582_, 1, v___x_4580_);
lean_ctor_set(v___x_4582_, 2, v___x_4579_);
return v___x_4582_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4(void){
_start:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4583_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4584_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4583_);
return v___x_4584_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4585_ = lean_unsigned_to_nat(0u);
v___x_4586_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__4);
v___x_4587_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4588_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
lean_ctor_set(v___x_4588_, 1, v___x_4586_);
lean_ctor_set(v___x_4588_, 2, v___x_4585_);
lean_ctor_set(v___x_4588_, 3, v___x_4585_);
return v___x_4588_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4589_){
_start:
{
lean_object* v___y_4591_; uint8_t v___x_4594_; 
v___x_4594_ = lean_uint8_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; 
v___x_4595_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__5);
v___y_4591_ = v___x_4595_;
goto v___jp_4590_;
}
else
{
lean_object* v___x_4596_; 
v___x_4596_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__6));
v___y_4591_ = v___x_4596_;
goto v___jp_4590_;
}
v___jp_4590_:
{
uint8_t v___x_4592_; uint8_t v___x_4593_; 
v___x_4592_ = 0;
lean_inc(v___y_4591_);
v___x_4593_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4589_, v___y_4591_, v___x_4592_);
return v___x_4593_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4597_){
_start:
{
uint8_t v_res_4598_; lean_object* v_r_4599_; 
v_res_4598_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4597_);
lean_dec_ref(v_s_4597_);
v_r_4599_ = lean_box(v_res_4598_);
return v_r_4599_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4600_, lean_object* v_as_x27_4601_, uint8_t v_b_4602_){
_start:
{
if (lean_obj_tag(v_as_x27_4601_) == 0)
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4604_ = lean_box(v_b_4602_);
v___x_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4604_);
return v___x_4605_;
}
else
{
lean_object* v_head_4606_; uint8_t v_isSilent_4607_; 
v_head_4606_ = lean_ctor_get(v_as_x27_4601_, 0);
v_isSilent_4607_ = lean_ctor_get_uint8(v_head_4606_, sizeof(void*)*5 + 2);
if (v_isSilent_4607_ == 0)
{
lean_object* v_tail_4608_; lean_object* v_data_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; uint8_t v___x_4614_; 
v_tail_4608_ = lean_ctor_get(v_as_x27_4601_, 1);
v_data_4609_ = lean_ctor_get(v_head_4606_, 4);
lean_inc(v_data_4609_);
v___x_4610_ = l_Lean_MessageData_toString(v_data_4609_);
v___x_4611_ = lean_unsigned_to_nat(0u);
v___x_4612_ = lean_string_utf8_byte_size(v___x_4610_);
v___x_4613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4610_);
lean_ctor_set(v___x_4613_, 1, v___x_4611_);
lean_ctor_set(v___x_4613_, 2, v___x_4612_);
v___x_4614_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4613_);
lean_dec_ref_known(v___x_4613_, 3);
if (v___x_4614_ == 0)
{
v_as_x27_4601_ = v_tail_4608_;
goto _start;
}
else
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = lean_box(v_foundPanic_4600_);
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
return v___x_4617_;
}
}
else
{
lean_object* v_tail_4618_; 
v_tail_4618_ = lean_ctor_get(v_as_x27_4601_, 1);
v_as_x27_4601_ = v_tail_4618_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4620_, lean_object* v_as_x27_4621_, lean_object* v_b_4622_, lean_object* v___y_4623_){
_start:
{
uint8_t v_foundPanic_boxed_4624_; uint8_t v_b_boxed_4625_; lean_object* v_res_4626_; 
v_foundPanic_boxed_4624_ = lean_unbox(v_foundPanic_4620_);
v_b_boxed_4625_ = lean_unbox(v_b_4622_);
v_res_4626_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4624_, v_as_x27_4621_, v_b_boxed_4625_);
lean_dec(v_as_x27_4621_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4627_, uint8_t v_severity_4628_, uint8_t v_isSilent_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_){
_start:
{
lean_object* v___x_4633_; 
v___x_4633_ = l_Lean_Elab_Command_getRef___redArg(v___y_4630_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4635_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
lean_inc(v_a_4634_);
lean_dec_ref_known(v___x_4633_, 1);
v___x_4635_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4634_, v_msgData_4627_, v_severity_4628_, v_isSilent_4629_, v___y_4630_, v___y_4631_);
lean_dec(v_a_4634_);
return v___x_4635_;
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec_ref(v_msgData_4627_);
v_a_4636_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4633_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4633_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4644_, lean_object* v_severity_4645_, lean_object* v_isSilent_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
uint8_t v_severity_boxed_4650_; uint8_t v_isSilent_boxed_4651_; lean_object* v_res_4652_; 
v_severity_boxed_4650_ = lean_unbox(v_severity_4645_);
v_isSilent_boxed_4651_ = lean_unbox(v_isSilent_4646_);
v_res_4652_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4644_, v_severity_boxed_4650_, v_isSilent_boxed_4651_, v___y_4647_, v___y_4648_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
uint8_t v___x_4657_; uint8_t v___x_4658_; lean_object* v___x_4659_; 
v___x_4657_ = 2;
v___x_4658_ = 0;
v___x_4659_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4653_, v___x_4657_, v___x_4658_, v___y_4654_, v___y_4655_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4660_, v___y_4661_, v___y_4662_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
return v_res_4664_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4672_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4673_ = l_Lean_MessageData_ofFormat(v___x_4672_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_){
_start:
{
lean_object* v___x_4678_; uint8_t v_foundPanic_4679_; 
v___x_4678_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4674_);
v_foundPanic_4679_ = l_Lean_Syntax_isOfKind(v_x_4674_, v___x_4678_);
if (v_foundPanic_4679_ == 0)
{
lean_object* v___x_4680_; 
lean_dec(v_x_4674_);
v___x_4680_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4680_;
}
else
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4681_ = lean_unsigned_to_nat(2u);
v___x_4682_ = l_Lean_Syntax_getArg(v_x_4674_, v___x_4681_);
lean_dec(v_x_4674_);
v___x_4683_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4682_, v_a_4675_, v_a_4676_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_object* v_a_4684_; uint8_t v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4744_; 
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc(v_a_4684_);
lean_dec_ref_known(v___x_4683_, 1);
v___x_4685_ = 0;
v___x_4686_ = l_Lean_MessageLog_toList(v_a_4684_);
v___x_4687_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4679_, v___x_4686_, v___x_4685_);
lean_dec(v___x_4686_);
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4690_ = v___x_4687_;
v_isShared_4691_ = v_isSharedCheck_4744_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4687_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4744_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
uint8_t v___x_4692_; 
v___x_4692_ = lean_unbox(v_a_4688_);
lean_dec(v_a_4688_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4693_; lean_object* v_env_4694_; lean_object* v_scopes_4695_; lean_object* v_usedQuotCtxts_4696_; lean_object* v_nextMacroScope_4697_; lean_object* v_maxRecDepth_4698_; lean_object* v_ngen_4699_; lean_object* v_auxDeclNGen_4700_; lean_object* v_infoState_4701_; lean_object* v_traceState_4702_; lean_object* v_snapshotTasks_4703_; lean_object* v_prevLinterStates_4704_; lean_object* v_codeQualityEntryTasks_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4715_; 
lean_del_object(v___x_4690_);
v___x_4693_ = lean_st_ref_take(v_a_4676_);
v_env_4694_ = lean_ctor_get(v___x_4693_, 0);
v_scopes_4695_ = lean_ctor_get(v___x_4693_, 2);
v_usedQuotCtxts_4696_ = lean_ctor_get(v___x_4693_, 3);
v_nextMacroScope_4697_ = lean_ctor_get(v___x_4693_, 4);
v_maxRecDepth_4698_ = lean_ctor_get(v___x_4693_, 5);
v_ngen_4699_ = lean_ctor_get(v___x_4693_, 6);
v_auxDeclNGen_4700_ = lean_ctor_get(v___x_4693_, 7);
v_infoState_4701_ = lean_ctor_get(v___x_4693_, 8);
v_traceState_4702_ = lean_ctor_get(v___x_4693_, 9);
v_snapshotTasks_4703_ = lean_ctor_get(v___x_4693_, 10);
v_prevLinterStates_4704_ = lean_ctor_get(v___x_4693_, 11);
v_codeQualityEntryTasks_4705_ = lean_ctor_get(v___x_4693_, 12);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4693_);
if (v_isSharedCheck_4715_ == 0)
{
lean_object* v_unused_4716_; 
v_unused_4716_ = lean_ctor_get(v___x_4693_, 1);
lean_dec(v_unused_4716_);
v___x_4707_ = v___x_4693_;
v_isShared_4708_ = v_isSharedCheck_4715_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4705_);
lean_inc(v_prevLinterStates_4704_);
lean_inc(v_snapshotTasks_4703_);
lean_inc(v_traceState_4702_);
lean_inc(v_infoState_4701_);
lean_inc(v_auxDeclNGen_4700_);
lean_inc(v_ngen_4699_);
lean_inc(v_maxRecDepth_4698_);
lean_inc(v_nextMacroScope_4697_);
lean_inc(v_usedQuotCtxts_4696_);
lean_inc(v_scopes_4695_);
lean_inc(v_env_4694_);
lean_dec(v___x_4693_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4715_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 1, v_a_4684_);
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_env_4694_);
lean_ctor_set(v_reuseFailAlloc_4714_, 1, v_a_4684_);
lean_ctor_set(v_reuseFailAlloc_4714_, 2, v_scopes_4695_);
lean_ctor_set(v_reuseFailAlloc_4714_, 3, v_usedQuotCtxts_4696_);
lean_ctor_set(v_reuseFailAlloc_4714_, 4, v_nextMacroScope_4697_);
lean_ctor_set(v_reuseFailAlloc_4714_, 5, v_maxRecDepth_4698_);
lean_ctor_set(v_reuseFailAlloc_4714_, 6, v_ngen_4699_);
lean_ctor_set(v_reuseFailAlloc_4714_, 7, v_auxDeclNGen_4700_);
lean_ctor_set(v_reuseFailAlloc_4714_, 8, v_infoState_4701_);
lean_ctor_set(v_reuseFailAlloc_4714_, 9, v_traceState_4702_);
lean_ctor_set(v_reuseFailAlloc_4714_, 10, v_snapshotTasks_4703_);
lean_ctor_set(v_reuseFailAlloc_4714_, 11, v_prevLinterStates_4704_);
lean_ctor_set(v_reuseFailAlloc_4714_, 12, v_codeQualityEntryTasks_4705_);
v___x_4710_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4711_ = lean_st_ref_put(v_a_4676_, v___x_4710_);
v___x_4712_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4713_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4712_, v_a_4675_, v_a_4676_);
return v___x_4713_;
}
}
}
else
{
lean_object* v___x_4717_; lean_object* v_env_4718_; lean_object* v_scopes_4719_; lean_object* v_usedQuotCtxts_4720_; lean_object* v_nextMacroScope_4721_; lean_object* v_maxRecDepth_4722_; lean_object* v_ngen_4723_; lean_object* v_auxDeclNGen_4724_; lean_object* v_infoState_4725_; lean_object* v_traceState_4726_; lean_object* v_snapshotTasks_4727_; lean_object* v_prevLinterStates_4728_; lean_object* v_codeQualityEntryTasks_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4742_; 
lean_dec(v_a_4684_);
v___x_4717_ = lean_st_ref_take(v_a_4676_);
v_env_4718_ = lean_ctor_get(v___x_4717_, 0);
v_scopes_4719_ = lean_ctor_get(v___x_4717_, 2);
v_usedQuotCtxts_4720_ = lean_ctor_get(v___x_4717_, 3);
v_nextMacroScope_4721_ = lean_ctor_get(v___x_4717_, 4);
v_maxRecDepth_4722_ = lean_ctor_get(v___x_4717_, 5);
v_ngen_4723_ = lean_ctor_get(v___x_4717_, 6);
v_auxDeclNGen_4724_ = lean_ctor_get(v___x_4717_, 7);
v_infoState_4725_ = lean_ctor_get(v___x_4717_, 8);
v_traceState_4726_ = lean_ctor_get(v___x_4717_, 9);
v_snapshotTasks_4727_ = lean_ctor_get(v___x_4717_, 10);
v_prevLinterStates_4728_ = lean_ctor_get(v___x_4717_, 11);
v_codeQualityEntryTasks_4729_ = lean_ctor_get(v___x_4717_, 12);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4717_);
if (v_isSharedCheck_4742_ == 0)
{
lean_object* v_unused_4743_; 
v_unused_4743_ = lean_ctor_get(v___x_4717_, 1);
lean_dec(v_unused_4743_);
v___x_4731_ = v___x_4717_;
v_isShared_4732_ = v_isSharedCheck_4742_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4729_);
lean_inc(v_prevLinterStates_4728_);
lean_inc(v_snapshotTasks_4727_);
lean_inc(v_traceState_4726_);
lean_inc(v_infoState_4725_);
lean_inc(v_auxDeclNGen_4724_);
lean_inc(v_ngen_4723_);
lean_inc(v_maxRecDepth_4722_);
lean_inc(v_nextMacroScope_4721_);
lean_inc(v_usedQuotCtxts_4720_);
lean_inc(v_scopes_4719_);
lean_inc(v_env_4718_);
lean_dec(v___x_4717_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4742_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4733_; lean_object* v___x_4735_; 
v___x_4733_ = l_Lean_MessageLog_empty;
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 1, v___x_4733_);
v___x_4735_ = v___x_4731_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_env_4718_);
lean_ctor_set(v_reuseFailAlloc_4741_, 1, v___x_4733_);
lean_ctor_set(v_reuseFailAlloc_4741_, 2, v_scopes_4719_);
lean_ctor_set(v_reuseFailAlloc_4741_, 3, v_usedQuotCtxts_4720_);
lean_ctor_set(v_reuseFailAlloc_4741_, 4, v_nextMacroScope_4721_);
lean_ctor_set(v_reuseFailAlloc_4741_, 5, v_maxRecDepth_4722_);
lean_ctor_set(v_reuseFailAlloc_4741_, 6, v_ngen_4723_);
lean_ctor_set(v_reuseFailAlloc_4741_, 7, v_auxDeclNGen_4724_);
lean_ctor_set(v_reuseFailAlloc_4741_, 8, v_infoState_4725_);
lean_ctor_set(v_reuseFailAlloc_4741_, 9, v_traceState_4726_);
lean_ctor_set(v_reuseFailAlloc_4741_, 10, v_snapshotTasks_4727_);
lean_ctor_set(v_reuseFailAlloc_4741_, 11, v_prevLinterStates_4728_);
lean_ctor_set(v_reuseFailAlloc_4741_, 12, v_codeQualityEntryTasks_4729_);
v___x_4735_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4739_; 
v___x_4736_ = lean_st_ref_put(v_a_4676_, v___x_4735_);
v___x_4737_ = lean_box(0);
if (v_isShared_4691_ == 0)
{
lean_ctor_set(v___x_4690_, 0, v___x_4737_);
v___x_4739_ = v___x_4690_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v___x_4737_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
}
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
v_a_4745_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4683_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4683_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4753_, v_a_4754_, v_a_4755_);
lean_dec(v_a_4755_);
lean_dec_ref(v_a_4754_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4758_, lean_object* v_as_4759_, lean_object* v_as_x27_4760_, uint8_t v_b_4761_, lean_object* v_a_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v___x_4766_; 
v___x_4766_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4758_, v_as_x27_4760_, v_b_4761_);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4767_, lean_object* v_as_4768_, lean_object* v_as_x27_4769_, lean_object* v_b_4770_, lean_object* v_a_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
uint8_t v_foundPanic_boxed_4775_; uint8_t v_b_boxed_4776_; lean_object* v_res_4777_; 
v_foundPanic_boxed_4775_ = lean_unbox(v_foundPanic_4767_);
v_b_boxed_4776_ = lean_unbox(v_b_4770_);
v_res_4777_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4775_, v_as_4768_, v_as_x27_4769_, v_b_boxed_4776_, v_a_4771_, v___y_4772_, v___y_4773_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
lean_dec(v_as_x27_4769_);
lean_dec(v_as_4768_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
v___x_4786_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4787_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4788_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4789_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4790_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4786_, v___x_4787_, v___x_4788_, v___x_4789_);
return v___x_4790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4792_;
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
