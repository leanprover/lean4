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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__2_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__4_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__6_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_55_ = l_Lean_Option_register___at___00__private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__spec__0(v___x_52_, v___x_53_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_56_;
v_res_56_ = l___private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_();
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Elab_GuardMsgs_0__Lean_initFn_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(lean_object* v_line_61_, lean_object* v_pos_62_){
_start:
{
lean_object* v_line_63_; lean_object* v_column_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_line_63_ = lean_ctor_get(v_pos_62_, 0);
lean_inc(v_line_63_);
v_column_64_ = lean_ctor_get(v_pos_62_, 1);
lean_inc(v_column_64_);
lean_dec_ref(v_pos_62_);
v___x_65_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__0));
v___x_66_ = lean_nat_sub(v_line_63_, v_line_61_);
lean_dec(v_line_63_);
v___x_67_ = l_Nat_reprFast(v___x_66_);
v___x_68_ = lean_string_append(v___x_65_, v___x_67_);
lean_dec_ref(v___x_67_);
v___x_69_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___closed__1));
v___x_70_ = lean_string_append(v___x_68_, v___x_69_);
v___x_71_ = l_Nat_reprFast(v_column_64_);
v___x_72_ = lean_string_append(v___x_70_, v___x_71_);
lean_dec_ref(v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0___boxed(lean_object* v_line_73_, lean_object* v_pos_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v_line_73_, v_pos_74_);
lean_dec(v_line_73_);
return v_res_75_;
}
}
lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(lean_object* v_msg_87_, lean_object* v_reportPos_x3f_88_){
_start:
{
lean_object* v___y_91_; lean_object* v___y_95_; uint32_t v___y_96_; lean_object* v___y_100_; lean_object* v_str_103_; lean_object* v_pos_113_; lean_object* v_endPos_114_; uint8_t v_severity_115_; lean_object* v_caption_116_; lean_object* v_data_117_; lean_object* v___y_119_; lean_object* v___y_120_; lean_object* v___y_121_; lean_object* v_str_132_; lean_object* v_str_144_; lean_object* v___y_155_; lean_object* v_str_159_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_pos_113_ = lean_ctor_get(v_msg_87_, 1);
lean_inc_ref(v_pos_113_);
v_endPos_114_ = lean_ctor_get(v_msg_87_, 2);
lean_inc(v_endPos_114_);
v_severity_115_ = lean_ctor_get_uint8(v_msg_87_, sizeof(void*)*5 + 1);
v_caption_116_ = lean_ctor_get(v_msg_87_, 3);
v_data_117_ = lean_ctor_get(v_msg_87_, 4);
lean_inc(v_data_117_);
v___x_166_ = l_Lean_MessageData_toString(v_data_117_);
v___x_167_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_168_ = lean_string_dec_eq(v_caption_116_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__10));
lean_inc_ref(v_caption_116_);
v___x_170_ = lean_string_append(v_caption_116_, v___x_169_);
v___x_171_ = lean_string_append(v___x_170_, v___x_166_);
lean_dec_ref(v___x_166_);
v_str_159_ = v___x_171_;
goto v___jp_158_;
}
else
{
v_str_159_ = v___x_166_;
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
uint32_t v___x_101_; 
v___x_101_ = 65;
v___y_95_ = v___y_100_;
v___y_96_ = v___x_101_;
goto v___jp_94_;
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_104_ = lean_string_utf8_byte_size(v_str_103_);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_nat_dec_eq(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_inc_ref(v_str_103_);
v___x_107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_107_, 0, v_str_103_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_104_);
v___x_108_ = l_String_Slice_Pos_prev_x3f(v___x_107_, v___x_104_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_dec_ref_known(v___x_107_, 3);
v___y_100_ = v_str_103_;
goto v___jp_99_;
}
else
{
lean_object* v_val_109_; lean_object* v___x_110_; 
v_val_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_val_109_);
lean_dec_ref_known(v___x_108_, 1);
v___x_110_ = l_String_Slice_Pos_get_x3f(v___x_107_, v_val_109_);
lean_dec(v_val_109_);
lean_dec_ref_known(v___x_107_, 3);
if (lean_obj_tag(v___x_110_) == 0)
{
v___y_100_ = v_str_103_;
goto v___jp_99_;
}
else
{
lean_object* v_val_111_; uint32_t v___x_112_; 
v_val_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_val_111_);
lean_dec_ref_known(v___x_110_, 1);
v___x_112_ = lean_unbox_uint32(v_val_111_);
lean_dec(v_val_111_);
v___y_95_ = v_str_103_;
v___y_96_ = v___x_112_;
goto v___jp_94_;
}
}
}
else
{
v___y_91_ = v_str_103_;
goto v___jp_90_;
}
}
v___jp_118_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_122_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__1));
v___x_123_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v___y_119_, v_pos_113_);
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
lean_dec_ref(v___x_123_);
v___x_125_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2));
v___x_126_ = lean_string_append(v___x_124_, v___x_125_);
v___x_127_ = lean_string_append(v___x_126_, v___y_121_);
lean_dec_ref(v___y_121_);
v___x_128_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_129_ = lean_string_append(v___x_127_, v___x_128_);
v___x_130_ = lean_string_append(v___x_129_, v___y_120_);
lean_dec_ref(v___y_120_);
v_str_103_ = v___x_130_;
goto v___jp_102_;
}
v___jp_131_:
{
if (lean_obj_tag(v_reportPos_x3f_88_) == 1)
{
if (lean_obj_tag(v_endPos_114_) == 0)
{
lean_object* v_val_133_; lean_object* v___x_134_; 
v_val_133_ = lean_ctor_get(v_reportPos_x3f_88_, 0);
v___x_134_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__3));
v___y_119_ = v_val_133_;
v___y_120_ = v_str_132_;
v___y_121_ = v___x_134_;
goto v___jp_118_;
}
else
{
lean_object* v_val_135_; lean_object* v_val_136_; lean_object* v_line_137_; lean_object* v_column_138_; lean_object* v_line_139_; uint8_t v___x_140_; 
v_val_135_ = lean_ctor_get(v_endPos_114_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v_endPos_114_, 1);
v_val_136_ = lean_ctor_get(v_reportPos_x3f_88_, 0);
v_line_137_ = lean_ctor_get(v_val_135_, 0);
v_column_138_ = lean_ctor_get(v_val_135_, 1);
v_line_139_ = lean_ctor_get(v_pos_113_, 0);
v___x_140_ = lean_nat_dec_eq(v_line_137_, v_line_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v_val_136_, v_val_135_);
v___y_119_ = v_val_136_;
v___y_120_ = v_str_132_;
v___y_121_ = v___x_141_;
goto v___jp_118_;
}
else
{
lean_object* v___x_142_; 
lean_inc(v_column_138_);
lean_dec(v_val_135_);
v___x_142_ = l_Nat_reprFast(v_column_138_);
v___y_119_ = v_val_136_;
v___y_120_ = v_str_132_;
v___y_121_ = v___x_142_;
goto v___jp_118_;
}
}
}
else
{
lean_dec(v_endPos_114_);
lean_dec_ref(v_pos_113_);
v_str_103_ = v_str_132_;
goto v___jp_102_;
}
}
v___jp_143_:
{
uint8_t v___x_145_; 
v___x_145_ = l_Lean_Message_isTrace(v_msg_87_);
lean_dec_ref(v_msg_87_);
if (v___x_145_ == 0)
{
switch(v_severity_115_)
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
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = lean_string_utf8_byte_size(v_str_159_);
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_dec_le(v___x_161_, v___x_160_);
if (v___x_162_ == 0)
{
v___y_155_ = v_str_159_;
goto v___jp_154_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_string_memcmp(v_str_159_, v___x_163_, v___x_164_, v___x_164_, v___x_161_);
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
LEAN_EXPORT void l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_87_ = stack[0].m_obj;
lean_object* v_reportPos_x3f_88_ = stack[1].m_obj;
lean_object* v_res_172_;
v_res_172_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_msg_87_, v_reportPos_x3f_88_);
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___boxed(lean_object* v_msg_173_, lean_object* v_reportPos_x3f_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_msg_173_, v_reportPos_x3f_174_);
lean_dec(v_reportPos_x3f_174_);
return v_res_176_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___impl(uint8_t v_x_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_box(v_x_177_);
v___x_179_ = lean_obj_tag_nat(v___x_178_);
lean_dec(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_177_ = stack[0].m_num;
lean_object* v_res_180_;
v_res_180_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___impl(v_x_177_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___impl___boxed(lean_object* v_x_181_){
_start:
{
uint8_t v_x_4__boxed_182_; lean_object* v_res_183_; 
v_x_4__boxed_182_ = lean_unbox(v_x_181_);
v_res_183_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___impl(v_x_4__boxed_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(lean_object* v_k_184_){
_start:
{
lean_inc(v_k_184_);
return v_k_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg___boxed(lean_object* v_k_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(v_k_185_);
lean_dec(v_k_185_);
return v_res_186_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, uint8_t v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_inc(v_k_191_);
return v_k_191_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_188_ = stack[1].m_obj;
uint8_t v_t_189_ = stack[2].m_num;
lean_object* v_k_191_ = stack[4].m_obj;
lean_object* v_res_192_;
v_res_192_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(lean_box(0), v_ctorIdx_188_, v_t_189_, lean_box(0), v_k_191_);
stack->m_obj
 = v_res_192_;
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
lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(lean_object* v_motive_203_, uint8_t v_t_204_, lean_object* v_h_205_, lean_object* v_check_206_){
_start:
{
lean_inc(v_check_206_);
return v_check_206_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_204_ = stack[1].m_num;
lean_object* v_check_206_ = stack[3].m_obj;
lean_object* v_res_207_;
v_res_207_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(lean_box(0), v_t_204_, lean_box(0), v_check_206_);
stack->m_obj
 = v_res_207_;
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
lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(lean_object* v_motive_217_, uint8_t v_t_218_, lean_object* v_h_219_, lean_object* v_drop_220_){
_start:
{
lean_inc(v_drop_220_);
return v_drop_220_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_218_ = stack[1].m_num;
lean_object* v_drop_220_ = stack[3].m_obj;
lean_object* v_res_221_;
v_res_221_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(lean_box(0), v_t_218_, lean_box(0), v_drop_220_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___boxed(lean_object* v_motive_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_drop_225_){
_start:
{
uint8_t v_t_boxed_226_; lean_object* v_res_227_; 
v_t_boxed_226_ = lean_unbox(v_t_223_);
v_res_227_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(v_motive_222_, v_t_boxed_226_, v_h_224_, v_drop_225_);
lean_dec(v_drop_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(lean_object* v_pass_228_){
_start:
{
lean_inc(v_pass_228_);
return v_pass_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg___boxed(lean_object* v_pass_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(v_pass_229_);
lean_dec(v_pass_229_);
return v_res_230_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(lean_object* v_motive_231_, uint8_t v_t_232_, lean_object* v_h_233_, lean_object* v_pass_234_){
_start:
{
lean_inc(v_pass_234_);
return v_pass_234_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_232_ = stack[1].m_num;
lean_object* v_pass_234_ = stack[3].m_obj;
lean_object* v_res_235_;
v_res_235_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(lean_box(0), v_t_232_, lean_box(0), v_pass_234_);
stack->m_obj
 = v_res_235_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___boxed(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_pass_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(v_motive_236_, v_t_boxed_240_, v_h_238_, v_pass_239_);
lean_dec(v_pass_239_);
return v_res_241_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___impl(uint8_t v_x_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_box(v_x_242_);
v___x_244_ = lean_obj_tag_nat(v___x_243_);
lean_dec(v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_242_ = stack[0].m_num;
lean_object* v_res_245_;
v_res_245_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___impl(v_x_242_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___impl___boxed(lean_object* v_x_246_){
_start:
{
uint8_t v_x_4__boxed_247_; lean_object* v_res_248_; 
v_x_4__boxed_247_ = lean_unbox(v_x_246_);
v_res_248_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___impl(v_x_4__boxed_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(lean_object* v_k_249_){
_start:
{
lean_inc(v_k_249_);
return v_k_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg___boxed(lean_object* v_k_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(v_k_250_);
lean_dec(v_k_250_);
return v_res_251_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(lean_object* v_motive_252_, lean_object* v_ctorIdx_253_, uint8_t v_t_254_, lean_object* v_h_255_, lean_object* v_k_256_){
_start:
{
lean_inc(v_k_256_);
return v_k_256_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_253_ = stack[1].m_obj;
uint8_t v_t_254_ = stack[2].m_num;
lean_object* v_k_256_ = stack[4].m_obj;
lean_object* v_res_257_;
v_res_257_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(lean_box(0), v_ctorIdx_253_, v_t_254_, lean_box(0), v_k_256_);
stack->m_obj
 = v_res_257_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___boxed(lean_object* v_motive_258_, lean_object* v_ctorIdx_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_k_262_){
_start:
{
uint8_t v_t_boxed_263_; lean_object* v_res_264_; 
v_t_boxed_263_ = lean_unbox(v_t_260_);
v_res_264_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(v_motive_258_, v_ctorIdx_259_, v_t_boxed_263_, v_h_261_, v_k_262_);
lean_dec(v_k_262_);
lean_dec(v_ctorIdx_259_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(lean_object* v_exact_265_){
_start:
{
lean_inc(v_exact_265_);
return v_exact_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg___boxed(lean_object* v_exact_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(v_exact_266_);
lean_dec(v_exact_266_);
return v_res_267_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(lean_object* v_motive_268_, uint8_t v_t_269_, lean_object* v_h_270_, lean_object* v_exact_271_){
_start:
{
lean_inc(v_exact_271_);
return v_exact_271_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_269_ = stack[1].m_num;
lean_object* v_exact_271_ = stack[3].m_obj;
lean_object* v_res_272_;
v_res_272_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(lean_box(0), v_t_269_, lean_box(0), v_exact_271_);
stack->m_obj
 = v_res_272_;
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
lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(lean_object* v_motive_282_, uint8_t v_t_283_, lean_object* v_h_284_, lean_object* v_normalized_285_){
_start:
{
lean_inc(v_normalized_285_);
return v_normalized_285_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_283_ = stack[1].m_num;
lean_object* v_normalized_285_ = stack[3].m_obj;
lean_object* v_res_286_;
v_res_286_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(lean_box(0), v_t_283_, lean_box(0), v_normalized_285_);
stack->m_obj
 = v_res_286_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___boxed(lean_object* v_motive_287_, lean_object* v_t_288_, lean_object* v_h_289_, lean_object* v_normalized_290_){
_start:
{
uint8_t v_t_boxed_291_; lean_object* v_res_292_; 
v_t_boxed_291_ = lean_unbox(v_t_288_);
v_res_292_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(v_motive_287_, v_t_boxed_291_, v_h_289_, v_normalized_290_);
lean_dec(v_normalized_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(lean_object* v_lax_293_){
_start:
{
lean_inc(v_lax_293_);
return v_lax_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg___boxed(lean_object* v_lax_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(v_lax_294_);
lean_dec(v_lax_294_);
return v_res_295_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(lean_object* v_motive_296_, uint8_t v_t_297_, lean_object* v_h_298_, lean_object* v_lax_299_){
_start:
{
lean_inc(v_lax_299_);
return v_lax_299_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_297_ = stack[1].m_num;
lean_object* v_lax_299_ = stack[3].m_obj;
lean_object* v_res_300_;
v_res_300_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(lean_box(0), v_t_297_, lean_box(0), v_lax_299_);
stack->m_obj
 = v_res_300_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___boxed(lean_object* v_motive_301_, lean_object* v_t_302_, lean_object* v_h_303_, lean_object* v_lax_304_){
_start:
{
uint8_t v_t_boxed_305_; lean_object* v_res_306_; 
v_t_boxed_305_ = lean_unbox(v_t_302_);
v_res_306_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(v_motive_301_, v_t_boxed_305_, v_h_303_, v_lax_304_);
lean_dec(v_lax_304_);
return v_res_306_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___impl(uint8_t v_x_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_box(v_x_307_);
v___x_309_ = lean_obj_tag_nat(v___x_308_);
lean_dec(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_307_ = stack[0].m_num;
lean_object* v_res_310_;
v_res_310_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___impl(v_x_307_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___impl___boxed(lean_object* v_x_311_){
_start:
{
uint8_t v_x_4__boxed_312_; lean_object* v_res_313_; 
v_x_4__boxed_312_ = lean_unbox(v_x_311_);
v_res_313_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___impl(v_x_4__boxed_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(lean_object* v_k_314_){
_start:
{
lean_inc(v_k_314_);
return v_k_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg___boxed(lean_object* v_k_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(v_k_315_);
lean_dec(v_k_315_);
return v_res_316_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(lean_object* v_motive_317_, lean_object* v_ctorIdx_318_, uint8_t v_t_319_, lean_object* v_h_320_, lean_object* v_k_321_){
_start:
{
lean_inc(v_k_321_);
return v_k_321_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_318_ = stack[1].m_obj;
uint8_t v_t_319_ = stack[2].m_num;
lean_object* v_k_321_ = stack[4].m_obj;
lean_object* v_res_322_;
v_res_322_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(lean_box(0), v_ctorIdx_318_, v_t_319_, lean_box(0), v_k_321_);
stack->m_obj
 = v_res_322_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___boxed(lean_object* v_motive_323_, lean_object* v_ctorIdx_324_, lean_object* v_t_325_, lean_object* v_h_326_, lean_object* v_k_327_){
_start:
{
uint8_t v_t_boxed_328_; lean_object* v_res_329_; 
v_t_boxed_328_ = lean_unbox(v_t_325_);
v_res_329_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(v_motive_323_, v_ctorIdx_324_, v_t_boxed_328_, v_h_326_, v_k_327_);
lean_dec(v_k_327_);
lean_dec(v_ctorIdx_324_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(lean_object* v_exact_330_){
_start:
{
lean_inc(v_exact_330_);
return v_exact_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg___boxed(lean_object* v_exact_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(v_exact_331_);
lean_dec(v_exact_331_);
return v_res_332_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(lean_object* v_motive_333_, uint8_t v_t_334_, lean_object* v_h_335_, lean_object* v_exact_336_){
_start:
{
lean_inc(v_exact_336_);
return v_exact_336_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_334_ = stack[1].m_num;
lean_object* v_exact_336_ = stack[3].m_obj;
lean_object* v_res_337_;
v_res_337_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(lean_box(0), v_t_334_, lean_box(0), v_exact_336_);
stack->m_obj
 = v_res_337_;
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
lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(lean_object* v_motive_347_, uint8_t v_t_348_, lean_object* v_h_349_, lean_object* v_sorted_350_){
_start:
{
lean_inc(v_sorted_350_);
return v_sorted_350_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_348_ = stack[1].m_num;
lean_object* v_sorted_350_ = stack[3].m_obj;
lean_object* v_res_351_;
v_res_351_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(lean_box(0), v_t_348_, lean_box(0), v_sorted_350_);
stack->m_obj
 = v_res_351_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___boxed(lean_object* v_motive_352_, lean_object* v_t_353_, lean_object* v_h_354_, lean_object* v_sorted_355_){
_start:
{
uint8_t v_t_boxed_356_; lean_object* v_res_357_; 
v_t_boxed_356_ = lean_unbox(v_t_353_);
v_res_357_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(v_motive_352_, v_t_boxed_356_, v_h_354_, v_sorted_355_);
lean_dec(v_sorted_355_);
return v_res_357_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_box(0);
v___x_359_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_358_);
return v___x_360_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg(){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_364_;
v_res_364_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___boxed(lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v_res_366_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(lean_object* v_00_u03b1_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_371_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_368_ = stack[1].m_obj;
lean_object* v___y_369_ = stack[2].m_obj;
lean_object* v_res_372_;
v_res_372_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(lean_box(0), v___y_368_, v___y_369_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___boxed(lean_object* v_00_u03b1_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(v_00_u03b1_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_377_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(lean_object* v_action_x3f_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
if (lean_obj_tag(v_action_x3f_395_) == 1)
{
lean_object* v_val_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_430_; 
v_val_399_ = lean_ctor_get(v_action_x3f_395_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v_action_x3f_395_);
if (v_isSharedCheck_430_ == 0)
{
v___x_401_ = v_action_x3f_395_;
v_isShared_402_ = v_isSharedCheck_430_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_val_399_);
lean_dec(v_action_x3f_395_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_430_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1));
lean_inc(v_val_399_);
v___x_404_ = l_Lean_Syntax_isOfKind(v_val_399_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_del_object(v___x_401_);
lean_dec(v_val_399_);
v___x_405_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_405_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = l_Lean_Syntax_getArg(v_val_399_, v___x_406_);
lean_dec(v_val_399_);
v___x_408_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4));
lean_inc(v___x_407_);
v___x_409_ = l_Lean_Syntax_isOfKind(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6));
lean_inc(v___x_407_);
v___x_411_ = l_Lean_Syntax_isOfKind(v___x_407_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8));
v___x_413_ = l_Lean_Syntax_isOfKind(v___x_407_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
lean_del_object(v___x_401_);
v___x_414_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_414_;
}
else
{
uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_415_ = 2;
v___x_416_ = lean_box(v___x_415_);
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 0);
lean_ctor_set(v___x_401_, 0, v___x_416_);
v___x_418_ = v___x_401_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
else
{
uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
lean_dec(v___x_407_);
v___x_420_ = 1;
v___x_421_ = lean_box(v___x_420_);
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 0);
lean_ctor_set(v___x_401_, 0, v___x_421_);
v___x_423_ = v___x_401_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
lean_dec(v___x_407_);
v___x_425_ = 0;
v___x_426_ = lean_box(v___x_425_);
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 0);
lean_ctor_set(v___x_401_, 0, v___x_426_);
v___x_428_ = v___x_401_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
else
{
uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec(v_action_x3f_395_);
v___x_431_ = 0;
v___x_432_ = lean_box(v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_0interp(lean_interpreter_value* stack)
{
lean_object* v_action_x3f_395_ = stack[0].m_obj;
lean_object* v_a_396_ = stack[1].m_obj;
lean_object* v_a_397_ = stack[2].m_obj;
lean_object* v_res_434_;
v_res_434_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_395_, v_a_396_, v_a_397_);
stack->m_obj
 = v_res_434_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___boxed(lean_object* v_action_x3f_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_439_;
}
}
uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(uint8_t v___x_440_, lean_object* v_x_441_){
_start:
{
return v___x_440_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_440_ = stack[0].m_num;
lean_object* v_x_441_ = stack[1].m_obj;
uint8_t v_res_442_;
v_res_442_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_440_, v_x_441_);
stack->m_num = v_res_442_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed(lean_object* v___x_443_, lean_object* v_x_444_){
_start:
{
uint8_t v___x_777__boxed_445_; uint8_t v_res_446_; lean_object* v_r_447_; 
v___x_777__boxed_445_ = lean_unbox(v___x_443_);
v_res_446_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_777__boxed_445_, v_x_444_);
lean_dec_ref(v_x_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(uint8_t v___x_448_, uint8_t v___x_449_, lean_object* v_msg_450_){
_start:
{
uint8_t v___y_452_; uint8_t v___x_456_; 
v___x_456_ = l_Lean_Message_isTrace(v_msg_450_);
if (v___x_456_ == 0)
{
v___y_452_ = v___x_449_;
goto v___jp_451_;
}
else
{
v___y_452_ = v___x_448_;
goto v___jp_451_;
}
v___jp_451_:
{
if (v___y_452_ == 0)
{
return v___x_448_;
}
else
{
uint8_t v_severity_453_; uint8_t v___x_454_; uint8_t v___x_455_; 
v_severity_453_ = lean_ctor_get_uint8(v_msg_450_, sizeof(void*)*5 + 1);
v___x_454_ = 2;
v___x_455_ = l_Lean_instBEqMessageSeverity_beq(v_severity_453_, v___x_454_);
return v___x_455_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_448_ = stack[0].m_num;
uint8_t v___x_449_ = stack[1].m_num;
lean_object* v_msg_450_ = stack[2].m_obj;
uint8_t v_res_457_;
v_res_457_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_448_, v___x_449_, v_msg_450_);
stack->m_num = v_res_457_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object* v___x_458_, lean_object* v___x_459_, lean_object* v_msg_460_){
_start:
{
uint8_t v___x_787__boxed_461_; uint8_t v___x_788__boxed_462_; uint8_t v_res_463_; lean_object* v_r_464_; 
v___x_787__boxed_461_ = lean_unbox(v___x_458_);
v___x_788__boxed_462_ = lean_unbox(v___x_459_);
v_res_463_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_787__boxed_461_, v___x_788__boxed_462_, v_msg_460_);
lean_dec_ref(v_msg_460_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(uint8_t v___x_465_, uint8_t v___x_466_, lean_object* v_msg_467_){
_start:
{
uint8_t v___y_469_; uint8_t v___x_473_; 
v___x_473_ = l_Lean_Message_isTrace(v_msg_467_);
if (v___x_473_ == 0)
{
v___y_469_ = v___x_466_;
goto v___jp_468_;
}
else
{
v___y_469_ = v___x_465_;
goto v___jp_468_;
}
v___jp_468_:
{
if (v___y_469_ == 0)
{
return v___x_465_;
}
else
{
uint8_t v_severity_470_; uint8_t v___x_471_; uint8_t v___x_472_; 
v_severity_470_ = lean_ctor_get_uint8(v_msg_467_, sizeof(void*)*5 + 1);
v___x_471_ = 1;
v___x_472_ = l_Lean_instBEqMessageSeverity_beq(v_severity_470_, v___x_471_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_465_ = stack[0].m_num;
uint8_t v___x_466_ = stack[1].m_num;
lean_object* v_msg_467_ = stack[2].m_obj;
uint8_t v_res_474_;
v_res_474_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_465_, v___x_466_, v_msg_467_);
stack->m_num = v_res_474_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v_msg_477_){
_start:
{
uint8_t v___x_812__boxed_478_; uint8_t v___x_813__boxed_479_; uint8_t v_res_480_; lean_object* v_r_481_; 
v___x_812__boxed_478_ = lean_unbox(v___x_475_);
v___x_813__boxed_479_ = lean_unbox(v___x_476_);
v_res_480_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_812__boxed_478_, v___x_813__boxed_479_, v_msg_477_);
lean_dec_ref(v_msg_477_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(uint8_t v___x_482_, uint8_t v___x_483_, lean_object* v_msg_484_){
_start:
{
uint8_t v___y_486_; uint8_t v___x_490_; 
v___x_490_ = l_Lean_Message_isTrace(v_msg_484_);
if (v___x_490_ == 0)
{
v___y_486_ = v___x_483_;
goto v___jp_485_;
}
else
{
v___y_486_ = v___x_482_;
goto v___jp_485_;
}
v___jp_485_:
{
if (v___y_486_ == 0)
{
return v___x_482_;
}
else
{
uint8_t v_severity_487_; uint8_t v___x_488_; uint8_t v___x_489_; 
v_severity_487_ = lean_ctor_get_uint8(v_msg_484_, sizeof(void*)*5 + 1);
v___x_488_ = 0;
v___x_489_ = l_Lean_instBEqMessageSeverity_beq(v_severity_487_, v___x_488_);
return v___x_489_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_482_ = stack[0].m_num;
uint8_t v___x_483_ = stack[1].m_num;
lean_object* v_msg_484_ = stack[2].m_obj;
uint8_t v_res_491_;
v_res_491_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_482_, v___x_483_, v_msg_484_);
stack->m_num = v_res_491_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v_msg_494_){
_start:
{
uint8_t v___x_837__boxed_495_; uint8_t v___x_838__boxed_496_; uint8_t v_res_497_; lean_object* v_r_498_; 
v___x_837__boxed_495_ = lean_unbox(v___x_492_);
v___x_838__boxed_496_ = lean_unbox(v___x_493_);
v_res_497_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_837__boxed_495_, v___x_838__boxed_496_, v_msg_494_);
lean_dec_ref(v_msg_494_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(lean_object* v_x_524_){
_start:
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1));
lean_inc(v_x_524_);
v___x_527_ = l_Lean_Syntax_isOfKind(v_x_524_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_dec(v_x_524_);
v___x_528_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_528_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = l_Lean_Syntax_getArg(v_x_524_, v___x_529_);
lean_dec(v_x_524_);
v___x_531_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3));
lean_inc(v___x_530_);
v___x_532_ = l_Lean_Syntax_isOfKind(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5));
lean_inc(v___x_530_);
v___x_534_ = l_Lean_Syntax_isOfKind(v___x_530_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7));
lean_inc(v___x_530_);
v___x_536_ = l_Lean_Syntax_isOfKind(v___x_530_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9));
lean_inc(v___x_530_);
v___x_538_ = l_Lean_Syntax_isOfKind(v___x_530_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11));
v___x_540_ = l_Lean_Syntax_isOfKind(v___x_530_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___x_544_; 
v___x_542_ = lean_box(v___x_540_);
v___f_543_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_543_, 0, v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___f_543_);
return v___x_544_;
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___f_547_; lean_object* v___x_548_; 
lean_dec(v___x_530_);
v___x_545_ = lean_box(v___x_536_);
v___x_546_ = lean_box(v___x_538_);
v___f_547_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_547_, 0, v___x_545_);
lean_closure_set(v___f_547_, 1, v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___f_547_);
return v___x_548_;
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___f_551_; lean_object* v___x_552_; 
lean_dec(v___x_530_);
v___x_549_ = lean_box(v___x_534_);
v___x_550_ = lean_box(v___x_536_);
v___f_551_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_551_, 0, v___x_549_);
lean_closure_set(v___f_551_, 1, v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___f_551_);
return v___x_552_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___f_555_; lean_object* v___x_556_; 
lean_dec(v___x_530_);
v___x_553_ = lean_box(v___x_532_);
v___x_554_ = lean_box(v___x_534_);
v___f_555_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_555_, 0, v___x_553_);
lean_closure_set(v___f_555_, 1, v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___f_555_);
return v___x_556_;
}
}
else
{
lean_object* v___f_557_; lean_object* v___x_558_; 
lean_dec(v___x_530_);
v___f_557_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12));
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___f_557_);
return v___x_558_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_524_ = stack[0].m_obj;
lean_object* v_res_559_;
v_res_559_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_524_);
stack->m_obj
 = v_res_559_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___boxed(lean_object* v_x_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_560_);
return v_res_562_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(lean_object* v_x_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_563_);
return v___x_567_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_563_ = stack[0].m_obj;
lean_object* v_a_564_ = stack[1].m_obj;
lean_object* v_a_565_ = stack[2].m_obj;
lean_object* v_res_568_;
v_res_568_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(v_x_563_, v_a_564_, v_a_565_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___boxed(lean_object* v_x_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(v_x_569_, v_a_570_, v_a_571_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
return v_res_573_;
}
}
uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object* v_x_574_){
_start:
{
uint8_t v___x_575_; 
v___x_575_ = 0;
return v___x_575_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_574_ = stack[0].m_obj;
uint8_t v_res_576_;
v_res_576_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(v_x_574_);
stack->m_num = v_res_576_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object* v_x_577_){
_start:
{
uint8_t v_res_578_; lean_object* v_r_579_; 
v_res_578_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(v_x_577_);
lean_dec_ref(v_x_577_);
v_r_579_ = lean_box(v_res_578_);
return v_r_579_;
}
}
uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(lean_object* v_snd_580_, lean_object* v___y_581_){
_start:
{
if (lean_obj_tag(v_snd_580_) == 0)
{
uint8_t v___x_582_; 
lean_dec_ref(v___y_581_);
v___x_582_ = 0;
return v___x_582_;
}
else
{
lean_object* v_val_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_val_583_ = lean_ctor_get(v_snd_580_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v_snd_580_, 1);
v___x_584_ = lean_apply_1(v_val_583_, v___y_581_);
v___x_585_ = lean_unbox(v___x_584_);
return v___x_585_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_580_ = stack[0].m_obj;
lean_object* v___y_581_ = stack[1].m_obj;
uint8_t v_res_586_;
v_res_586_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(v_snd_580_, v___y_581_);
stack->m_num = v_res_586_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed(lean_object* v_snd_587_, lean_object* v___y_588_){
_start:
{
uint8_t v_res_589_; lean_object* v_r_590_; 
v_res_589_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(v_snd_587_, v___y_588_);
v_r_590_ = lean_box(v_res_589_);
return v_r_590_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(lean_object* v_a_591_, lean_object* v_snd_592_, uint8_t v_a_593_, lean_object* v___y_594_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
lean_inc_ref(v___y_594_);
v___x_595_ = lean_apply_1(v_a_591_, v___y_594_);
v___x_596_ = lean_unbox(v___x_595_);
if (v___x_596_ == 0)
{
if (lean_obj_tag(v_snd_592_) == 0)
{
uint8_t v___x_597_; 
lean_dec_ref(v___y_594_);
v___x_597_ = 2;
return v___x_597_;
}
else
{
lean_object* v_val_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v_val_598_ = lean_ctor_get(v_snd_592_, 0);
lean_inc(v_val_598_);
lean_dec_ref_known(v_snd_592_, 1);
v___x_599_ = lean_apply_1(v_val_598_, v___y_594_);
v___x_600_ = lean_unbox(v___x_599_);
return v___x_600_;
}
}
else
{
lean_dec_ref(v___y_594_);
lean_dec(v_snd_592_);
return v_a_593_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_591_ = stack[0].m_obj;
lean_object* v_snd_592_ = stack[1].m_obj;
uint8_t v_a_593_ = stack[2].m_num;
lean_object* v___y_594_ = stack[3].m_obj;
uint8_t v_res_601_;
v_res_601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_591_, v_snd_592_, v_a_593_, v___y_594_);
stack->m_num = v_res_601_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed(lean_object* v_a_602_, lean_object* v_snd_603_, lean_object* v_a_604_, lean_object* v___y_605_){
_start:
{
uint8_t v_a_6397__boxed_606_; uint8_t v_res_607_; lean_object* v_r_608_; 
v_a_6397__boxed_606_ = lean_unbox(v_a_604_);
v_res_607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_602_, v_snd_603_, v_a_6397__boxed_606_, v___y_605_);
v_r_608_ = lean_box(v_res_607_);
return v_r_608_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object* v_as_669_, size_t v_sz_670_, size_t v_i_671_, lean_object* v_b_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_a_677_; uint8_t v___x_681_; 
v___x_681_ = lean_usize_dec_lt(v_i_671_, v_sz_670_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v_b_672_);
return v___x_682_;
}
else
{
lean_object* v_snd_683_; lean_object* v_snd_684_; lean_object* v_snd_685_; lean_object* v_fst_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_993_; 
v_snd_683_ = lean_ctor_get(v_b_672_, 1);
lean_inc(v_snd_683_);
v_snd_684_ = lean_ctor_get(v_snd_683_, 1);
lean_inc(v_snd_684_);
v_snd_685_ = lean_ctor_get(v_snd_684_, 1);
lean_inc(v_snd_685_);
v_fst_686_ = lean_ctor_get(v_b_672_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v_b_672_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v_b_672_, 1);
lean_dec(v_unused_994_);
v___x_688_ = v_b_672_;
v_isShared_689_ = v_isSharedCheck_993_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_fst_686_);
lean_dec(v_b_672_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_993_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fst_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_991_; 
v_fst_690_ = lean_ctor_get(v_snd_683_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v_snd_683_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v_snd_683_, 1);
lean_dec(v_unused_992_);
v___x_692_ = v_snd_683_;
v_isShared_693_ = v_isSharedCheck_991_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_fst_690_);
lean_dec(v_snd_683_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_991_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_fst_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_989_; 
v_fst_694_ = lean_ctor_get(v_snd_684_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v_snd_684_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v_snd_684_, 1);
lean_dec(v_unused_990_);
v___x_696_ = v_snd_684_;
v_isShared_697_ = v_isSharedCheck_989_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_fst_694_);
lean_dec(v_snd_684_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_989_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_fst_698_; lean_object* v_snd_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_988_; 
v_fst_698_ = lean_ctor_get(v_snd_685_, 0);
v_snd_699_ = lean_ctor_get(v_snd_685_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v_snd_685_);
if (v_isSharedCheck_988_ == 0)
{
v___x_701_ = v_snd_685_;
v_isShared_702_ = v_isSharedCheck_988_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_snd_699_);
lean_inc(v_fst_698_);
lean_dec(v_snd_685_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_988_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_a_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_a_703_ = lean_array_uget_borrowed(v_as_669_, v_i_671_);
v___x_704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_a_703_);
v___x_705_ = l_Lean_Syntax_isOfKind(v_a_703_, v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v___x_708_; 
lean_dec_ref_known(v___x_706_, 1);
if (v_isShared_702_ == 0)
{
v___x_708_ = v___x_701_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_fst_698_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_snd_699_);
v___x_708_ = v_reuseFailAlloc_718_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_710_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_708_);
v___x_710_ = v___x_696_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_fst_694_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_708_);
v___x_710_ = v_reuseFailAlloc_717_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_710_);
v___x_712_ = v___x_692_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_fst_690_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_712_);
v___x_714_ = v___x_688_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_fst_686_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
v_a_677_ = v___x_714_;
goto v___jp_676_;
}
}
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_del_object(v___x_701_);
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_del_object(v___x_696_);
lean_dec(v_fst_694_);
lean_del_object(v___x_692_);
lean_dec(v_fst_690_);
lean_del_object(v___x_688_);
lean_dec(v_fst_686_);
v_a_719_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_706_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_706_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_action_x3f_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = l_Lean_Syntax_getArg(v_a_703_, v___x_727_);
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3));
lean_inc(v___x_728_);
v___x_770_ = l_Lean_Syntax_isOfKind(v___x_728_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; uint8_t v___x_772_; 
lean_del_object(v___x_701_);
lean_del_object(v___x_696_);
lean_del_object(v___x_692_);
lean_del_object(v___x_688_);
v___x_771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5));
lean_inc(v___x_728_);
v___x_772_ = l_Lean_Syntax_isOfKind(v___x_728_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; uint8_t v_reportPositions_774_; 
v___x_773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7));
lean_inc(v___x_728_);
v_reportPositions_774_ = l_Lean_Syntax_isOfKind(v___x_728_, v___x_773_);
if (v_reportPositions_774_ == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9));
lean_inc(v___x_728_);
v___x_776_ = l_Lean_Syntax_isOfKind(v___x_728_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11));
lean_inc(v___x_728_);
v___x_778_ = l_Lean_Syntax_isOfKind(v___x_728_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec(v___x_728_);
v___x_779_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec_ref_known(v___x_779_, 1);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_fst_698_);
lean_ctor_set(v___x_780_, 1, v_snd_699_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_fst_694_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_fst_690_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v_fst_686_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v_a_677_ = v___x_783_;
goto v___jp_676_;
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_dec(v_fst_694_);
lean_dec(v_fst_690_);
lean_dec(v_fst_686_);
v_a_784_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_779_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_779_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_792_ = lean_unsigned_to_nat(2u);
v___x_793_ = l_Lean_Syntax_getArg(v___x_728_, v___x_792_);
lean_dec(v___x_728_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_793_);
v___x_795_ = l_Lean_Syntax_isOfKind(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_797_ = l_Lean_Syntax_isOfKind(v___x_793_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec_ref_known(v___x_798_, 1);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_fst_698_);
lean_ctor_set(v___x_799_, 1, v_snd_699_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_fst_694_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_fst_690_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_fst_686_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v_a_677_ = v___x_802_;
goto v___jp_676_;
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_dec(v_fst_694_);
lean_dec(v_fst_690_);
lean_dec(v_fst_686_);
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
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v_fst_698_);
v___x_811_ = lean_box(v_reportPositions_774_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v_snd_699_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v_fst_694_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_fst_690_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_fst_686_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v_a_677_ = v___x_815_;
goto v___jp_676_;
}
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec(v___x_793_);
lean_dec(v_fst_698_);
v___x_816_ = lean_box(v___x_705_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_snd_699_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_fst_694_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_fst_690_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_fst_686_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v_a_677_ = v___x_820_;
goto v___jp_676_;
}
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_821_ = lean_unsigned_to_nat(2u);
v___x_822_ = l_Lean_Syntax_getArg(v___x_728_, v___x_821_);
lean_dec(v___x_728_);
v___x_823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17));
lean_inc(v___x_822_);
v___x_824_ = l_Lean_Syntax_isOfKind(v___x_822_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_dec(v___x_822_);
v___x_825_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec_ref_known(v___x_825_, 1);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v_fst_698_);
lean_ctor_set(v___x_826_, 1, v_snd_699_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v_fst_694_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v_fst_690_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v_fst_686_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v_a_677_ = v___x_829_;
goto v___jp_676_;
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_dec(v_fst_694_);
lean_dec(v_fst_690_);
lean_dec(v_fst_686_);
v_a_830_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_825_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_825_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_838_ = l_Lean_Syntax_getArg(v___x_822_, v___x_727_);
lean_dec(v___x_822_);
v___x_839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_838_);
v___x_840_ = l_Lean_Syntax_isOfKind(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_842_ = l_Lean_Syntax_isOfKind(v___x_838_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref_known(v___x_843_, 1);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_fst_698_);
lean_ctor_set(v___x_844_, 1, v_snd_699_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_fst_694_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v_fst_690_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_fst_686_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v_a_677_ = v___x_847_;
goto v___jp_676_;
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_dec(v_fst_694_);
lean_dec(v_fst_690_);
lean_dec(v_fst_686_);
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
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec(v_fst_694_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_fst_698_);
lean_ctor_set(v___x_856_, 1, v_snd_699_);
v___x_857_ = lean_box(v_reportPositions_774_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_fst_690_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_fst_686_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v_a_677_ = v___x_860_;
goto v___jp_676_;
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec(v___x_838_);
lean_dec(v_fst_694_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_fst_698_);
lean_ctor_set(v___x_861_, 1, v_snd_699_);
v___x_862_ = lean_box(v___x_705_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v___x_861_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v_fst_690_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v_fst_686_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v_a_677_ = v___x_865_;
goto v___jp_676_;
}
}
}
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_866_ = lean_unsigned_to_nat(2u);
v___x_867_ = l_Lean_Syntax_getArg(v___x_728_, v___x_866_);
lean_dec(v___x_728_);
v___x_868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19));
lean_inc(v___x_867_);
v___x_869_ = l_Lean_Syntax_isOfKind(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
lean_dec(v___x_867_);
v___x_870_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec_ref_known(v___x_870_, 1);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v_fst_698_);
lean_ctor_set(v___x_871_, 1, v_snd_699_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_fst_694_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_fst_690_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_fst_686_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v_a_677_ = v___x_874_;
goto v___jp_676_;
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_dec(v_fst_694_);
lean_dec(v_fst_690_);
lean_dec(v_fst_686_);
v_a_875_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_870_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_870_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_883_ = l_Lean_Syntax_getArg(v___x_867_, v___x_727_);
lean_dec(v___x_867_);
v___x_884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_883_);
v___x_885_ = l_Lean_Syntax_isOfKind(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23));
v___x_887_ = l_Lean_Syntax_isOfKind(v___x_883_, v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec_ref_known(v___x_888_, 1);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v_fst_698_);
lean_ctor_set(v___x_889_, 1, v_snd_699_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v_fst_694_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_fst_690_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v_fst_686_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v_a_677_ = v___x_892_;
goto v___jp_676_;
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_dec(v_fst_694_);
lean_dec(v_fst_690_);
lean_dec(v_fst_686_);
v_a_893_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_888_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_888_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec(v_fst_690_);
v___x_901_ = 1;
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v_fst_698_);
lean_ctor_set(v___x_902_, 1, v_snd_699_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v_fst_694_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_box(v___x_901_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_903_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v_fst_686_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v_a_677_ = v___x_906_;
goto v___jp_676_;
}
}
else
{
uint8_t v_ordering_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec(v___x_883_);
lean_dec(v_fst_690_);
v_ordering_907_ = 0;
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v_fst_698_);
lean_ctor_set(v___x_908_, 1, v_snd_699_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_fst_694_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_box(v_ordering_907_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_909_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_fst_686_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v_a_677_ = v___x_912_;
goto v___jp_676_;
}
}
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_913_ = lean_unsigned_to_nat(2u);
v___x_914_ = l_Lean_Syntax_getArg(v___x_728_, v___x_913_);
lean_dec(v___x_728_);
v___x_915_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25));
lean_inc(v___x_914_);
v___x_916_ = l_Lean_Syntax_isOfKind(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_dec(v___x_914_);
v___x_917_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
lean_dec_ref_known(v___x_917_, 1);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v_fst_698_);
lean_ctor_set(v___x_918_, 1, v_snd_699_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_fst_694_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_fst_690_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v_fst_686_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v_a_677_ = v___x_921_;
goto v___jp_676_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_dec(v_fst_694_);
lean_dec(v_fst_690_);
lean_dec(v_fst_686_);
v_a_922_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_917_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_917_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_930_ = l_Lean_Syntax_getArg(v___x_914_, v___x_727_);
lean_dec(v___x_914_);
v___x_931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_930_);
v___x_932_ = l_Lean_Syntax_isOfKind(v___x_930_, v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27));
lean_inc(v___x_930_);
v___x_934_ = l_Lean_Syntax_isOfKind(v___x_930_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29));
v___x_936_ = l_Lean_Syntax_isOfKind(v___x_930_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
lean_dec_ref_known(v___x_937_, 1);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_fst_698_);
lean_ctor_set(v___x_938_, 1, v_snd_699_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_fst_694_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v_fst_690_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v_fst_686_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v_a_677_ = v___x_941_;
goto v___jp_676_;
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_dec(v_fst_694_);
lean_dec(v_fst_690_);
lean_dec(v_fst_686_);
v_a_942_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_937_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_937_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v_fst_686_);
v___x_950_ = 2;
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v_fst_698_);
lean_ctor_set(v___x_951_, 1, v_snd_699_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_fst_694_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_fst_690_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_box(v___x_950_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
v_a_677_ = v___x_955_;
goto v___jp_676_;
}
}
else
{
uint8_t v_whitespace_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec(v___x_930_);
lean_dec(v_fst_686_);
v_whitespace_956_ = 1;
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_fst_698_);
lean_ctor_set(v___x_957_, 1, v_snd_699_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v_fst_694_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v_fst_690_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_box(v_whitespace_956_);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_959_);
v_a_677_ = v___x_961_;
goto v___jp_676_;
}
}
else
{
uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v___x_930_);
lean_dec(v_fst_686_);
v___x_962_ = 0;
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v_fst_698_);
lean_ctor_set(v___x_963_, 1, v_snd_699_);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v_fst_694_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v_fst_690_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_box(v___x_962_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_965_);
v_a_677_ = v___x_967_;
goto v___jp_676_;
}
}
}
}
else
{
lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_968_ = l_Lean_Syntax_getArg(v___x_728_, v___x_727_);
v___x_969_ = l_Lean_Syntax_isNone(v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_968_);
v___x_971_ = l_Lean_Syntax_matchesNull(v___x_968_, v___x_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; 
lean_dec(v___x_968_);
lean_dec(v___x_728_);
lean_del_object(v___x_701_);
lean_del_object(v___x_696_);
lean_del_object(v___x_692_);
lean_del_object(v___x_688_);
v___x_972_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec_ref_known(v___x_972_, 1);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_fst_698_);
lean_ctor_set(v___x_973_, 1, v_snd_699_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_fst_694_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_fst_690_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v_fst_686_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v_a_677_ = v___x_976_;
goto v___jp_676_;
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_dec(v_fst_694_);
lean_dec(v_fst_690_);
lean_dec(v_fst_686_);
v_a_977_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_972_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_972_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = l_Lean_Syntax_getArg(v___x_968_, v___x_727_);
lean_dec(v___x_968_);
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
v_action_x3f_730_ = v___x_986_;
v___y_731_ = v___y_673_;
v___y_732_ = v___y_674_;
goto v___jp_729_;
}
}
else
{
lean_object* v___x_987_; 
lean_dec(v___x_968_);
v___x_987_ = lean_box(0);
v_action_x3f_730_ = v___x_987_;
v___y_731_ = v___y_673_;
v___y_732_ = v___y_674_;
goto v___jp_729_;
}
}
v___jp_729_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = l_Lean_Syntax_getArg(v___x_728_, v___x_733_);
lean_dec(v___x_728_);
v___x_735_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_730_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v___x_734_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v___f_739_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_739_, 0, v_a_738_);
lean_closure_set(v___f_739_, 1, v_snd_699_);
lean_closure_set(v___f_739_, 2, v_a_736_);
v___x_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_740_, 0, v___f_739_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_740_);
v___x_742_ = v___x_701_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_fst_698_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_752_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_742_);
v___x_744_ = v___x_696_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_fst_694_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_742_);
v___x_744_ = v_reuseFailAlloc_751_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_744_);
v___x_746_ = v___x_692_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_fst_690_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_746_);
v___x_748_ = v___x_688_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_fst_686_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
v_a_677_ = v___x_748_;
goto v___jp_676_;
}
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec(v_a_736_);
lean_del_object(v___x_701_);
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_del_object(v___x_696_);
lean_dec(v_fst_694_);
lean_del_object(v___x_692_);
lean_dec(v_fst_690_);
lean_del_object(v___x_688_);
lean_dec(v_fst_686_);
v_a_753_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_737_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_737_);
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
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v___x_734_);
lean_del_object(v___x_701_);
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_del_object(v___x_696_);
lean_dec(v_fst_694_);
lean_del_object(v___x_692_);
lean_dec(v_fst_690_);
lean_del_object(v___x_688_);
lean_dec(v_fst_686_);
v_a_761_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_735_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_735_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
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
v___jp_676_:
{
size_t v___x_678_; size_t v___x_679_; 
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_671_, v___x_678_);
v_i_671_ = v___x_679_;
v_b_672_ = v_a_677_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_669_ = stack[0].m_obj;
size_t v_sz_670_ = stack[1].m_num;
size_t v_i_671_ = stack[2].m_num;
lean_object* v_b_672_ = stack[3].m_obj;
lean_object* v___y_673_ = stack[4].m_obj;
lean_object* v___y_674_ = stack[5].m_obj;
lean_object* v_res_995_;
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v_as_669_, v_sz_670_, v_i_671_, v_b_672_, v___y_673_, v___y_674_);
stack->m_obj
 = v_res_995_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object* v_as_996_, lean_object* v_sz_997_, lean_object* v_i_998_, lean_object* v_b_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
size_t v_sz_boxed_1003_; size_t v_i_boxed_1004_; lean_object* v_res_1005_; 
v_sz_boxed_1003_ = lean_unbox_usize(v_sz_997_);
lean_dec(v_sz_997_);
v_i_boxed_1004_ = lean_unbox_usize(v_i_998_);
lean_dec(v_i_998_);
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v_as_996_, v_sz_boxed_1003_, v_i_boxed_1004_, v_b_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec_ref(v_as_996_);
return v_res_1005_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(size_t v_sz_1006_, size_t v_i_1007_, lean_object* v_bs_1008_){
_start:
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_usize_dec_lt(v_i_1007_, v_sz_1006_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_bs_1008_);
return v___x_1010_;
}
else
{
lean_object* v_v_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v_v_1011_ = lean_array_uget(v_bs_1008_, v_i_1007_);
v___x_1012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_v_1011_);
v___x_1013_ = l_Lean_Syntax_isOfKind(v_v_1011_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_dec(v_v_1011_);
lean_dec_ref(v_bs_1008_);
v___x_1014_ = lean_box(0);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v_bs_x27_1016_; size_t v___x_1017_; size_t v___x_1018_; lean_object* v___x_1019_; 
v___x_1015_ = lean_unsigned_to_nat(0u);
v_bs_x27_1016_ = lean_array_uset(v_bs_1008_, v_i_1007_, v___x_1015_);
v___x_1017_ = ((size_t)1ULL);
v___x_1018_ = lean_usize_add(v_i_1007_, v___x_1017_);
v___x_1019_ = lean_array_uset(v_bs_x27_1016_, v_i_1007_, v_v_1011_);
v_i_1007_ = v___x_1018_;
v_bs_1008_ = v___x_1019_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1006_ = stack[0].m_num;
size_t v_i_1007_ = stack[1].m_num;
lean_object* v_bs_1008_ = stack[2].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_1006_, v_i_1007_, v_bs_1008_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1___boxed(lean_object* v_sz_1022_, lean_object* v_i_1023_, lean_object* v_bs_1024_){
_start:
{
size_t v_sz_boxed_1025_; size_t v_i_boxed_1026_; lean_object* v_res_1027_; 
v_sz_boxed_1025_ = lean_unbox_usize(v_sz_1022_);
lean_dec(v_sz_1022_);
v_i_boxed_1026_ = lean_unbox_usize(v_i_1023_);
lean_dec(v_i_1023_);
v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_boxed_1025_, v_i_boxed_1026_, v_bs_1024_);
return v_res_1027_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(uint8_t v___x_1028_, lean_object* v_as_1029_, size_t v_i_1030_, size_t v_stop_1031_, lean_object* v_b_1032_){
_start:
{
lean_object* v___y_1034_; uint8_t v___x_1038_; 
v___x_1038_ = lean_usize_dec_eq(v_i_1030_, v_stop_1031_);
if (v___x_1038_ == 0)
{
lean_object* v_fst_1039_; uint8_t v___x_1040_; 
v_fst_1039_ = lean_ctor_get(v_b_1032_, 0);
v___x_1040_ = lean_unbox(v_fst_1039_);
if (v___x_1040_ == 0)
{
lean_object* v_snd_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
v_snd_1041_ = lean_ctor_get(v_b_1032_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_b_1032_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v_b_1032_, 0);
lean_dec(v_unused_1050_);
v___x_1043_ = v_b_1032_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_snd_1041_);
lean_dec(v_b_1032_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_box(v___x_1028_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1045_);
v___x_1047_ = v___x_1043_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_snd_1041_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
v___y_1034_ = v___x_1047_;
goto v___jp_1033_;
}
}
}
else
{
lean_object* v_snd_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1061_; 
v_snd_1051_ = lean_ctor_get(v_b_1032_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_b_1032_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_b_1032_, 0);
lean_dec(v_unused_1062_);
v___x_1053_ = v_b_1032_;
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_snd_1051_);
lean_dec(v_b_1032_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1055_ = lean_array_uget_borrowed(v_as_1029_, v_i_1030_);
lean_inc(v___x_1055_);
v___x_1056_ = lean_array_push(v_snd_1051_, v___x_1055_);
v___x_1057_ = lean_box(v___x_1038_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1056_);
lean_ctor_set(v___x_1053_, 0, v___x_1057_);
v___x_1059_ = v___x_1053_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1056_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
v___y_1034_ = v___x_1059_;
goto v___jp_1033_;
}
}
}
}
else
{
return v_b_1032_;
}
v___jp_1033_:
{
size_t v___x_1035_; size_t v___x_1036_; 
v___x_1035_ = ((size_t)1ULL);
v___x_1036_ = lean_usize_add(v_i_1030_, v___x_1035_);
v_i_1030_ = v___x_1036_;
v_b_1032_ = v___y_1034_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1028_ = stack[0].m_num;
lean_object* v_as_1029_ = stack[1].m_obj;
size_t v_i_1030_ = stack[2].m_num;
size_t v_stop_1031_ = stack[3].m_num;
lean_object* v_b_1032_ = stack[4].m_obj;
lean_object* v_res_1063_;
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1028_, v_as_1029_, v_i_1030_, v_stop_1031_, v_b_1032_);
stack->m_obj
 = v_res_1063_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object* v___x_1064_, lean_object* v_as_1065_, lean_object* v_i_1066_, lean_object* v_stop_1067_, lean_object* v_b_1068_){
_start:
{
uint8_t v___x_7666__boxed_1069_; size_t v_i_boxed_1070_; size_t v_stop_boxed_1071_; lean_object* v_res_1072_; 
v___x_7666__boxed_1069_ = lean_unbox(v___x_1064_);
v_i_boxed_1070_ = lean_unbox_usize(v_i_1066_);
lean_dec(v_i_1066_);
v_stop_boxed_1071_ = lean_unbox_usize(v_stop_1067_);
lean_dec(v_stop_1067_);
v_res_1072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_7666__boxed_1069_, v_as_1065_, v_i_boxed_1070_, v_stop_boxed_1071_, v_b_1068_);
lean_dec_ref(v_as_1065_);
return v_res_1072_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object* v_spec_x3f_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_elts_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1145_; lean_object* v_cfg_1159_; 
v_cfg_1159_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5));
if (lean_obj_tag(v_spec_x3f_1101_) == 1)
{
lean_object* v_val_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_val_1160_ = lean_ctor_get(v_spec_x3f_1101_, 0);
lean_inc_n(v_val_1160_, 2);
lean_dec_ref_known(v_spec_x3f_1101_, 1);
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7));
v___x_1162_ = l_Lean_Syntax_isOfKind(v_val_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_val_1160_);
v___x_1163_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = l_Lean_Syntax_getArg(v_val_1160_, v___x_1172_);
lean_dec(v_val_1160_);
v___x_1174_ = l_Lean_Syntax_getArgs(v___x_1173_);
lean_dec(v___x_1173_);
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8));
v___x_1177_ = lean_array_get_size(v___x_1174_);
v___x_1178_ = lean_nat_dec_lt(v___x_1175_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec_ref(v___x_1174_);
v___y_1145_ = v___x_1176_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; lean_object* v___x_1183_; lean_object* v_snd_1184_; 
v___x_1179_ = lean_box(v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v___x_1176_);
v___x_1181_ = ((size_t)0ULL);
v___x_1182_ = lean_usize_of_nat(v___x_1177_);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1162_, v___x_1174_, v___x_1181_, v___x_1182_, v___x_1180_);
lean_dec_ref(v___x_1174_);
v_snd_1184_ = lean_ctor_get(v___x_1183_, 1);
lean_inc(v_snd_1184_);
lean_dec_ref(v___x_1183_);
v___y_1145_ = v_snd_1184_;
goto v___jp_1144_;
}
}
}
else
{
lean_object* v___x_1185_; 
lean_dec(v_spec_x3f_1101_);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v_cfg_1159_);
return v___x_1185_;
}
v___jp_1105_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; size_t v_sz_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1109_ = l_Array_reverse___redArg(v_elts_1106_);
v___x_1110_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4));
v_sz_1111_ = lean_array_size(v___x_1109_);
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v___x_1109_, v_sz_1111_, v___x_1112_, v___x_1110_, v___y_1107_, v___y_1108_);
lean_dec_ref(v___x_1109_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1135_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1135_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1135_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_snd_1118_; lean_object* v_snd_1119_; lean_object* v_snd_1120_; lean_object* v_fst_1121_; lean_object* v_fst_1122_; lean_object* v_fst_1123_; lean_object* v_fst_1124_; lean_object* v_snd_1125_; lean_object* v___y_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; uint8_t v___x_1129_; uint8_t v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1133_; 
v_snd_1118_ = lean_ctor_get(v_a_1114_, 1);
lean_inc(v_snd_1118_);
v_snd_1119_ = lean_ctor_get(v_snd_1118_, 1);
lean_inc(v_snd_1119_);
v_snd_1120_ = lean_ctor_get(v_snd_1119_, 1);
lean_inc(v_snd_1120_);
v_fst_1121_ = lean_ctor_get(v_a_1114_, 0);
lean_inc(v_fst_1121_);
lean_dec(v_a_1114_);
v_fst_1122_ = lean_ctor_get(v_snd_1118_, 0);
lean_inc(v_fst_1122_);
lean_dec(v_snd_1118_);
v_fst_1123_ = lean_ctor_get(v_snd_1119_, 0);
lean_inc(v_fst_1123_);
lean_dec(v_snd_1119_);
v_fst_1124_ = lean_ctor_get(v_snd_1120_, 0);
lean_inc(v_fst_1124_);
v_snd_1125_ = lean_ctor_get(v_snd_1120_, 1);
lean_inc(v_snd_1125_);
lean_dec(v_snd_1120_);
v___y_1126_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___y_1126_, 0, v_snd_1125_);
v___x_1127_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1127_, 0, v___y_1126_);
v___x_1128_ = lean_unbox(v_fst_1121_);
lean_dec(v_fst_1121_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*1, v___x_1128_);
v___x_1129_ = lean_unbox(v_fst_1122_);
lean_dec(v_fst_1122_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*1 + 1, v___x_1129_);
v___x_1130_ = lean_unbox(v_fst_1123_);
lean_dec(v_fst_1123_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*1 + 2, v___x_1130_);
v___x_1131_ = lean_unbox(v_fst_1124_);
lean_dec(v_fst_1124_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*1 + 3, v___x_1131_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1127_);
v___x_1133_ = v___x_1116_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1127_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
v_a_1136_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1113_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1113_);
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
}
v___jp_1144_:
{
size_t v_sz_1146_; size_t v___x_1147_; lean_object* v___x_1148_; 
v_sz_1146_ = lean_array_size(v___y_1145_);
v___x_1147_ = ((size_t)0ULL);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_1146_, v___x_1147_, v___y_1145_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v___x_1149_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
lean_object* v_val_1158_; 
v_val_1158_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_val_1158_);
lean_dec_ref_known(v___x_1148_, 1);
v_elts_1106_ = v_val_1158_;
v___y_1107_ = v_a_1102_;
v___y_1108_ = v_a_1103_;
goto v___jp_1105_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_x3f_1101_ = stack[0].m_obj;
lean_object* v_a_1102_ = stack[1].m_obj;
lean_object* v_a_1103_ = stack[2].m_obj;
lean_object* v_res_1186_;
v_res_1186_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v_spec_x3f_1101_, v_a_1102_, v_a_1103_);
stack->m_obj
 = v_res_1186_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object* v_spec_x3f_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v_spec_x3f_1187_, v_a_1188_, v_a_1189_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(lean_object* v_s_1204_, lean_object* v_replacement_1205_, lean_object* v_a_1206_, lean_object* v_b_1207_){
_start:
{
lean_object* v_it_1209_; lean_object* v_startPos_1210_; lean_object* v_endPos_1211_; lean_object* v_it_1220_; 
switch(lean_obj_tag(v_a_1206_))
{
case 0:
{
lean_object* v_pos_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1238_; 
v_pos_1226_ = lean_ctor_get(v_a_1206_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_a_1206_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1228_ = v_a_1206_;
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_pos_1226_);
lean_dec(v_a_1206_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_startInclusive_1230_; lean_object* v_endExclusive_1231_; lean_object* v___x_1232_; uint8_t v_decide_1233_; 
v_startInclusive_1230_ = lean_ctor_get(v_s_1204_, 1);
v_endExclusive_1231_ = lean_ctor_get(v_s_1204_, 2);
v___x_1232_ = lean_nat_sub(v_endExclusive_1231_, v_startInclusive_1230_);
v_decide_1233_ = lean_nat_dec_eq(v_pos_1226_, v___x_1232_);
lean_dec(v___x_1232_);
if (v_decide_1233_ == 0)
{
lean_object* v___x_1235_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set_tag(v___x_1228_, 1);
v___x_1235_ = v___x_1228_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_pos_1226_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
v_it_1220_ = v___x_1235_;
goto v___jp_1219_;
}
}
else
{
lean_object* v___x_1237_; 
lean_del_object(v___x_1228_);
lean_dec(v_pos_1226_);
v___x_1237_ = lean_box(3);
v_it_1220_ = v___x_1237_;
goto v___jp_1219_;
}
}
}
case 1:
{
lean_object* v_pos_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1251_; 
v_pos_1239_ = lean_ctor_get(v_a_1206_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_a_1206_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1241_ = v_a_1206_;
v_isShared_1242_ = v_isSharedCheck_1251_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_pos_1239_);
lean_dec(v_a_1206_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1251_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_str_1243_; lean_object* v_startInclusive_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v_str_1243_ = lean_ctor_get(v_s_1204_, 0);
v_startInclusive_1244_ = lean_ctor_get(v_s_1204_, 1);
v___x_1245_ = lean_nat_add(v_startInclusive_1244_, v_pos_1239_);
v___x_1246_ = lean_string_utf8_next_fast(v_str_1243_, v___x_1245_);
lean_dec(v___x_1245_);
v___x_1247_ = lean_nat_sub(v___x_1246_, v_startInclusive_1244_);
lean_inc(v___x_1247_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set_tag(v___x_1241_, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1247_);
v___x_1249_ = v___x_1241_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
v_it_1209_ = v___x_1249_;
v_startPos_1210_ = v_pos_1239_;
v_endPos_1211_ = v___x_1247_;
goto v___jp_1208_;
}
}
}
case 2:
{
lean_object* v_needle_1252_; lean_object* v_table_1253_; lean_object* v_stackPos_1254_; lean_object* v_needlePos_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1316_; 
v_needle_1252_ = lean_ctor_get(v_a_1206_, 0);
v_table_1253_ = lean_ctor_get(v_a_1206_, 1);
v_stackPos_1254_ = lean_ctor_get(v_a_1206_, 2);
v_needlePos_1255_ = lean_ctor_get(v_a_1206_, 3);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_a_1206_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1257_ = v_a_1206_;
v_isShared_1258_ = v_isSharedCheck_1316_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_needlePos_1255_);
lean_inc(v_stackPos_1254_);
lean_inc(v_table_1253_);
lean_inc(v_needle_1252_);
lean_dec(v_a_1206_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1316_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_str_1259_; lean_object* v_startInclusive_1260_; lean_object* v_endExclusive_1261_; lean_object* v_str_1262_; lean_object* v_startInclusive_1263_; lean_object* v_endExclusive_1264_; lean_object* v_basePos_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_str_1259_ = lean_ctor_get(v_needle_1252_, 0);
v_startInclusive_1260_ = lean_ctor_get(v_needle_1252_, 1);
v_endExclusive_1261_ = lean_ctor_get(v_needle_1252_, 2);
v_str_1262_ = lean_ctor_get(v_s_1204_, 0);
v_startInclusive_1263_ = lean_ctor_get(v_s_1204_, 1);
v_endExclusive_1264_ = lean_ctor_get(v_s_1204_, 2);
v_basePos_1265_ = lean_nat_sub(v_stackPos_1254_, v_needlePos_1255_);
v___x_1266_ = lean_nat_sub(v_endExclusive_1261_, v_startInclusive_1260_);
v___x_1267_ = lean_nat_add(v_basePos_1265_, v___x_1266_);
v___x_1268_ = lean_nat_sub(v_endExclusive_1264_, v_startInclusive_1263_);
v___x_1269_ = lean_nat_dec_le(v___x_1267_, v___x_1268_);
lean_dec(v___x_1267_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
lean_dec(v___x_1266_);
lean_del_object(v___x_1257_);
lean_dec(v_needlePos_1255_);
lean_dec(v_stackPos_1254_);
lean_dec_ref(v_table_1253_);
lean_dec_ref(v_needle_1252_);
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_nat_add(v_basePos_1265_, v___x_1270_);
v___x_1272_ = lean_nat_dec_le(v___x_1271_, v___x_1268_);
lean_dec(v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec(v___x_1268_);
lean_dec(v_basePos_1265_);
lean_dec_ref(v_s_1204_);
return v_b_1207_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = l_String_Slice_pos_x21(v_s_1204_, v_basePos_1265_);
lean_dec(v_basePos_1265_);
v___x_1274_ = lean_box(3);
v_it_1209_ = v___x_1274_;
v_startPos_1210_ = v___x_1273_;
v_endPos_1211_ = v___x_1268_;
goto v___jp_1208_;
}
}
else
{
lean_object* v___x_1275_; uint8_t v_stackByte_1276_; lean_object* v___x_1277_; uint8_t v_patByte_1278_; uint8_t v___x_1279_; 
lean_dec(v___x_1268_);
v___x_1275_ = lean_nat_add(v_startInclusive_1263_, v_stackPos_1254_);
v_stackByte_1276_ = lean_string_get_byte_fast(v_str_1262_, v___x_1275_);
v___x_1277_ = lean_nat_add(v_startInclusive_1260_, v_needlePos_1255_);
v_patByte_1278_ = lean_string_get_byte_fast(v_str_1259_, v___x_1277_);
v___x_1279_ = lean_uint8_dec_eq(v_stackByte_1276_, v_patByte_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; uint8_t v_decide_1281_; 
lean_dec(v___x_1266_);
v___x_1280_ = lean_unsigned_to_nat(0u);
v_decide_1281_ = lean_nat_dec_eq(v_needlePos_1255_, v___x_1280_);
if (v_decide_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v_newNeedlePos_1284_; uint8_t v___x_1285_; 
v___x_1282_ = lean_unsigned_to_nat(1u);
v___x_1283_ = lean_nat_sub(v_needlePos_1255_, v___x_1282_);
lean_dec(v_needlePos_1255_);
v_newNeedlePos_1284_ = lean_array_fget_borrowed(v_table_1253_, v___x_1283_);
lean_dec(v___x_1283_);
v___x_1285_ = lean_nat_dec_eq(v_newNeedlePos_1284_, v___x_1280_);
if (v___x_1285_ == 0)
{
lean_object* v_oldBasePos_1286_; lean_object* v___x_1287_; lean_object* v_newBasePos_1288_; lean_object* v___x_1290_; 
lean_inc(v_newNeedlePos_1284_);
v_oldBasePos_1286_ = l_String_Slice_pos_x21(v_s_1204_, v_basePos_1265_);
lean_dec(v_basePos_1265_);
v___x_1287_ = lean_nat_sub(v_stackPos_1254_, v_newNeedlePos_1284_);
v_newBasePos_1288_ = l_String_Slice_pos_x21(v_s_1204_, v___x_1287_);
lean_dec(v___x_1287_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 3, v_newNeedlePos_1284_);
v___x_1290_ = v___x_1257_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_needle_1252_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_table_1253_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_stackPos_1254_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_newNeedlePos_1284_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
v_it_1209_ = v___x_1290_;
v_startPos_1210_ = v_oldBasePos_1286_;
v_endPos_1211_ = v_newBasePos_1288_;
goto v___jp_1208_;
}
}
else
{
lean_object* v_basePos_1292_; lean_object* v_nextStackPos_1293_; lean_object* v___x_1295_; 
v_basePos_1292_ = l_String_Slice_pos_x21(v_s_1204_, v_basePos_1265_);
lean_dec(v_basePos_1265_);
v_nextStackPos_1293_ = l_String_Slice_posGE___redArg(v_s_1204_, v_stackPos_1254_);
lean_inc(v_nextStackPos_1293_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 3, v___x_1280_);
lean_ctor_set(v___x_1257_, 2, v_nextStackPos_1293_);
v___x_1295_ = v___x_1257_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_needle_1252_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_table_1253_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_nextStackPos_1293_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v___x_1280_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
v_it_1209_ = v___x_1295_;
v_startPos_1210_ = v_basePos_1292_;
v_endPos_1211_ = v_nextStackPos_1293_;
goto v___jp_1208_;
}
}
}
else
{
lean_object* v_basePos_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_nextStackPos_1300_; lean_object* v___x_1302_; 
lean_dec(v_basePos_1265_);
lean_dec(v_needlePos_1255_);
v_basePos_1297_ = l_String_Slice_pos_x21(v_s_1204_, v_stackPos_1254_);
v___x_1298_ = lean_unsigned_to_nat(1u);
v___x_1299_ = lean_nat_add(v_stackPos_1254_, v___x_1298_);
lean_dec(v_stackPos_1254_);
v_nextStackPos_1300_ = l_String_Slice_posGE___redArg(v_s_1204_, v___x_1299_);
lean_inc(v_nextStackPos_1300_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 3, v___x_1280_);
lean_ctor_set(v___x_1257_, 2, v_nextStackPos_1300_);
v___x_1302_ = v___x_1257_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_needle_1252_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_table_1253_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_nextStackPos_1300_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v___x_1280_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
v_it_1209_ = v___x_1302_;
v_startPos_1210_ = v_basePos_1297_;
v_endPos_1211_ = v_nextStackPos_1300_;
goto v___jp_1208_;
}
}
}
else
{
lean_object* v___x_1304_; lean_object* v_nextStackPos_1305_; lean_object* v_nextNeedlePos_1306_; uint8_t v_decide_1307_; 
lean_dec(v_basePos_1265_);
v___x_1304_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1305_ = lean_nat_add(v_stackPos_1254_, v___x_1304_);
lean_dec(v_stackPos_1254_);
v_nextNeedlePos_1306_ = lean_nat_add(v_needlePos_1255_, v___x_1304_);
lean_dec(v_needlePos_1255_);
v_decide_1307_ = lean_nat_dec_eq(v_nextNeedlePos_1306_, v___x_1266_);
lean_dec(v___x_1266_);
if (v_decide_1307_ == 0)
{
lean_object* v___x_1309_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 3, v_nextNeedlePos_1306_);
lean_ctor_set(v___x_1257_, 2, v_nextStackPos_1305_);
v___x_1309_ = v___x_1257_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_needle_1252_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_table_1253_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v_nextStackPos_1305_);
lean_ctor_set(v_reuseFailAlloc_1311_, 3, v_nextNeedlePos_1306_);
v___x_1309_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
v_a_1206_ = v___x_1309_;
goto _start;
}
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_dec(v_nextNeedlePos_1306_);
v___x_1312_ = lean_unsigned_to_nat(0u);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 3, v___x_1312_);
lean_ctor_set(v___x_1257_, 2, v_nextStackPos_1305_);
v___x_1314_ = v___x_1257_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_needle_1252_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_table_1253_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_nextStackPos_1305_);
lean_ctor_set(v_reuseFailAlloc_1315_, 3, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
v_it_1220_ = v___x_1314_;
goto v___jp_1219_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1204_);
return v_b_1207_;
}
}
v___jp_1208_:
{
lean_object* v___x_1212_; lean_object* v_str_1213_; lean_object* v_startInclusive_1214_; lean_object* v_endExclusive_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_inc_ref(v_s_1204_);
v___x_1212_ = l_String_Slice_slice_x21(v_s_1204_, v_startPos_1210_, v_endPos_1211_);
lean_dec(v_endPos_1211_);
lean_dec(v_startPos_1210_);
v_str_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc_ref(v_str_1213_);
v_startInclusive_1214_ = lean_ctor_get(v___x_1212_, 1);
lean_inc(v_startInclusive_1214_);
v_endExclusive_1215_ = lean_ctor_get(v___x_1212_, 2);
lean_inc(v_endExclusive_1215_);
lean_dec_ref(v___x_1212_);
v___x_1216_ = lean_string_utf8_extract_fast(v_str_1213_, v_startInclusive_1214_, v_endExclusive_1215_);
lean_dec(v_endExclusive_1215_);
lean_dec(v_startInclusive_1214_);
lean_dec_ref(v_str_1213_);
v___x_1217_ = lean_string_append(v_b_1207_, v___x_1216_);
lean_dec_ref(v___x_1216_);
v_a_1206_ = v_it_1209_;
v_b_1207_ = v___x_1217_;
goto _start;
}
v___jp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_string_utf8_byte_size(v_replacement_1205_);
v___x_1223_ = lean_string_utf8_extract_fast(v_replacement_1205_, v___x_1221_, v___x_1222_);
v___x_1224_ = lean_string_append(v_b_1207_, v___x_1223_);
lean_dec_ref(v___x_1223_);
v_a_1206_ = v_it_1220_;
v_b_1207_ = v___x_1224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg___boxed(lean_object* v_s_1317_, lean_object* v_replacement_1318_, lean_object* v_a_1319_, lean_object* v_b_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1317_, v_replacement_1318_, v_a_1319_, v_b_1320_);
lean_dec_ref(v_replacement_1318_);
return v_res_1321_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1));
v___x_1328_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2);
v___x_1331_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1));
v___x_1332_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v___x_1330_);
lean_ctor_set(v___x_1332_, 2, v___x_1329_);
lean_ctor_set(v___x_1332_, 3, v___x_1329_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object* v_s_1333_, lean_object* v_replacement_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1336_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1337_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1333_, v_replacement_1334_, v___x_1336_, v___x_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___boxed(lean_object* v_s_1338_, lean_object* v_replacement_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1338_, v_replacement_1339_);
lean_dec_ref(v_replacement_1339_);
return v_res_1340_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1));
v___x_1347_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1348_ = lean_unsigned_to_nat(0u);
v___x_1349_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2);
v___x_1350_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1));
v___x_1351_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v___x_1349_);
lean_ctor_set(v___x_1351_, 2, v___x_1348_);
lean_ctor_set(v___x_1351_, 3, v___x_1348_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object* v_s_1352_, lean_object* v_replacement_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1355_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1356_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1352_, v_replacement_1353_, v___x_1355_, v___x_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object* v_s_1357_, lean_object* v_replacement_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1357_, v_replacement_1358_);
lean_dec_ref(v_replacement_1358_);
return v_res_1359_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1));
v___x_1366_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1365_);
return v___x_1366_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2);
v___x_1369_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1));
v___x_1370_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v___x_1368_);
lean_ctor_set(v___x_1370_, 2, v___x_1367_);
lean_ctor_set(v___x_1370_, 3, v___x_1367_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(lean_object* v_s_1371_, lean_object* v_replacement_1372_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1374_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1375_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1371_, v_replacement_1372_, v___x_1374_, v___x_1373_);
return v___x_1375_;
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
lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg(){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___closed__0));
return v___x_1445_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1446_;
v_res_1446_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
stack->m_obj
 = v_res_1446_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___boxed(lean_object* v___dummy_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
return v_res_1448_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object* v_s_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object* v_s_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v_s_1452_);
lean_dec_ref(v_s_1452_);
return v_res_1453_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0));
v___x_1459_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1462_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0));
v___x_1463_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___x_1461_);
lean_ctor_set(v___x_1463_, 2, v___x_1460_);
lean_ctor_set(v___x_1463_, 3, v___x_1460_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object* v_s_1464_, lean_object* v_replacement_1465_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1467_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2);
v___x_1468_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1464_, v_replacement_1465_, v___x_1467_, v___x_1466_);
return v___x_1468_;
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
lean_object* v_currPos_1488_; lean_object* v_searcher_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1517_; 
v_currPos_1488_ = lean_ctor_get(v_a_1475_, 0);
v_searcher_1489_ = lean_ctor_get(v_a_1475_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_a_1475_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1491_ = v_a_1475_;
v_isShared_1492_ = v_isSharedCheck_1517_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_searcher_1489_);
lean_inc(v_currPos_1488_);
lean_dec(v_a_1475_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1517_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
uint8_t v_decide_1503_; 
v_decide_1503_ = lean_nat_dec_eq(v_searcher_1489_, v___x_1474_);
if (v_decide_1503_ == 0)
{
uint32_t v___x_1504_; uint32_t v___x_1505_; uint8_t v___x_1506_; 
v___x_1504_ = lean_string_utf8_get_fast(v_s_1472_, v_searcher_1489_);
v___x_1505_ = 32;
v___x_1506_ = lean_uint32_dec_eq(v___x_1504_, v___x_1505_);
if (v___x_1506_ == 0)
{
uint32_t v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = 9;
v___x_1508_ = lean_uint32_dec_eq(v___x_1504_, v___x_1507_);
if (v___x_1508_ == 0)
{
uint32_t v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = 13;
v___x_1510_ = lean_uint32_dec_eq(v___x_1504_, v___x_1509_);
if (v___x_1510_ == 0)
{
uint32_t v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = 10;
v___x_1512_ = lean_uint32_dec_eq(v___x_1504_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_del_object(v___x_1491_);
v___x_1513_ = lean_string_utf8_next_fast(v_s_1472_, v_searcher_1489_);
lean_dec(v_searcher_1489_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_currPos_1488_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v_a_1475_ = v___x_1514_;
goto _start;
}
else
{
goto v___jp_1493_;
}
}
else
{
goto v___jp_1493_;
}
}
else
{
goto v___jp_1493_;
}
}
else
{
goto v___jp_1493_;
}
}
else
{
lean_object* v___x_1516_; 
lean_del_object(v___x_1491_);
lean_dec(v_searcher_1489_);
v___x_1516_ = lean_box(1);
lean_inc(v___x_1474_);
v_it_1478_ = v___x_1516_;
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object* v_s_1518_, lean_object* v___x_1519_, lean_object* v___x_1520_, lean_object* v_a_1521_, lean_object* v_b_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1518_, v___x_1519_, v___x_1520_, v_a_1521_, v_b_1522_);
lean_dec_ref(v___x_1519_);
return v_res_1523_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t v_mode_1530_, lean_object* v_s_1531_){
_start:
{
switch(v_mode_1530_)
{
case 0:
{
return v_s_1531_;
}
case 1:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1532_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = lean_string_utf8_byte_size(v_s_1531_);
v___x_1535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1535_, 0, v_s_1531_);
lean_ctor_set(v___x_1535_, 1, v___x_1533_);
lean_ctor_set(v___x_1535_, 2, v___x_1534_);
v___x_1536_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v___x_1535_, v___x_1532_);
return v___x_1536_;
}
default: 
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0));
v___x_1539_ = lean_string_utf8_byte_size(v_s_1531_);
lean_inc_ref(v_s_1531_);
v___x_1540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1540_, 0, v_s_1531_);
lean_ctor_set(v___x_1540_, 1, v___x_1537_);
lean_ctor_set(v___x_1540_, 2, v___x_1539_);
v___x_1541_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0);
v___x_1542_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1));
v___x_1543_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1531_, v___x_1540_, v___x_1539_, v___x_1541_, v___x_1542_);
lean_dec_ref_known(v___x_1540_, 3);
v___x_1544_ = lean_array_to_list(v___x_1543_);
v___x_1545_ = l_String_Slice_intercalate(v___x_1538_, v___x_1544_);
lean_dec(v___x_1544_);
return v___x_1545_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_1530_ = stack[0].m_num;
lean_object* v_s_1531_ = stack[1].m_obj;
lean_object* v_res_1546_;
v_res_1546_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v_mode_1530_, v_s_1531_);
stack->m_obj
 = v_res_1546_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object* v_mode_1547_, lean_object* v_s_1548_){
_start:
{
uint8_t v_mode_boxed_1549_; lean_object* v_res_1550_; 
v_mode_boxed_1549_ = lean_unbox(v_mode_1547_);
v_res_1550_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v_mode_boxed_1549_, v_s_1548_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object* v_s_1551_, lean_object* v_pattern_1552_, lean_object* v_replacement_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1551_, v_replacement_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object* v_s_1555_, lean_object* v_pattern_1556_, lean_object* v_replacement_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(v_s_1555_, v_pattern_1556_, v_replacement_1557_);
lean_dec_ref(v_replacement_1557_);
lean_dec_ref(v_pattern_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object* v_s_1559_, lean_object* v___x_1560_, lean_object* v___x_1561_, lean_object* v_inst_1562_, lean_object* v_R_1563_, lean_object* v_a_1564_, lean_object* v_b_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1559_, v___x_1560_, v___x_1561_, v_a_1564_, v_b_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___boxed(lean_object* v_s_1567_, lean_object* v___x_1568_, lean_object* v___x_1569_, lean_object* v_inst_1570_, lean_object* v_R_1571_, lean_object* v_a_1572_, lean_object* v_b_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(v_s_1567_, v___x_1568_, v___x_1569_, v_inst_1570_, v_R_1571_, v_a_1572_, v_b_1573_);
lean_dec_ref(v___x_1568_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(lean_object* v_hi_1575_, lean_object* v_pivot_1576_, lean_object* v_as_1577_, lean_object* v_i_1578_, lean_object* v_k_1579_){
_start:
{
uint8_t v___x_1580_; 
v___x_1580_ = lean_nat_dec_lt(v_k_1579_, v_hi_1575_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec(v_k_1579_);
v___x_1581_ = lean_array_fswap(v_as_1577_, v_i_1578_, v_hi_1575_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v_i_1578_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
return v___x_1582_;
}
else
{
lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = lean_array_fget_borrowed(v_as_1577_, v_k_1579_);
v___x_1584_ = lean_string_dec_lt(v___x_1583_, v_pivot_1576_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_unsigned_to_nat(1u);
v___x_1586_ = lean_nat_add(v_k_1579_, v___x_1585_);
lean_dec(v_k_1579_);
v_k_1579_ = v___x_1586_;
goto _start;
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1588_ = lean_array_fswap(v_as_1577_, v_i_1578_, v_k_1579_);
v___x_1589_ = lean_unsigned_to_nat(1u);
v___x_1590_ = lean_nat_add(v_i_1578_, v___x_1589_);
lean_dec(v_i_1578_);
v___x_1591_ = lean_nat_add(v_k_1579_, v___x_1589_);
lean_dec(v_k_1579_);
v_as_1577_ = v___x_1588_;
v_i_1578_ = v___x_1590_;
v_k_1579_ = v___x_1591_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg___boxed(lean_object* v_hi_1593_, lean_object* v_pivot_1594_, lean_object* v_as_1595_, lean_object* v_i_1596_, lean_object* v_k_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1593_, v_pivot_1594_, v_as_1595_, v_i_1596_, v_k_1597_);
lean_dec_ref(v_pivot_1594_);
lean_dec(v_hi_1593_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object* v_n_1599_, lean_object* v_as_1600_, lean_object* v_lo_1601_, lean_object* v_hi_1602_){
_start:
{
lean_object* v___y_1604_; uint8_t v___x_1614_; 
v___x_1614_ = lean_nat_dec_lt(v_lo_1601_, v_hi_1602_);
if (v___x_1614_ == 0)
{
lean_dec(v_lo_1601_);
return v_as_1600_;
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_mid_1617_; lean_object* v___y_1619_; lean_object* v___y_1625_; lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1615_ = lean_nat_add(v_lo_1601_, v_hi_1602_);
v___x_1616_ = lean_unsigned_to_nat(1u);
v_mid_1617_ = lean_nat_shiftr(v___x_1615_, v___x_1616_);
lean_dec(v___x_1615_);
v___x_1630_ = lean_array_fget_borrowed(v_as_1600_, v_mid_1617_);
v___x_1631_ = lean_array_fget_borrowed(v_as_1600_, v_lo_1601_);
v___x_1632_ = lean_string_dec_lt(v___x_1630_, v___x_1631_);
if (v___x_1632_ == 0)
{
v___y_1625_ = v_as_1600_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_array_fswap(v_as_1600_, v_lo_1601_, v_mid_1617_);
v___y_1625_ = v___x_1633_;
goto v___jp_1624_;
}
v___jp_1618_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1620_ = lean_array_fget_borrowed(v___y_1619_, v_mid_1617_);
v___x_1621_ = lean_array_fget_borrowed(v___y_1619_, v_hi_1602_);
v___x_1622_ = lean_string_dec_lt(v___x_1620_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_dec(v_mid_1617_);
v___y_1604_ = v___y_1619_;
goto v___jp_1603_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_array_fswap(v___y_1619_, v_mid_1617_, v_hi_1602_);
lean_dec(v_mid_1617_);
v___y_1604_ = v___x_1623_;
goto v___jp_1603_;
}
}
v___jp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1626_ = lean_array_fget_borrowed(v___y_1625_, v_hi_1602_);
v___x_1627_ = lean_array_fget_borrowed(v___y_1625_, v_lo_1601_);
v___x_1628_ = lean_string_dec_lt(v___x_1626_, v___x_1627_);
if (v___x_1628_ == 0)
{
v___y_1619_ = v___y_1625_;
goto v___jp_1618_;
}
else
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_array_fswap(v___y_1625_, v_lo_1601_, v_hi_1602_);
v___y_1619_ = v___x_1629_;
goto v___jp_1618_;
}
}
}
v___jp_1603_:
{
lean_object* v_pivot_1605_; lean_object* v___x_1606_; lean_object* v_fst_1607_; lean_object* v_snd_1608_; uint8_t v___x_1609_; 
v_pivot_1605_ = lean_array_fget(v___y_1604_, v_hi_1602_);
lean_inc_n(v_lo_1601_, 2);
v___x_1606_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1602_, v_pivot_1605_, v___y_1604_, v_lo_1601_, v_lo_1601_);
lean_dec(v_pivot_1605_);
v_fst_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_fst_1607_);
v_snd_1608_ = lean_ctor_get(v___x_1606_, 1);
lean_inc(v_snd_1608_);
lean_dec_ref(v___x_1606_);
v___x_1609_ = lean_nat_dec_le(v_hi_1602_, v_fst_1607_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1610_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1599_, v_snd_1608_, v_lo_1601_, v_fst_1607_);
v___x_1611_ = lean_unsigned_to_nat(1u);
v___x_1612_ = lean_nat_add(v_fst_1607_, v___x_1611_);
lean_dec(v_fst_1607_);
v_as_1600_ = v___x_1610_;
v_lo_1601_ = v___x_1612_;
goto _start;
}
else
{
lean_dec(v_fst_1607_);
lean_dec(v_lo_1601_);
return v_snd_1608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object* v_n_1634_, lean_object* v_as_1635_, lean_object* v_lo_1636_, lean_object* v_hi_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1634_, v_as_1635_, v_lo_1636_, v_hi_1637_);
lean_dec(v_hi_1637_);
lean_dec(v_n_1634_);
return v_res_1638_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t v_mode_1639_, lean_object* v_msgs_1640_){
_start:
{
if (v_mode_1639_ == 0)
{
return v_msgs_1640_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1641_ = lean_array_mk(v_msgs_1640_);
v___x_1642_ = lean_array_get_size(v___x_1641_);
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = lean_nat_dec_eq(v___x_1642_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___y_1653_; uint8_t v___x_1655_; 
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = lean_nat_sub(v___x_1642_, v___x_1650_);
v___x_1655_ = lean_nat_dec_le(v___x_1648_, v___x_1651_);
if (v___x_1655_ == 0)
{
lean_inc(v___x_1651_);
v___y_1653_ = v___x_1651_;
goto v___jp_1652_;
}
else
{
v___y_1653_ = v___x_1648_;
goto v___jp_1652_;
}
v___jp_1652_:
{
uint8_t v___x_1654_; 
v___x_1654_ = lean_nat_dec_le(v___y_1653_, v___x_1651_);
if (v___x_1654_ == 0)
{
lean_dec(v___x_1651_);
lean_inc(v___y_1653_);
v___y_1644_ = v___y_1653_;
v___y_1645_ = v___y_1653_;
goto v___jp_1643_;
}
else
{
v___y_1644_ = v___y_1653_;
v___y_1645_ = v___x_1651_;
goto v___jp_1643_;
}
}
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_array_to_list(v___x_1641_);
return v___x_1656_;
}
v___jp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v___x_1642_, v___x_1641_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
v___x_1647_ = lean_array_to_list(v___x_1646_);
return v___x_1647_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_1639_ = stack[0].m_num;
lean_object* v_msgs_1640_ = stack[1].m_obj;
lean_object* v_res_1657_;
v_res_1657_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_1639_, v_msgs_1640_);
stack->m_obj
 = v_res_1657_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* v_mode_1658_, lean_object* v_msgs_1659_){
_start:
{
uint8_t v_mode_boxed_1660_; lean_object* v_res_1661_; 
v_mode_boxed_1660_ = lean_unbox(v_mode_1658_);
v_res_1661_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_boxed_1660_, v_msgs_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object* v_n_1662_, lean_object* v_as_1663_, lean_object* v_lo_1664_, lean_object* v_hi_1665_, lean_object* v_w_1666_, lean_object* v_hlo_1667_, lean_object* v_hhi_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1662_, v_as_1663_, v_lo_1664_, v_hi_1665_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object* v_n_1670_, lean_object* v_as_1671_, lean_object* v_lo_1672_, lean_object* v_hi_1673_, lean_object* v_w_1674_, lean_object* v_hlo_1675_, lean_object* v_hhi_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(v_n_1670_, v_as_1671_, v_lo_1672_, v_hi_1673_, v_w_1674_, v_hlo_1675_, v_hhi_1676_);
lean_dec(v_hi_1673_);
lean_dec(v_n_1670_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(lean_object* v_n_1678_, lean_object* v_lo_1679_, lean_object* v_hi_1680_, lean_object* v_hhi_1681_, lean_object* v_pivot_1682_, lean_object* v_as_1683_, lean_object* v_i_1684_, lean_object* v_k_1685_, lean_object* v_ilo_1686_, lean_object* v_ik_1687_, lean_object* v_w_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1680_, v_pivot_1682_, v_as_1683_, v_i_1684_, v_k_1685_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___boxed(lean_object* v_n_1690_, lean_object* v_lo_1691_, lean_object* v_hi_1692_, lean_object* v_hhi_1693_, lean_object* v_pivot_1694_, lean_object* v_as_1695_, lean_object* v_i_1696_, lean_object* v_k_1697_, lean_object* v_ilo_1698_, lean_object* v_ik_1699_, lean_object* v_w_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(v_n_1690_, v_lo_1691_, v_hi_1692_, v_hhi_1693_, v_pivot_1694_, v_as_1695_, v_i_1696_, v_k_1697_, v_ilo_1698_, v_ik_1699_, v_w_1700_);
lean_dec_ref(v_pivot_1694_);
lean_dec(v_hi_1692_);
lean_dec(v_lo_1691_);
lean_dec(v_n_1690_);
return v_res_1701_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object* v_as_1702_, size_t v_i_1703_, size_t v_stop_1704_, lean_object* v_b_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = lean_usize_dec_eq(v_i_1703_, v_stop_1704_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; lean_object* v_diagnostics_1708_; lean_object* v_msgLog_1709_; lean_object* v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; 
v___x_1707_ = lean_array_uget_borrowed(v_as_1702_, v_i_1703_);
v_diagnostics_1708_ = lean_ctor_get(v___x_1707_, 1);
v_msgLog_1709_ = lean_ctor_get(v_diagnostics_1708_, 0);
lean_inc_ref(v_msgLog_1709_);
v___x_1710_ = l_Lean_MessageLog_append(v_b_1705_, v_msgLog_1709_);
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_add(v_i_1703_, v___x_1711_);
v_i_1703_ = v___x_1712_;
v_b_1705_ = v___x_1710_;
goto _start;
}
else
{
return v_b_1705_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1702_ = stack[0].m_obj;
size_t v_i_1703_ = stack[1].m_num;
size_t v_stop_1704_ = stack[2].m_num;
lean_object* v_b_1705_ = stack[3].m_obj;
lean_object* v_res_1714_;
v_res_1714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v_as_1702_, v_i_1703_, v_stop_1704_, v_b_1705_);
stack->m_obj
 = v_res_1714_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object* v_as_1722_, size_t v_i_1723_, size_t v_stop_1724_, lean_object* v_b_1725_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1722_ = stack[0].m_obj;
size_t v_i_1723_ = stack[1].m_num;
size_t v_stop_1724_ = stack[2].m_num;
lean_object* v_b_1725_ = stack[3].m_obj;
lean_object* v_res_1750_;
v_res_1750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_as_1722_, v_i_1723_, v_stop_1724_, v_b_1725_);
stack->m_obj
 = v_res_1750_;
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
lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object* v_cmd_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
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
lean_dec_ref_known(v___x_1775_, 10);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1824_; 
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v___x_1776_, 0);
lean_dec(v_unused_1825_);
v___x_1778_ = v___x_1776_;
v_isShared_1779_ = v_isSharedCheck_1824_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v___x_1776_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1824_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_messages_1782_; lean_object* v___y_1784_; lean_object* v_snapshotTasks_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1780_ = lean_st_ref_get(v_a_1762_);
v___x_1781_ = lean_st_ref_get(v_a_1762_);
v_messages_1782_ = lean_ctor_get(v___x_1780_, 1);
lean_inc_ref(v_messages_1782_);
lean_dec(v___x_1780_);
v_snapshotTasks_1812_ = lean_ctor_get(v___x_1781_, 10);
lean_inc_ref(v_snapshotTasks_1812_);
lean_dec(v___x_1781_);
v___x_1813_ = l_Lean_MessageLog_empty;
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = lean_array_get_size(v_snapshotTasks_1812_);
v___x_1816_ = lean_nat_dec_lt(v___x_1814_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_dec_ref(v_snapshotTasks_1812_);
v___y_1784_ = v___x_1813_;
goto v___jp_1783_;
}
else
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_nat_dec_le(v___x_1815_, v___x_1815_);
if (v___x_1817_ == 0)
{
if (v___x_1816_ == 0)
{
lean_dec_ref(v_snapshotTasks_1812_);
v___y_1784_ = v___x_1813_;
goto v___jp_1783_;
}
else
{
size_t v___x_1818_; size_t v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = ((size_t)0ULL);
v___x_1819_ = lean_usize_of_nat(v___x_1815_);
v___x_1820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1812_, v___x_1818_, v___x_1819_, v___x_1813_);
lean_dec_ref(v_snapshotTasks_1812_);
v___y_1784_ = v___x_1820_;
goto v___jp_1783_;
}
}
else
{
size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = ((size_t)0ULL);
v___x_1822_ = lean_usize_of_nat(v___x_1815_);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1812_, v___x_1821_, v___x_1822_, v___x_1813_);
lean_dec_ref(v_snapshotTasks_1812_);
v___y_1784_ = v___x_1823_;
goto v___jp_1783_;
}
}
v___jp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v_env_1787_; lean_object* v_messages_1788_; lean_object* v_scopes_1789_; lean_object* v_usedQuotCtxts_1790_; lean_object* v_nextMacroScope_1791_; lean_object* v_maxRecDepth_1792_; lean_object* v_ngen_1793_; lean_object* v_auxDeclNGen_1794_; lean_object* v_infoState_1795_; lean_object* v_traceState_1796_; lean_object* v_prevLinterStates_1797_; lean_object* v_codeQualityEntryTasks_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1810_; 
v___x_1785_ = l_Lean_MessageLog_append(v_messages_1782_, v___y_1784_);
v___x_1786_ = lean_st_ref_take(v_a_1762_);
v_env_1787_ = lean_ctor_get(v___x_1786_, 0);
v_messages_1788_ = lean_ctor_get(v___x_1786_, 1);
v_scopes_1789_ = lean_ctor_get(v___x_1786_, 2);
v_usedQuotCtxts_1790_ = lean_ctor_get(v___x_1786_, 3);
v_nextMacroScope_1791_ = lean_ctor_get(v___x_1786_, 4);
v_maxRecDepth_1792_ = lean_ctor_get(v___x_1786_, 5);
v_ngen_1793_ = lean_ctor_get(v___x_1786_, 6);
v_auxDeclNGen_1794_ = lean_ctor_get(v___x_1786_, 7);
v_infoState_1795_ = lean_ctor_get(v___x_1786_, 8);
v_traceState_1796_ = lean_ctor_get(v___x_1786_, 9);
v_prevLinterStates_1797_ = lean_ctor_get(v___x_1786_, 11);
v_codeQualityEntryTasks_1798_ = lean_ctor_get(v___x_1786_, 12);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; 
v_unused_1811_ = lean_ctor_get(v___x_1786_, 10);
lean_dec(v_unused_1811_);
v___x_1800_ = v___x_1786_;
v_isShared_1801_ = v_isSharedCheck_1810_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1798_);
lean_inc(v_prevLinterStates_1797_);
lean_inc(v_traceState_1796_);
lean_inc(v_infoState_1795_);
lean_inc(v_auxDeclNGen_1794_);
lean_inc(v_ngen_1793_);
lean_inc(v_maxRecDepth_1792_);
lean_inc(v_nextMacroScope_1791_);
lean_inc(v_usedQuotCtxts_1790_);
lean_inc(v_scopes_1789_);
lean_inc(v_messages_1788_);
lean_inc(v_env_1787_);
lean_dec(v___x_1786_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1810_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 10, v___x_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_env_1787_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_messages_1788_);
lean_ctor_set(v_reuseFailAlloc_1809_, 2, v_scopes_1789_);
lean_ctor_set(v_reuseFailAlloc_1809_, 3, v_usedQuotCtxts_1790_);
lean_ctor_set(v_reuseFailAlloc_1809_, 4, v_nextMacroScope_1791_);
lean_ctor_set(v_reuseFailAlloc_1809_, 5, v_maxRecDepth_1792_);
lean_ctor_set(v_reuseFailAlloc_1809_, 6, v_ngen_1793_);
lean_ctor_set(v_reuseFailAlloc_1809_, 7, v_auxDeclNGen_1794_);
lean_ctor_set(v_reuseFailAlloc_1809_, 8, v_infoState_1795_);
lean_ctor_set(v_reuseFailAlloc_1809_, 9, v_traceState_1796_);
lean_ctor_set(v_reuseFailAlloc_1809_, 10, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1809_, 11, v_prevLinterStates_1797_);
lean_ctor_set(v_reuseFailAlloc_1809_, 12, v_codeQualityEntryTasks_1798_);
v___x_1804_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1805_ = lean_st_ref_put(v_a_1762_, v___x_1804_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1785_);
v___x_1807_ = v___x_1778_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1785_);
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
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
v_a_1826_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1776_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1776_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmd_1760_ = stack[0].m_obj;
lean_object* v_a_1761_ = stack[1].m_obj;
lean_object* v_a_1762_ = stack[2].m_obj;
lean_object* v_res_1834_;
v_res_1834_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1760_, v_a_1761_, v_a_1762_);
stack->m_obj
 = v_res_1834_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1835_, v_a_1836_, v_a_1837_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
return v_res_1839_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1840_, lean_object* v_opt_1841_){
_start:
{
lean_object* v_name_1842_; lean_object* v_defValue_1843_; lean_object* v_map_1844_; lean_object* v___x_1845_; 
v_name_1842_ = lean_ctor_get(v_opt_1841_, 0);
v_defValue_1843_ = lean_ctor_get(v_opt_1841_, 1);
v_map_1844_ = lean_ctor_get(v_opts_1840_, 0);
v___x_1845_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1844_, v_name_1842_);
if (lean_obj_tag(v___x_1845_) == 0)
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_unbox(v_defValue_1843_);
return v___x_1846_;
}
else
{
lean_object* v_val_1847_; 
v_val_1847_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_val_1847_);
lean_dec_ref_known(v___x_1845_, 1);
if (lean_obj_tag(v_val_1847_) == 1)
{
uint8_t v_v_1848_; 
v_v_1848_ = lean_ctor_get_uint8(v_val_1847_, 0);
lean_dec_ref_known(v_val_1847_, 0);
return v_v_1848_;
}
else
{
uint8_t v___x_1849_; 
lean_dec(v_val_1847_);
v___x_1849_ = lean_unbox(v_defValue_1843_);
return v___x_1849_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1840_ = stack[0].m_obj;
lean_object* v_opt_1841_ = stack[1].m_obj;
uint8_t v_res_1850_;
v_res_1850_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1840_, v_opt_1841_);
stack->m_num = v_res_1850_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1851_, lean_object* v_opt_1852_){
_start:
{
uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_res_1853_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1851_, v_opt_1852_);
lean_dec_ref(v_opt_1852_);
lean_dec_ref(v_opts_1851_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg(){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___closed__0));
return v___x_1858_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1859_;
v_res_1859_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
stack->m_obj
 = v_res_1859_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___boxed(lean_object* v___dummy_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v_res_1861_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1865_);
lean_dec_ref(v_s_1865_);
return v_res_1866_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_box(1);
v___x_1868_ = l_Lean_MessageData_ofFormat(v___x_1867_);
return v___x_1868_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1873_ = l_Lean_MessageData_ofFormat(v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
return v_x_1874_;
}
else
{
lean_object* v_head_1876_; lean_object* v_tail_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1899_; 
v_head_1876_ = lean_ctor_get(v_x_1875_, 0);
v_tail_1877_ = lean_ctor_get(v_x_1875_, 1);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1879_ = v_x_1875_;
v_isShared_1880_ = v_isSharedCheck_1899_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_tail_1877_);
lean_inc(v_head_1876_);
lean_dec(v_x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1899_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_before_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1897_; 
v_before_1881_ = lean_ctor_get(v_head_1876_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_head_1876_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v_head_1876_, 1);
lean_dec(v_unused_1898_);
v___x_1883_ = v_head_1876_;
v_isShared_1884_ = v_isSharedCheck_1897_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_before_1881_);
lean_dec(v_head_1876_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1897_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 7);
lean_ctor_set(v___x_1883_, 1, v___x_1885_);
lean_ctor_set(v___x_1883_, 0, v_x_1874_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_x_1874_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 7);
lean_ctor_set(v___x_1879_, 1, v___x_1888_);
lean_ctor_set(v___x_1879_, 0, v___x_1887_);
v___x_1890_ = v___x_1879_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = l_Lean_MessageData_ofSyntax(v_before_1881_);
v___x_1892_ = l_Lean_indentD(v___x_1891_);
v___x_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1890_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v_x_1874_ = v___x_1893_;
v_x_1875_ = v_tail_1877_;
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
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1904_ = l_Lean_MessageData_ofFormat(v___x_1903_);
return v___x_1904_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1905_, lean_object* v_macroStack_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_scopes_1911_; lean_object* v___x_1912_; lean_object* v_opts_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1909_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1910_ = lean_st_ref_get(v___y_1907_);
v_scopes_1911_ = lean_ctor_get(v___x_1910_, 2);
lean_inc(v_scopes_1911_);
lean_dec(v___x_1910_);
v___x_1912_ = l_List_head_x21___redArg(v___x_1909_, v_scopes_1911_);
lean_dec(v_scopes_1911_);
v_opts_1913_ = lean_ctor_get(v___x_1912_, 1);
lean_inc_ref(v_opts_1913_);
lean_dec(v___x_1912_);
v___x_1914_ = l_Lean_Elab_pp_macroStack;
v___x_1915_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1913_, v___x_1914_);
lean_dec_ref(v_opts_1913_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; 
lean_dec(v_macroStack_1906_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_msgData_1905_);
return v___x_1916_;
}
else
{
if (lean_obj_tag(v_macroStack_1906_) == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_msgData_1905_);
return v___x_1917_;
}
else
{
lean_object* v_head_1918_; lean_object* v_after_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1934_; 
v_head_1918_ = lean_ctor_get(v_macroStack_1906_, 0);
lean_inc(v_head_1918_);
v_after_1919_ = lean_ctor_get(v_head_1918_, 1);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_head_1918_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v_head_1918_, 0);
lean_dec(v_unused_1935_);
v___x_1921_ = v_head_1918_;
v_isShared_1922_ = v_isSharedCheck_1934_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_after_1919_);
lean_dec(v_head_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1934_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 7);
lean_ctor_set(v___x_1921_, 1, v___x_1923_);
lean_ctor_set(v___x_1921_, 0, v_msgData_1905_);
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_msgData_1905_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v_msgData_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1926_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = l_Lean_MessageData_ofSyntax(v_after_1919_);
v___x_1929_ = l_Lean_indentD(v___x_1928_);
v_msgData_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1930_, 0, v___x_1927_);
lean_ctor_set(v_msgData_1930_, 1, v___x_1929_);
v___x_1931_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1930_, v_macroStack_1906_);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1905_ = stack[0].m_obj;
lean_object* v_macroStack_1906_ = stack[1].m_obj;
lean_object* v___y_1907_ = stack[2].m_obj;
lean_object* v_res_1936_;
v_res_1936_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1905_, v_macroStack_1906_, v___y_1907_);
stack->m_obj
 = v_res_1936_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1937_, lean_object* v_macroStack_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1937_, v_macroStack_1938_, v___y_1939_);
lean_dec(v___y_1939_);
return v_res_1941_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1945_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1946_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
lean_ctor_set(v___x_1948_, 2, v___x_1947_);
lean_ctor_set(v___x_1948_, 3, v___x_1947_);
lean_ctor_set(v___x_1948_, 4, v___x_1946_);
lean_ctor_set(v___x_1948_, 5, v___x_1946_);
lean_ctor_set(v___x_1948_, 6, v___x_1946_);
lean_ctor_set(v___x_1948_, 7, v___x_1946_);
lean_ctor_set(v___x_1948_, 8, v___x_1946_);
lean_ctor_set(v___x_1948_, 9, v___x_1946_);
lean_ctor_set(v___x_1948_, 10, v___x_1946_);
lean_ctor_set(v___x_1948_, 11, v___x_1945_);
return v___x_1948_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1949_ = lean_unsigned_to_nat(32u);
v___x_1950_ = lean_mk_empty_array_with_capacity(v___x_1949_);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1952_ = ((size_t)5ULL);
v___x_1953_ = lean_unsigned_to_nat(0u);
v___x_1954_ = lean_unsigned_to_nat(32u);
v___x_1955_ = lean_mk_empty_array_with_capacity(v___x_1954_);
v___x_1956_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1957_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
lean_ctor_set(v___x_1957_, 1, v___x_1955_);
lean_ctor_set(v___x_1957_, 2, v___x_1953_);
lean_ctor_set(v___x_1957_, 3, v___x_1953_);
lean_ctor_set_usize(v___x_1957_, 4, v___x_1952_);
return v___x_1957_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1958_ = lean_box(1);
v___x_1959_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1960_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v___x_1959_);
lean_ctor_set(v___x_1961_, 2, v___x_1958_);
return v___x_1961_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v_env_1966_; uint8_t v___x_1967_; lean_object* v_env_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v_scopes_1971_; lean_object* v___x_1972_; lean_object* v_opts_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1965_ = lean_st_ref_get(v___y_1963_);
v_env_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc_ref(v_env_1966_);
lean_dec(v___x_1965_);
v___x_1967_ = 0;
v_env_1968_ = l_Lean_Environment_setRecordingDeps(v_env_1966_, v___x_1967_);
v___x_1969_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1970_ = lean_st_ref_get(v___y_1963_);
v_scopes_1971_ = lean_ctor_get(v___x_1970_, 2);
lean_inc(v_scopes_1971_);
lean_dec(v___x_1970_);
v___x_1972_ = l_List_head_x21___redArg(v___x_1969_, v_scopes_1971_);
lean_dec(v_scopes_1971_);
v_opts_1973_ = lean_ctor_get(v___x_1972_, 1);
lean_inc_ref(v_opts_1973_);
lean_dec(v___x_1972_);
v___x_1974_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1975_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1976_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1976_, 0, v_env_1968_);
lean_ctor_set(v___x_1976_, 1, v___x_1974_);
lean_ctor_set(v___x_1976_, 2, v___x_1975_);
lean_ctor_set(v___x_1976_, 3, v_opts_1973_);
v___x_1977_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v_msgData_1962_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1962_ = stack[0].m_obj;
lean_object* v___y_1963_ = stack[1].m_obj;
lean_object* v_res_1979_;
v_res_1979_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1962_, v___y_1963_);
stack->m_obj
 = v_res_1979_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1980_, v___y_1981_);
lean_dec(v___y_1981_);
return v_res_1983_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_Elab_Command_getRef___redArg(v___y_1985_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v_macroStack_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v_a_1993_; lean_object* v___x_1994_; lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2003_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v_macroStack_1990_ = lean_ctor_get(v___y_1985_, 4);
v___x_1991_ = l_Lean_Elab_getBetterRef(v_a_1989_, v_macroStack_1990_);
lean_dec(v_a_1989_);
v___x_1992_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1984_, v___y_1986_);
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref(v___x_1992_);
lean_inc(v_macroStack_1990_);
v___x_1994_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1993_, v_macroStack_1990_, v___y_1986_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1991_);
lean_ctor_set(v___x_1999_, 1, v_a_1995_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 1);
lean_ctor_set(v___x_1997_, 0, v___x_1999_);
v___x_2001_ = v___x_1997_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v_msg_1984_);
v_a_2004_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1988_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1988_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1984_ = stack[0].m_obj;
lean_object* v___y_1985_ = stack[1].m_obj;
lean_object* v___y_1986_ = stack[2].m_obj;
lean_object* v_res_2012_;
v_res_2012_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1984_, v___y_1985_, v___y_1986_);
stack->m_obj
 = v_res_2012_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
return v_res_2017_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_2018_, lean_object* v_msg_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_Elab_Command_getRef___redArg(v___y_2020_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v_fileName_2025_; lean_object* v_fileMap_2026_; lean_object* v_currRecDepth_2027_; lean_object* v_cmdPos_2028_; lean_object* v_macroStack_2029_; lean_object* v_quotContext_x3f_2030_; lean_object* v_currMacroScope_2031_; lean_object* v_snap_x3f_2032_; lean_object* v_cancelTk_x3f_2033_; uint8_t v_suppressElabErrors_2034_; lean_object* v_ref_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v_fileName_2025_ = lean_ctor_get(v___y_2020_, 0);
v_fileMap_2026_ = lean_ctor_get(v___y_2020_, 1);
v_currRecDepth_2027_ = lean_ctor_get(v___y_2020_, 2);
v_cmdPos_2028_ = lean_ctor_get(v___y_2020_, 3);
v_macroStack_2029_ = lean_ctor_get(v___y_2020_, 4);
v_quotContext_x3f_2030_ = lean_ctor_get(v___y_2020_, 5);
v_currMacroScope_2031_ = lean_ctor_get(v___y_2020_, 6);
v_snap_x3f_2032_ = lean_ctor_get(v___y_2020_, 8);
v_cancelTk_x3f_2033_ = lean_ctor_get(v___y_2020_, 9);
v_suppressElabErrors_2034_ = lean_ctor_get_uint8(v___y_2020_, sizeof(void*)*10);
v_ref_2035_ = l_Lean_replaceRef(v_ref_2018_, v_a_2024_);
lean_dec(v_a_2024_);
lean_inc(v_cancelTk_x3f_2033_);
lean_inc(v_snap_x3f_2032_);
lean_inc(v_currMacroScope_2031_);
lean_inc(v_quotContext_x3f_2030_);
lean_inc(v_macroStack_2029_);
lean_inc(v_cmdPos_2028_);
lean_inc(v_currRecDepth_2027_);
lean_inc_ref(v_fileMap_2026_);
lean_inc_ref(v_fileName_2025_);
v___x_2036_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2036_, 0, v_fileName_2025_);
lean_ctor_set(v___x_2036_, 1, v_fileMap_2026_);
lean_ctor_set(v___x_2036_, 2, v_currRecDepth_2027_);
lean_ctor_set(v___x_2036_, 3, v_cmdPos_2028_);
lean_ctor_set(v___x_2036_, 4, v_macroStack_2029_);
lean_ctor_set(v___x_2036_, 5, v_quotContext_x3f_2030_);
lean_ctor_set(v___x_2036_, 6, v_currMacroScope_2031_);
lean_ctor_set(v___x_2036_, 7, v_ref_2035_);
lean_ctor_set(v___x_2036_, 8, v_snap_x3f_2032_);
lean_ctor_set(v___x_2036_, 9, v_cancelTk_x3f_2033_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*10, v_suppressElabErrors_2034_);
v___x_2037_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_2019_, v___x_2036_, v___y_2021_);
lean_dec_ref_known(v___x_2036_, 10);
return v___x_2037_;
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_msg_2019_);
v_a_2038_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2023_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2023_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2018_ = stack[0].m_obj;
lean_object* v_msg_2019_ = stack[1].m_obj;
lean_object* v___y_2020_ = stack[2].m_obj;
lean_object* v___y_2021_ = stack[3].m_obj;
lean_object* v_res_2046_;
v_res_2046_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_2018_, v_msg_2019_, v___y_2020_, v___y_2021_);
stack->m_obj
 = v_res_2046_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_2047_, lean_object* v_msg_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_2047_, v_msg_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v_ref_2047_);
return v_res_2052_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_2055_ = l_Lean_stringToMessageData(v___x_2054_);
return v___x_2055_;
}
}
lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_unsigned_to_nat(1u);
v___x_2070_ = l_Lean_Syntax_getArg(v_stx_2059_, v___x_2069_);
if (lean_obj_tag(v___x_2070_) == 1)
{
lean_object* v_kind_2071_; 
v_kind_2071_ = lean_ctor_get(v___x_2070_, 1);
lean_inc(v_kind_2071_);
if (lean_obj_tag(v_kind_2071_) == 1)
{
lean_object* v_pre_2072_; 
v_pre_2072_ = lean_ctor_get(v_kind_2071_, 0);
lean_inc(v_pre_2072_);
if (lean_obj_tag(v_pre_2072_) == 1)
{
lean_object* v_pre_2073_; 
v_pre_2073_ = lean_ctor_get(v_pre_2072_, 0);
lean_inc(v_pre_2073_);
if (lean_obj_tag(v_pre_2073_) == 1)
{
lean_object* v_pre_2074_; 
v_pre_2074_ = lean_ctor_get(v_pre_2073_, 0);
lean_inc(v_pre_2074_);
if (lean_obj_tag(v_pre_2074_) == 1)
{
lean_object* v_pre_2075_; 
v_pre_2075_ = lean_ctor_get(v_pre_2074_, 0);
if (lean_obj_tag(v_pre_2075_) == 0)
{
lean_object* v_args_2076_; lean_object* v_str_2077_; lean_object* v_str_2078_; lean_object* v_str_2079_; lean_object* v_str_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_args_2076_ = lean_ctor_get(v___x_2070_, 2);
lean_inc_ref(v_args_2076_);
lean_dec_ref_known(v___x_2070_, 3);
v_str_2077_ = lean_ctor_get(v_kind_2071_, 1);
lean_inc_ref(v_str_2077_);
lean_dec_ref_known(v_kind_2071_, 2);
v_str_2078_ = lean_ctor_get(v_pre_2072_, 1);
lean_inc_ref(v_str_2078_);
lean_dec_ref_known(v_pre_2072_, 2);
v_str_2079_ = lean_ctor_get(v_pre_2073_, 1);
lean_inc_ref(v_str_2079_);
lean_dec_ref_known(v_pre_2073_, 2);
v_str_2080_ = lean_ctor_get(v_pre_2074_, 1);
lean_inc_ref(v_str_2080_);
lean_dec_ref_known(v_pre_2074_, 2);
v___x_2081_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_2082_ = lean_string_dec_eq(v_str_2080_, v___x_2081_);
lean_dec_ref(v_str_2080_);
if (v___x_2082_ == 0)
{
lean_dec_ref(v_str_2079_);
lean_dec_ref(v_str_2078_);
lean_dec_ref(v_str_2077_);
lean_dec_ref(v_args_2076_);
goto v___jp_2063_;
}
else
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2084_ = lean_string_dec_eq(v_str_2079_, v___x_2083_);
lean_dec_ref(v_str_2079_);
if (v___x_2084_ == 0)
{
lean_dec_ref(v_str_2078_);
lean_dec_ref(v_str_2077_);
lean_dec_ref(v_args_2076_);
goto v___jp_2063_;
}
else
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2086_ = lean_string_dec_eq(v_str_2078_, v___x_2085_);
lean_dec_ref(v_str_2078_);
if (v___x_2086_ == 0)
{
lean_dec_ref(v_str_2077_);
lean_dec_ref(v_args_2076_);
goto v___jp_2063_;
}
else
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2088_ = lean_string_dec_eq(v_str_2077_, v___x_2087_);
lean_dec_ref(v_str_2077_);
if (v___x_2088_ == 0)
{
lean_dec_ref(v_args_2076_);
goto v___jp_2063_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2089_ = lean_array_get_size(v_args_2076_);
v___x_2090_ = lean_unsigned_to_nat(2u);
v___x_2091_ = lean_nat_dec_eq(v___x_2089_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_dec_ref(v_args_2076_);
goto v___jp_2063_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = lean_unsigned_to_nat(0u);
v___x_2093_ = lean_array_fget(v_args_2076_, v___x_2092_);
lean_dec_ref(v_args_2076_);
if (lean_obj_tag(v___x_2093_) == 2)
{
lean_object* v_val_2094_; lean_object* v___x_2095_; 
lean_dec(v_stx_2059_);
v_val_2094_ = lean_ctor_get(v___x_2093_, 1);
lean_inc_ref(v_val_2094_);
lean_dec_ref_known(v___x_2093_, 2);
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v_val_2094_);
return v___x_2095_;
}
else
{
lean_dec(v___x_2093_);
goto v___jp_2063_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2074_, 2);
lean_dec_ref_known(v_pre_2073_, 2);
lean_dec_ref_known(v_pre_2072_, 2);
lean_dec_ref_known(v_kind_2071_, 2);
lean_dec_ref_known(v___x_2070_, 3);
goto v___jp_2063_;
}
}
else
{
lean_dec_ref_known(v_pre_2073_, 2);
lean_dec(v_pre_2074_);
lean_dec_ref_known(v_pre_2072_, 2);
lean_dec_ref_known(v_kind_2071_, 2);
lean_dec_ref_known(v___x_2070_, 3);
goto v___jp_2063_;
}
}
else
{
lean_dec(v_pre_2073_);
lean_dec_ref_known(v_pre_2072_, 2);
lean_dec_ref_known(v_kind_2071_, 2);
lean_dec_ref_known(v___x_2070_, 3);
goto v___jp_2063_;
}
}
else
{
lean_dec_ref_known(v_kind_2071_, 2);
lean_dec(v_pre_2072_);
lean_dec_ref_known(v___x_2070_, 3);
goto v___jp_2063_;
}
}
else
{
lean_dec(v_kind_2071_);
lean_dec_ref_known(v___x_2070_, 3);
goto v___jp_2063_;
}
}
else
{
lean_dec(v___x_2070_);
goto v___jp_2063_;
}
v___jp_2063_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2064_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2059_);
v___x_2065_ = l_Lean_MessageData_ofSyntax(v_stx_2059_);
v___x_2066_ = l_Lean_indentD(v___x_2065_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2064_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2059_, v___x_2067_, v___y_2060_, v___y_2061_);
lean_dec(v_stx_2059_);
return v___x_2068_;
}
}
}
LEAN_EXPORT void l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2059_ = stack[0].m_obj;
lean_object* v___y_2060_ = stack[1].m_obj;
lean_object* v___y_2061_ = stack[2].m_obj;
lean_object* v_res_2096_;
v_res_2096_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2059_, v___y_2060_, v___y_2061_);
stack->m_obj
 = v_res_2096_;
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
return v_res_2101_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2102_, size_t v_sz_2103_, size_t v_i_2104_, lean_object* v_b_2105_){
_start:
{
lean_object* v_a_2107_; uint8_t v___x_2111_; 
v___x_2111_ = lean_usize_dec_lt(v_i_2104_, v_sz_2103_);
if (v___x_2111_ == 0)
{
return v_b_2105_;
}
else
{
lean_object* v_a_2112_; lean_object* v_fst_2113_; lean_object* v_snd_2114_; lean_object* v_out_2115_; uint8_t v___x_2116_; 
v_a_2112_ = lean_array_uget_borrowed(v_as_2102_, v_i_2104_);
v_fst_2113_ = lean_ctor_get(v_a_2112_, 0);
v_snd_2114_ = lean_ctor_get(v_a_2112_, 1);
v_out_2115_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2116_ = lean_string_dec_eq(v_snd_2114_, v_out_2115_);
if (v___x_2116_ == 0)
{
uint8_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2117_ = lean_unbox(v_fst_2113_);
v___x_2118_ = l_Lean_Diff_Action_linePrefix(v___x_2117_);
v___x_2119_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2120_ = lean_string_append(v___x_2118_, v___x_2119_);
v___x_2121_ = lean_string_append(v___x_2120_, v_snd_2114_);
v___x_2122_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2123_ = lean_string_append(v___x_2121_, v___x_2122_);
v___x_2124_ = lean_string_append(v_b_2105_, v___x_2123_);
lean_dec_ref(v___x_2123_);
v_a_2107_ = v___x_2124_;
goto v___jp_2106_;
}
else
{
uint8_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2125_ = lean_unbox(v_fst_2113_);
v___x_2126_ = l_Lean_Diff_Action_linePrefix(v___x_2125_);
v___x_2127_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2128_ = lean_string_append(v___x_2126_, v___x_2127_);
v___x_2129_ = lean_string_append(v_b_2105_, v___x_2128_);
lean_dec_ref(v___x_2128_);
v_a_2107_ = v___x_2129_;
goto v___jp_2106_;
}
}
v___jp_2106_:
{
size_t v___x_2108_; size_t v___x_2109_; 
v___x_2108_ = ((size_t)1ULL);
v___x_2109_ = lean_usize_add(v_i_2104_, v___x_2108_);
v_i_2104_ = v___x_2109_;
v_b_2105_ = v_a_2107_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2102_ = stack[0].m_obj;
size_t v_sz_2103_ = stack[1].m_num;
size_t v_i_2104_ = stack[2].m_num;
lean_object* v_b_2105_ = stack[3].m_obj;
lean_object* v_res_2130_;
v_res_2130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2102_, v_sz_2103_, v_i_2104_, v_b_2105_);
stack->m_obj
 = v_res_2130_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2131_, lean_object* v_sz_2132_, lean_object* v_i_2133_, lean_object* v_b_2134_){
_start:
{
size_t v_sz_boxed_2135_; size_t v_i_boxed_2136_; lean_object* v_res_2137_; 
v_sz_boxed_2135_ = lean_unbox_usize(v_sz_2132_);
lean_dec(v_sz_2132_);
v_i_boxed_2136_ = lean_unbox_usize(v_i_2133_);
lean_dec(v_i_2133_);
v_res_2137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2131_, v_sz_boxed_2135_, v_i_boxed_2136_, v_b_2134_);
lean_dec_ref(v_as_2131_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2138_){
_start:
{
lean_object* v_out_2139_; size_t v_sz_2140_; size_t v___x_2141_; lean_object* v___x_2142_; 
v_out_2139_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v_sz_2140_ = lean_array_size(v_lines_2138_);
v___x_2141_ = ((size_t)0ULL);
v___x_2142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2138_, v_sz_2140_, v___x_2141_, v_out_2139_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2143_);
lean_dec_ref(v_lines_2143_);
return v_res_2144_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2145_, lean_object* v_as_x27_2146_, lean_object* v_b_2147_){
_start:
{
if (lean_obj_tag(v_as_x27_2146_) == 0)
{
lean_object* v___x_2149_; 
lean_dec_ref(v_filterFn_2145_);
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v_b_2147_);
return v___x_2149_;
}
else
{
lean_object* v_head_2150_; uint8_t v_isSilent_2151_; 
v_head_2150_ = lean_ctor_get(v_as_x27_2146_, 0);
v_isSilent_2151_ = lean_ctor_get_uint8(v_head_2150_, sizeof(void*)*5 + 2);
if (v_isSilent_2151_ == 0)
{
lean_object* v_tail_2152_; lean_object* v_fst_2153_; lean_object* v_snd_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2174_; 
v_tail_2152_ = lean_ctor_get(v_as_x27_2146_, 1);
v_fst_2153_ = lean_ctor_get(v_b_2147_, 0);
v_snd_2154_ = lean_ctor_get(v_b_2147_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_b_2147_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2156_ = v_b_2147_;
v_isShared_2157_ = v_isSharedCheck_2174_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_snd_2154_);
lean_inc(v_fst_2153_);
lean_dec(v_b_2147_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2174_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; uint8_t v___x_2159_; 
lean_inc_ref(v_filterFn_2145_);
lean_inc(v_head_2150_);
v___x_2158_ = lean_apply_1(v_filterFn_2145_, v_head_2150_);
v___x_2159_ = lean_unbox(v___x_2158_);
switch(v___x_2159_)
{
case 0:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
lean_inc(v_head_2150_);
v___x_2160_ = l_Lean_MessageLog_add(v_head_2150_, v_fst_2153_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2160_);
v___x_2162_ = v___x_2156_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_snd_2154_);
v___x_2162_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
v_as_x27_2146_ = v_tail_2152_;
v_b_2147_ = v___x_2162_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2166_; 
if (v_isShared_2157_ == 0)
{
v___x_2166_ = v___x_2156_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_fst_2153_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_snd_2154_);
v___x_2166_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
v_as_x27_2146_ = v_tail_2152_;
v_b_2147_ = v___x_2166_;
goto _start;
}
}
default: 
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
lean_inc(v_head_2150_);
v___x_2169_ = l_Lean_MessageLog_add(v_head_2150_, v_snd_2154_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v___x_2169_);
v___x_2171_ = v___x_2156_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_fst_2153_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
v_as_x27_2146_ = v_tail_2152_;
v_b_2147_ = v___x_2171_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2175_; lean_object* v_fst_2176_; lean_object* v_snd_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2185_; 
v_tail_2175_ = lean_ctor_get(v_as_x27_2146_, 1);
v_fst_2176_ = lean_ctor_get(v_b_2147_, 0);
v_snd_2177_ = lean_ctor_get(v_b_2147_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_b_2147_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2179_ = v_b_2147_;
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_snd_2177_);
lean_inc(v_fst_2176_);
lean_dec(v_b_2147_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_fst_2176_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_snd_2177_);
v___x_2182_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
v_as_x27_2146_ = v_tail_2175_;
v_b_2147_ = v___x_2182_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_filterFn_2145_ = stack[0].m_obj;
lean_object* v_as_x27_2146_ = stack[1].m_obj;
lean_object* v_b_2147_ = stack[2].m_obj;
lean_object* v_res_2186_;
v_res_2186_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2145_, v_as_x27_2146_, v_b_2147_);
stack->m_obj
 = v_res_2186_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2187_, lean_object* v_as_x27_2188_, lean_object* v_b_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2187_, v_as_x27_2188_, v_b_2189_);
lean_dec(v_as_x27_2188_);
return v_res_2191_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2192_, lean_object* v_a_2193_, uint8_t v_b_2194_){
_start:
{
uint8_t v___x_2195_; 
v___x_2195_ = 0;
switch(lean_obj_tag(v_a_2193_))
{
case 0:
{
lean_object* v_pos_2196_; lean_object* v_startInclusive_2197_; lean_object* v_endExclusive_2198_; lean_object* v___x_2199_; uint8_t v_decide_2200_; 
v_pos_2196_ = lean_ctor_get(v_a_2193_, 0);
lean_inc(v_pos_2196_);
lean_dec_ref_known(v_a_2193_, 1);
v_startInclusive_2197_ = lean_ctor_get(v_s_2192_, 1);
v_endExclusive_2198_ = lean_ctor_get(v_s_2192_, 2);
v___x_2199_ = lean_nat_sub(v_endExclusive_2198_, v_startInclusive_2197_);
v_decide_2200_ = lean_nat_dec_eq(v_pos_2196_, v___x_2199_);
lean_dec(v___x_2199_);
lean_dec(v_pos_2196_);
if (v_decide_2200_ == 0)
{
uint8_t v___x_2201_; 
v___x_2201_ = 1;
return v___x_2201_;
}
else
{
return v_decide_2200_;
}
}
case 1:
{
lean_object* v_pos_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2215_; 
v_pos_2202_ = lean_ctor_get(v_a_2193_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_a_2193_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2204_ = v_a_2193_;
v_isShared_2205_ = v_isSharedCheck_2215_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_pos_2202_);
lean_dec(v_a_2193_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2215_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_str_2206_; lean_object* v_startInclusive_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v_str_2206_ = lean_ctor_get(v_s_2192_, 0);
v_startInclusive_2207_ = lean_ctor_get(v_s_2192_, 1);
v___x_2208_ = lean_nat_add(v_startInclusive_2207_, v_pos_2202_);
lean_dec(v_pos_2202_);
v___x_2209_ = lean_string_utf8_next_fast(v_str_2206_, v___x_2208_);
lean_dec(v___x_2208_);
v___x_2210_ = lean_nat_sub(v___x_2209_, v_startInclusive_2207_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set_tag(v___x_2204_, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2210_);
v___x_2212_ = v___x_2204_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
v_a_2193_ = v___x_2212_;
v_b_2194_ = v___x_2195_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2216_; lean_object* v_table_2217_; lean_object* v_stackPos_2218_; lean_object* v_needlePos_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2274_; 
v_needle_2216_ = lean_ctor_get(v_a_2193_, 0);
v_table_2217_ = lean_ctor_get(v_a_2193_, 1);
v_stackPos_2218_ = lean_ctor_get(v_a_2193_, 2);
v_needlePos_2219_ = lean_ctor_get(v_a_2193_, 3);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_a_2193_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2221_ = v_a_2193_;
v_isShared_2222_ = v_isSharedCheck_2274_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_needlePos_2219_);
lean_inc(v_stackPos_2218_);
lean_inc(v_table_2217_);
lean_inc(v_needle_2216_);
lean_dec(v_a_2193_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2274_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v_str_2223_; lean_object* v_startInclusive_2224_; lean_object* v_endExclusive_2225_; lean_object* v_str_2226_; lean_object* v_startInclusive_2227_; lean_object* v_endExclusive_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v_str_2223_ = lean_ctor_get(v_needle_2216_, 0);
v_startInclusive_2224_ = lean_ctor_get(v_needle_2216_, 1);
v_endExclusive_2225_ = lean_ctor_get(v_needle_2216_, 2);
v_str_2226_ = lean_ctor_get(v_s_2192_, 0);
v_startInclusive_2227_ = lean_ctor_get(v_s_2192_, 1);
v_endExclusive_2228_ = lean_ctor_get(v_s_2192_, 2);
v___x_2229_ = lean_nat_sub(v_stackPos_2218_, v_needlePos_2219_);
v___x_2230_ = lean_nat_sub(v_endExclusive_2225_, v_startInclusive_2224_);
v___x_2231_ = lean_nat_add(v___x_2229_, v___x_2230_);
v___x_2232_ = lean_nat_sub(v_endExclusive_2228_, v_startInclusive_2227_);
v___x_2233_ = lean_nat_dec_le(v___x_2231_, v___x_2232_);
lean_dec(v___x_2231_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
lean_dec(v___x_2230_);
lean_del_object(v___x_2221_);
lean_dec(v_needlePos_2219_);
lean_dec(v_stackPos_2218_);
lean_dec_ref(v_table_2217_);
lean_dec_ref(v_needle_2216_);
v___x_2234_ = lean_unsigned_to_nat(1u);
v___x_2235_ = lean_nat_add(v___x_2229_, v___x_2234_);
lean_dec(v___x_2229_);
v___x_2236_ = lean_nat_dec_le(v___x_2235_, v___x_2232_);
lean_dec(v___x_2232_);
lean_dec(v___x_2235_);
if (v___x_2236_ == 0)
{
return v_b_2194_;
}
else
{
lean_object* v___x_2237_; 
v___x_2237_ = lean_box(3);
v_a_2193_ = v___x_2237_;
v_b_2194_ = v___x_2195_;
goto _start;
}
}
else
{
lean_object* v___x_2239_; uint8_t v_stackByte_2240_; lean_object* v___x_2241_; uint8_t v_patByte_2242_; uint8_t v___x_2243_; 
lean_dec(v___x_2232_);
lean_dec(v___x_2229_);
v___x_2239_ = lean_nat_add(v_startInclusive_2227_, v_stackPos_2218_);
v_stackByte_2240_ = lean_string_get_byte_fast(v_str_2226_, v___x_2239_);
v___x_2241_ = lean_nat_add(v_startInclusive_2224_, v_needlePos_2219_);
v_patByte_2242_ = lean_string_get_byte_fast(v_str_2223_, v___x_2241_);
v___x_2243_ = lean_uint8_dec_eq(v_stackByte_2240_, v_patByte_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; uint8_t v_decide_2245_; 
lean_dec(v___x_2230_);
v___x_2244_ = lean_unsigned_to_nat(0u);
v_decide_2245_ = lean_nat_dec_eq(v_needlePos_2219_, v___x_2244_);
if (v_decide_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v_newNeedlePos_2248_; uint8_t v___x_2249_; 
v___x_2246_ = lean_unsigned_to_nat(1u);
v___x_2247_ = lean_nat_sub(v_needlePos_2219_, v___x_2246_);
lean_dec(v_needlePos_2219_);
v_newNeedlePos_2248_ = lean_array_fget_borrowed(v_table_2217_, v___x_2247_);
lean_dec(v___x_2247_);
v___x_2249_ = lean_nat_dec_eq(v_newNeedlePos_2248_, v___x_2244_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2251_; 
lean_inc(v_newNeedlePos_2248_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 3, v_newNeedlePos_2248_);
v___x_2251_ = v___x_2221_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_needle_2216_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_table_2217_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_stackPos_2218_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v_newNeedlePos_2248_);
v___x_2251_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
v_a_2193_ = v___x_2251_;
v_b_2194_ = v___x_2195_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2254_; lean_object* v___x_2256_; 
v_nextStackPos_2254_ = l_String_Slice_posGE___redArg(v_s_2192_, v_stackPos_2218_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 3, v___x_2244_);
lean_ctor_set(v___x_2221_, 2, v_nextStackPos_2254_);
v___x_2256_ = v___x_2221_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_needle_2216_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_table_2217_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_nextStackPos_2254_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v___x_2244_);
v___x_2256_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
v_a_2193_ = v___x_2256_;
v_b_2194_ = v___x_2195_;
goto _start;
}
}
}
else
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v_nextStackPos_2261_; lean_object* v___x_2263_; 
lean_dec(v_needlePos_2219_);
v___x_2259_ = lean_unsigned_to_nat(1u);
v___x_2260_ = lean_nat_add(v_stackPos_2218_, v___x_2259_);
lean_dec(v_stackPos_2218_);
v_nextStackPos_2261_ = l_String_Slice_posGE___redArg(v_s_2192_, v___x_2260_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 3, v___x_2244_);
lean_ctor_set(v___x_2221_, 2, v_nextStackPos_2261_);
v___x_2263_ = v___x_2221_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_needle_2216_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_table_2217_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_nextStackPos_2261_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v___x_2244_);
v___x_2263_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
v_a_2193_ = v___x_2263_;
v_b_2194_ = v___x_2195_;
goto _start;
}
}
}
else
{
lean_object* v___x_2266_; lean_object* v_nextNeedlePos_2267_; uint8_t v_decide_2268_; 
v___x_2266_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2267_ = lean_nat_add(v_needlePos_2219_, v___x_2266_);
lean_dec(v_needlePos_2219_);
v_decide_2268_ = lean_nat_dec_eq(v_nextNeedlePos_2267_, v___x_2230_);
lean_dec(v___x_2230_);
if (v_decide_2268_ == 0)
{
lean_object* v_nextStackPos_2269_; lean_object* v___x_2271_; 
v_nextStackPos_2269_ = lean_nat_add(v_stackPos_2218_, v___x_2266_);
lean_dec(v_stackPos_2218_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 3, v_nextNeedlePos_2267_);
lean_ctor_set(v___x_2221_, 2, v_nextStackPos_2269_);
v___x_2271_ = v___x_2221_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_needle_2216_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_table_2217_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v_nextStackPos_2269_);
lean_ctor_set(v_reuseFailAlloc_2273_, 3, v_nextNeedlePos_2267_);
v___x_2271_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
v_a_2193_ = v___x_2271_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2267_);
lean_del_object(v___x_2221_);
lean_dec(v_stackPos_2218_);
lean_dec_ref(v_table_2217_);
lean_dec_ref(v_needle_2216_);
return v_decide_2268_;
}
}
}
}
}
default: 
{
return v_b_2194_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2192_ = stack[0].m_obj;
lean_object* v_a_2193_ = stack[1].m_obj;
uint8_t v_b_2194_ = stack[2].m_num;
uint8_t v_res_2275_;
v_res_2275_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2192_, v_a_2193_, v_b_2194_);
stack->m_num = v_res_2275_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2276_, lean_object* v_a_2277_, lean_object* v_b_2278_){
_start:
{
uint8_t v_b_boxed_2279_; uint8_t v_res_2280_; lean_object* v_r_2281_; 
v_b_boxed_2279_ = lean_unbox(v_b_2278_);
v_res_2280_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2276_, v_a_2277_, v_b_boxed_2279_);
lean_dec_ref(v_s_2276_);
v_r_2281_ = lean_box(v_res_2280_);
return v_r_2281_;
}
}
uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2284_, lean_object* v_s_2285_){
_start:
{
lean_object* v___y_2287_; lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = lean_string_utf8_byte_size(v___x_2284_);
v___x_2292_ = lean_nat_dec_eq(v___x_2291_, v___x_2290_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2284_);
lean_ctor_set(v___x_2293_, 1, v___x_2290_);
lean_ctor_set(v___x_2293_, 2, v___x_2291_);
v___x_2294_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2293_);
v___x_2295_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
lean_ctor_set(v___x_2295_, 2, v___x_2290_);
lean_ctor_set(v___x_2295_, 3, v___x_2290_);
v___y_2287_ = v___x_2295_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2296_; 
lean_dec_ref(v___x_2284_);
v___x_2296_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___closed__0));
v___y_2287_ = v___x_2296_;
goto v___jp_2286_;
}
v___jp_2286_:
{
uint8_t v___x_2288_; uint8_t v___x_2289_; 
v___x_2288_ = 0;
v___x_2289_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2285_, v___y_2287_, v___x_2288_);
return v___x_2289_;
}
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2284_ = stack[0].m_obj;
lean_object* v_s_2285_ = stack[1].m_obj;
uint8_t v_res_2297_;
v_res_2297_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2284_, v_s_2285_);
stack->m_num = v_res_2297_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2298_, lean_object* v_s_2299_){
_start:
{
uint8_t v_res_2300_; lean_object* v_r_2301_; 
v_res_2300_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2298_, v_s_2299_);
lean_dec_ref(v_s_2299_);
v_r_2301_ = lean_box(v_res_2300_);
return v_r_2301_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v_suppressElabErrors_2302_, uint8_t v___y_2303_, lean_object* v_x_2304_){
_start:
{
if (lean_obj_tag(v_x_2304_) == 1)
{
lean_object* v_pre_2305_; 
v_pre_2305_ = lean_ctor_get(v_x_2304_, 0);
if (lean_obj_tag(v_pre_2305_) == 0)
{
lean_object* v_str_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_str_2306_ = lean_ctor_get(v_x_2304_, 1);
v___x_2307_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2308_ = lean_string_dec_eq(v_str_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
return v___x_2308_;
}
else
{
return v_suppressElabErrors_2302_;
}
}
else
{
return v___y_2303_;
}
}
else
{
return v___y_2303_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_2302_ = stack[0].m_num;
uint8_t v___y_2303_ = stack[1].m_num;
lean_object* v_x_2304_ = stack[2].m_obj;
uint8_t v_res_2309_;
v_res_2309_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v_suppressElabErrors_2302_, v___y_2303_, v_x_2304_);
stack->m_num = v_res_2309_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_2310_, lean_object* v___y_2311_, lean_object* v_x_2312_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2313_; uint8_t v___y_26446__boxed_2314_; uint8_t v_res_2315_; lean_object* v_r_2316_; 
v_suppressElabErrors_boxed_2313_ = lean_unbox(v_suppressElabErrors_2310_);
v___y_26446__boxed_2314_ = lean_unbox(v___y_2311_);
v_res_2315_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v_suppressElabErrors_boxed_2313_, v___y_26446__boxed_2314_, v_x_2312_);
lean_dec(v_x_2312_);
v_r_2316_ = lean_box(v_res_2315_);
return v_r_2316_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2317_, lean_object* v_msgData_2318_, uint8_t v_severity_2319_, uint8_t v_isSilent_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; uint8_t v___y_2329_; uint8_t v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; uint8_t v___y_2390_; lean_object* v___y_2391_; uint8_t v___y_2392_; uint8_t v___y_2393_; lean_object* v___y_2394_; uint8_t v___y_2418_; uint8_t v___y_2419_; uint8_t v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; uint8_t v___y_2426_; uint8_t v___y_2427_; uint8_t v___y_2428_; uint8_t v___x_2443_; uint8_t v___y_2445_; uint8_t v___y_2446_; uint8_t v___y_2447_; uint8_t v___y_2449_; uint8_t v___x_2461_; 
v___x_2443_ = 2;
v___x_2461_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2319_, v___x_2443_);
if (v___x_2461_ == 0)
{
v___y_2449_ = v___x_2461_;
goto v___jp_2448_;
}
else
{
uint8_t v___x_2462_; 
lean_inc_ref(v_msgData_2318_);
v___x_2462_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2318_);
v___y_2449_ = v___x_2462_;
goto v___jp_2448_;
}
v___jp_2324_:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_Elab_Command_getScope___redArg(v___y_2332_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v_currNamespace_2335_; lean_object* v___x_2336_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v_currNamespace_2335_ = lean_ctor_get(v_a_2334_, 2);
lean_inc(v_currNamespace_2335_);
lean_dec(v_a_2334_);
v___x_2336_ = l_Lean_Elab_Command_getScope___redArg(v___y_2332_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2372_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2372_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2372_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_openDecls_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v_env_2346_; lean_object* v_messages_2347_; lean_object* v_scopes_2348_; lean_object* v_usedQuotCtxts_2349_; lean_object* v_nextMacroScope_2350_; lean_object* v_maxRecDepth_2351_; lean_object* v_ngen_2352_; lean_object* v_auxDeclNGen_2353_; lean_object* v_infoState_2354_; lean_object* v_traceState_2355_; lean_object* v_snapshotTasks_2356_; lean_object* v_prevLinterStates_2357_; lean_object* v_codeQualityEntryTasks_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2371_; 
v_openDecls_2341_ = lean_ctor_get(v_a_2337_, 3);
lean_inc(v_openDecls_2341_);
lean_dec(v_a_2337_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v_currNamespace_2335_);
lean_ctor_set(v___x_2342_, 1, v_openDecls_2341_);
v___x_2343_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v___y_2327_);
lean_inc_ref(v___y_2326_);
lean_inc_ref(v___y_2331_);
v___x_2344_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2344_, 0, v___y_2331_);
lean_ctor_set(v___x_2344_, 1, v___y_2325_);
lean_ctor_set(v___x_2344_, 2, v___y_2328_);
lean_ctor_set(v___x_2344_, 3, v___y_2326_);
lean_ctor_set(v___x_2344_, 4, v___x_2343_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*5, v___y_2329_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*5 + 1, v___y_2330_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*5 + 2, v_isSilent_2320_);
v___x_2345_ = lean_st_ref_take(v___y_2332_);
v_env_2346_ = lean_ctor_get(v___x_2345_, 0);
v_messages_2347_ = lean_ctor_get(v___x_2345_, 1);
v_scopes_2348_ = lean_ctor_get(v___x_2345_, 2);
v_usedQuotCtxts_2349_ = lean_ctor_get(v___x_2345_, 3);
v_nextMacroScope_2350_ = lean_ctor_get(v___x_2345_, 4);
v_maxRecDepth_2351_ = lean_ctor_get(v___x_2345_, 5);
v_ngen_2352_ = lean_ctor_get(v___x_2345_, 6);
v_auxDeclNGen_2353_ = lean_ctor_get(v___x_2345_, 7);
v_infoState_2354_ = lean_ctor_get(v___x_2345_, 8);
v_traceState_2355_ = lean_ctor_get(v___x_2345_, 9);
v_snapshotTasks_2356_ = lean_ctor_get(v___x_2345_, 10);
v_prevLinterStates_2357_ = lean_ctor_get(v___x_2345_, 11);
v_codeQualityEntryTasks_2358_ = lean_ctor_get(v___x_2345_, 12);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2360_ = v___x_2345_;
v_isShared_2361_ = v_isSharedCheck_2371_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2358_);
lean_inc(v_prevLinterStates_2357_);
lean_inc(v_snapshotTasks_2356_);
lean_inc(v_traceState_2355_);
lean_inc(v_infoState_2354_);
lean_inc(v_auxDeclNGen_2353_);
lean_inc(v_ngen_2352_);
lean_inc(v_maxRecDepth_2351_);
lean_inc(v_nextMacroScope_2350_);
lean_inc(v_usedQuotCtxts_2349_);
lean_inc(v_scopes_2348_);
lean_inc(v_messages_2347_);
lean_inc(v_env_2346_);
lean_dec(v___x_2345_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2371_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2362_ = lean_box(0);
v___x_2363_ = l_Lean_MessageLog_add(v___x_2344_, v_messages_2347_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v___x_2363_);
v___x_2365_ = v___x_2360_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_env_2346_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_scopes_2348_);
lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_usedQuotCtxts_2349_);
lean_ctor_set(v_reuseFailAlloc_2370_, 4, v_nextMacroScope_2350_);
lean_ctor_set(v_reuseFailAlloc_2370_, 5, v_maxRecDepth_2351_);
lean_ctor_set(v_reuseFailAlloc_2370_, 6, v_ngen_2352_);
lean_ctor_set(v_reuseFailAlloc_2370_, 7, v_auxDeclNGen_2353_);
lean_ctor_set(v_reuseFailAlloc_2370_, 8, v_infoState_2354_);
lean_ctor_set(v_reuseFailAlloc_2370_, 9, v_traceState_2355_);
lean_ctor_set(v_reuseFailAlloc_2370_, 10, v_snapshotTasks_2356_);
lean_ctor_set(v_reuseFailAlloc_2370_, 11, v_prevLinterStates_2357_);
lean_ctor_set(v_reuseFailAlloc_2370_, 12, v_codeQualityEntryTasks_2358_);
v___x_2365_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2366_ = lean_st_ref_put(v___y_2332_, v___x_2365_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2362_);
v___x_2368_ = v___x_2339_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2362_);
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
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_currNamespace_2335_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec_ref(v___y_2325_);
v_a_2373_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2336_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2336_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec_ref(v___y_2325_);
v_a_2381_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2333_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2333_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
v___jp_2389_:
{
lean_object* v_fileName_2395_; lean_object* v_fileMap_2396_; uint8_t v_suppressElabErrors_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___f_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2416_; 
v_fileName_2395_ = lean_ctor_get(v___y_2321_, 0);
v_fileMap_2396_ = lean_ctor_get(v___y_2321_, 1);
v_suppressElabErrors_2397_ = lean_ctor_get_uint8(v___y_2321_, sizeof(void*)*10);
v___x_2398_ = lean_box(v_suppressElabErrors_2397_);
v___x_2399_ = lean_box(v___y_2390_);
v___f_2400_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2400_, 0, v___x_2398_);
lean_closure_set(v___f_2400_, 1, v___x_2399_);
v___x_2401_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2318_);
v___x_2402_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2401_, v___y_2322_);
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2416_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2416_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_inc_ref_n(v_fileMap_2396_, 2);
v___x_2407_ = l_Lean_FileMap_toPosition(v_fileMap_2396_, v___y_2391_);
lean_dec(v___y_2391_);
v___x_2408_ = l_Lean_FileMap_toPosition(v_fileMap_2396_, v___y_2394_);
lean_dec(v___y_2394_);
v___x_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
v___x_2410_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
if (v_suppressElabErrors_2397_ == 0)
{
lean_del_object(v___x_2405_);
lean_dec_ref(v___f_2400_);
v___y_2325_ = v___x_2407_;
v___y_2326_ = v___x_2410_;
v___y_2327_ = v_a_2403_;
v___y_2328_ = v___x_2409_;
v___y_2329_ = v___y_2392_;
v___y_2330_ = v___y_2393_;
v___y_2331_ = v_fileName_2395_;
v___y_2332_ = v___y_2322_;
goto v___jp_2324_;
}
else
{
uint8_t v___x_2411_; 
lean_inc(v_a_2403_);
v___x_2411_ = l_Lean_MessageData_hasTag(v___f_2400_, v_a_2403_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
lean_dec_ref_known(v___x_2409_, 1);
lean_dec_ref(v___x_2407_);
lean_dec(v_a_2403_);
v___x_2412_ = lean_box(0);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2412_);
v___x_2414_ = v___x_2405_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
else
{
lean_del_object(v___x_2405_);
v___y_2325_ = v___x_2407_;
v___y_2326_ = v___x_2410_;
v___y_2327_ = v_a_2403_;
v___y_2328_ = v___x_2409_;
v___y_2329_ = v___y_2392_;
v___y_2330_ = v___y_2393_;
v___y_2331_ = v_fileName_2395_;
v___y_2332_ = v___y_2322_;
goto v___jp_2324_;
}
}
}
}
v___jp_2417_:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_Syntax_getTailPos_x3f(v___y_2421_, v___y_2419_);
lean_dec(v___y_2421_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_inc(v___y_2422_);
v___y_2390_ = v___y_2418_;
v___y_2391_ = v___y_2422_;
v___y_2392_ = v___y_2419_;
v___y_2393_ = v___y_2420_;
v___y_2394_ = v___y_2422_;
goto v___jp_2389_;
}
else
{
lean_object* v_val_2424_; 
v_val_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_val_2424_);
lean_dec_ref_known(v___x_2423_, 1);
v___y_2390_ = v___y_2418_;
v___y_2391_ = v___y_2422_;
v___y_2392_ = v___y_2419_;
v___y_2393_ = v___y_2420_;
v___y_2394_ = v_val_2424_;
goto v___jp_2389_;
}
}
v___jp_2425_:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_Elab_Command_getRef___redArg(v___y_2321_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v_ref_2431_; lean_object* v___x_2432_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v_ref_2431_ = l_Lean_replaceRef(v_ref_2317_, v_a_2430_);
lean_dec(v_a_2430_);
v___x_2432_ = l_Lean_Syntax_getPos_x3f(v_ref_2431_, v___y_2427_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_unsigned_to_nat(0u);
v___y_2418_ = v___y_2426_;
v___y_2419_ = v___y_2427_;
v___y_2420_ = v___y_2428_;
v___y_2421_ = v_ref_2431_;
v___y_2422_ = v___x_2433_;
goto v___jp_2417_;
}
else
{
lean_object* v_val_2434_; 
v_val_2434_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_val_2434_);
lean_dec_ref_known(v___x_2432_, 1);
v___y_2418_ = v___y_2426_;
v___y_2419_ = v___y_2427_;
v___y_2420_ = v___y_2428_;
v___y_2421_ = v_ref_2431_;
v___y_2422_ = v_val_2434_;
goto v___jp_2417_;
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec_ref(v_msgData_2318_);
v_a_2435_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2429_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2429_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
v___jp_2444_:
{
if (v___y_2447_ == 0)
{
v___y_2426_ = v___y_2445_;
v___y_2427_ = v___y_2446_;
v___y_2428_ = v_severity_2319_;
goto v___jp_2425_;
}
else
{
v___y_2426_ = v___y_2445_;
v___y_2427_ = v___y_2446_;
v___y_2428_ = v___x_2443_;
goto v___jp_2425_;
}
}
v___jp_2448_:
{
if (v___y_2449_ == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v_scopes_2452_; lean_object* v___x_2453_; lean_object* v_opts_2454_; uint8_t v___x_2455_; uint8_t v___x_2456_; 
v___x_2450_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2451_ = lean_st_ref_get(v___y_2322_);
v_scopes_2452_ = lean_ctor_get(v___x_2451_, 2);
lean_inc(v_scopes_2452_);
lean_dec(v___x_2451_);
v___x_2453_ = l_List_head_x21___redArg(v___x_2450_, v_scopes_2452_);
lean_dec(v_scopes_2452_);
v_opts_2454_ = lean_ctor_get(v___x_2453_, 1);
lean_inc_ref(v_opts_2454_);
lean_dec(v___x_2453_);
v___x_2455_ = 1;
v___x_2456_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2319_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_dec_ref(v_opts_2454_);
v___y_2445_ = v___y_2449_;
v___y_2446_ = v___y_2449_;
v___y_2447_ = v___x_2456_;
goto v___jp_2444_;
}
else
{
lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = l_Lean_warningAsError;
v___x_2458_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2454_, v___x_2457_);
lean_dec_ref(v_opts_2454_);
v___y_2445_ = v___y_2449_;
v___y_2446_ = v___y_2449_;
v___y_2447_ = v___x_2458_;
goto v___jp_2444_;
}
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
lean_dec_ref(v_msgData_2318_);
v___x_2459_ = lean_box(0);
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
return v___x_2460_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2317_ = stack[0].m_obj;
lean_object* v_msgData_2318_ = stack[1].m_obj;
uint8_t v_severity_2319_ = stack[2].m_num;
uint8_t v_isSilent_2320_ = stack[3].m_num;
lean_object* v___y_2321_ = stack[4].m_obj;
lean_object* v___y_2322_ = stack[5].m_obj;
lean_object* v_res_2463_;
v_res_2463_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2317_, v_msgData_2318_, v_severity_2319_, v_isSilent_2320_, v___y_2321_, v___y_2322_);
stack->m_obj
 = v_res_2463_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2464_, lean_object* v_msgData_2465_, lean_object* v_severity_2466_, lean_object* v_isSilent_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
uint8_t v_severity_boxed_2471_; uint8_t v_isSilent_boxed_2472_; lean_object* v_res_2473_; 
v_severity_boxed_2471_ = lean_unbox(v_severity_2466_);
v_isSilent_boxed_2472_ = lean_unbox(v_isSilent_2467_);
v_res_2473_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2464_, v_msgData_2465_, v_severity_boxed_2471_, v_isSilent_boxed_2472_, v___y_2468_, v___y_2469_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v_ref_2464_);
return v_res_2473_;
}
}
lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2474_, lean_object* v_msgData_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
uint8_t v___x_2479_; uint8_t v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = 2;
v___x_2480_ = 0;
v___x_2481_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2474_, v_msgData_2475_, v___x_2479_, v___x_2480_, v___y_2476_, v___y_2477_);
return v___x_2481_;
}
}
LEAN_EXPORT void l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2474_ = stack[0].m_obj;
lean_object* v_msgData_2475_ = stack[1].m_obj;
lean_object* v___y_2476_ = stack[2].m_obj;
lean_object* v___y_2477_ = stack[3].m_obj;
lean_object* v_res_2482_;
v_res_2482_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2474_, v_msgData_2475_, v___y_2476_, v___y_2477_);
stack->m_obj
 = v_res_2482_;
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2483_, lean_object* v_msgData_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2483_, v_msgData_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v_ref_2483_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2489_, lean_object* v___x_2490_, lean_object* v___x_2491_, lean_object* v_a_2492_, lean_object* v_b_2493_){
_start:
{
lean_object* v_it_2495_; lean_object* v_startInclusive_2496_; lean_object* v_endExclusive_2497_; 
if (lean_obj_tag(v_a_2492_) == 0)
{
lean_object* v_currPos_2502_; lean_object* v_searcher_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2532_; 
v_currPos_2502_ = lean_ctor_get(v_a_2492_, 0);
v_searcher_2503_ = lean_ctor_get(v_a_2492_, 1);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_a_2492_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2505_ = v_a_2492_;
v_isShared_2506_ = v_isSharedCheck_2532_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_searcher_2503_);
lean_inc(v_currPos_2502_);
lean_dec(v_a_2492_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2532_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v_str_2507_; lean_object* v_startInclusive_2508_; lean_object* v_endExclusive_2509_; lean_object* v___x_2510_; uint8_t v_decide_2511_; 
v_str_2507_ = lean_ctor_get(v___x_2490_, 0);
v_startInclusive_2508_ = lean_ctor_get(v___x_2490_, 1);
v_endExclusive_2509_ = lean_ctor_get(v___x_2490_, 2);
v___x_2510_ = lean_nat_sub(v_endExclusive_2509_, v_startInclusive_2508_);
v_decide_2511_ = lean_nat_dec_eq(v_searcher_2503_, v___x_2510_);
lean_dec(v___x_2510_);
if (v_decide_2511_ == 0)
{
uint32_t v___x_2512_; lean_object* v___x_2513_; uint32_t v___x_2514_; uint8_t v___x_2515_; 
v___x_2512_ = 10;
v___x_2513_ = lean_nat_add(v_startInclusive_2508_, v_searcher_2503_);
v___x_2514_ = lean_string_utf8_get_fast(v_str_2507_, v___x_2513_);
v___x_2515_ = lean_uint32_dec_eq(v___x_2514_, v___x_2512_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
lean_dec(v_searcher_2503_);
v___x_2516_ = lean_string_utf8_next_fast(v_str_2507_, v___x_2513_);
lean_dec(v___x_2513_);
v___x_2517_ = lean_nat_sub(v___x_2516_, v_startInclusive_2508_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 1, v___x_2517_);
v___x_2519_ = v___x_2505_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_currPos_2502_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
v_a_2492_ = v___x_2519_;
goto _start;
}
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v_slice_2525_; lean_object* v_nextIt_2527_; 
v___x_2522_ = lean_string_utf8_next_fast(v_str_2507_, v___x_2513_);
v___x_2523_ = lean_nat_sub(v___x_2522_, v___x_2513_);
lean_dec(v___x_2513_);
v___x_2524_ = lean_nat_add(v_searcher_2503_, v___x_2523_);
lean_dec(v___x_2523_);
v_slice_2525_ = l_String_Slice_subslice_x21(v___x_2490_, v_currPos_2502_, v_searcher_2503_);
lean_inc(v___x_2524_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 1, v___x_2524_);
lean_ctor_set(v___x_2505_, 0, v___x_2524_);
v_nextIt_2527_ = v___x_2505_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v___x_2524_);
v_nextIt_2527_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v_startInclusive_2528_; lean_object* v_endExclusive_2529_; 
v_startInclusive_2528_ = lean_ctor_get(v_slice_2525_, 0);
lean_inc(v_startInclusive_2528_);
v_endExclusive_2529_ = lean_ctor_get(v_slice_2525_, 1);
lean_inc(v_endExclusive_2529_);
lean_dec_ref(v_slice_2525_);
v_it_2495_ = v_nextIt_2527_;
v_startInclusive_2496_ = v_startInclusive_2528_;
v_endExclusive_2497_ = v_endExclusive_2529_;
goto v___jp_2494_;
}
}
}
else
{
lean_object* v___x_2531_; 
lean_del_object(v___x_2505_);
lean_dec(v_searcher_2503_);
v___x_2531_ = lean_box(1);
lean_inc(v___x_2491_);
v_it_2495_ = v___x_2531_;
v_startInclusive_2496_ = v_currPos_2502_;
v_endExclusive_2497_ = v___x_2491_;
goto v___jp_2494_;
}
}
}
else
{
lean_dec(v___x_2491_);
lean_dec_ref(v___x_2489_);
return v_b_2493_;
}
v___jp_2494_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_inc_ref(v___x_2489_);
v___x_2498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2489_);
lean_ctor_set(v___x_2498_, 1, v_startInclusive_2496_);
lean_ctor_set(v___x_2498_, 2, v_endExclusive_2497_);
v___x_2499_ = l_String_Slice_toString(v___x_2498_);
lean_dec_ref_known(v___x_2498_, 3);
v___x_2500_ = lean_array_push(v_b_2493_, v___x_2499_);
v_a_2492_ = v_it_2495_;
v_b_2493_ = v___x_2500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2533_, lean_object* v___x_2534_, lean_object* v___x_2535_, lean_object* v_a_2536_, lean_object* v_b_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2533_, v___x_2534_, v___x_2535_, v_a_2536_, v_b_2537_);
lean_dec_ref(v___x_2534_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2539_, lean_object* v___x_2540_, lean_object* v___x_2541_, lean_object* v_a_2542_, lean_object* v_b_2543_){
_start:
{
lean_object* v_it_2545_; lean_object* v_startInclusive_2546_; lean_object* v_endExclusive_2547_; 
if (lean_obj_tag(v_a_2542_) == 0)
{
lean_object* v_currPos_2552_; lean_object* v_searcher_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2582_; 
v_currPos_2552_ = lean_ctor_get(v_a_2542_, 0);
v_searcher_2553_ = lean_ctor_get(v_a_2542_, 1);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_a_2542_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2555_ = v_a_2542_;
v_isShared_2556_ = v_isSharedCheck_2582_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_searcher_2553_);
lean_inc(v_currPos_2552_);
lean_dec(v_a_2542_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2582_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v_str_2557_; lean_object* v_startInclusive_2558_; lean_object* v_endExclusive_2559_; lean_object* v___x_2560_; uint8_t v_decide_2561_; 
v_str_2557_ = lean_ctor_get(v___x_2540_, 0);
v_startInclusive_2558_ = lean_ctor_get(v___x_2540_, 1);
v_endExclusive_2559_ = lean_ctor_get(v___x_2540_, 2);
v___x_2560_ = lean_nat_sub(v_endExclusive_2559_, v_startInclusive_2558_);
v_decide_2561_ = lean_nat_dec_eq(v_searcher_2553_, v___x_2560_);
lean_dec(v___x_2560_);
if (v_decide_2561_ == 0)
{
lean_object* v___x_2562_; uint32_t v___x_2563_; uint32_t v___x_2564_; uint8_t v___x_2565_; 
v___x_2562_ = lean_nat_add(v_startInclusive_2558_, v_searcher_2553_);
v___x_2563_ = lean_string_utf8_get_fast(v_str_2557_, v___x_2562_);
v___x_2564_ = 10;
v___x_2565_ = lean_uint32_dec_eq(v___x_2563_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2569_; 
lean_dec(v_searcher_2553_);
v___x_2566_ = lean_string_utf8_next_fast(v_str_2557_, v___x_2562_);
lean_dec(v___x_2562_);
v___x_2567_ = lean_nat_sub(v___x_2566_, v_startInclusive_2558_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 1, v___x_2567_);
v___x_2569_ = v___x_2555_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_currPos_2552_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
lean_object* v___x_2570_; 
v___x_2570_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2539_, v___x_2540_, v___x_2541_, v___x_2569_, v_b_2543_);
return v___x_2570_;
}
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v_slice_2575_; lean_object* v_nextIt_2577_; 
v___x_2572_ = lean_string_utf8_next_fast(v_str_2557_, v___x_2562_);
v___x_2573_ = lean_nat_sub(v___x_2572_, v___x_2562_);
lean_dec(v___x_2562_);
v___x_2574_ = lean_nat_add(v_searcher_2553_, v___x_2573_);
lean_dec(v___x_2573_);
v_slice_2575_ = l_String_Slice_subslice_x21(v___x_2540_, v_currPos_2552_, v_searcher_2553_);
lean_inc(v___x_2574_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 1, v___x_2574_);
lean_ctor_set(v___x_2555_, 0, v___x_2574_);
v_nextIt_2577_ = v___x_2555_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v___x_2574_);
v_nextIt_2577_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v_startInclusive_2578_; lean_object* v_endExclusive_2579_; 
v_startInclusive_2578_ = lean_ctor_get(v_slice_2575_, 0);
lean_inc(v_startInclusive_2578_);
v_endExclusive_2579_ = lean_ctor_get(v_slice_2575_, 1);
lean_inc(v_endExclusive_2579_);
lean_dec_ref(v_slice_2575_);
v_it_2545_ = v_nextIt_2577_;
v_startInclusive_2546_ = v_startInclusive_2578_;
v_endExclusive_2547_ = v_endExclusive_2579_;
goto v___jp_2544_;
}
}
}
else
{
lean_object* v___x_2581_; 
lean_del_object(v___x_2555_);
lean_dec(v_searcher_2553_);
v___x_2581_ = lean_box(1);
lean_inc(v___x_2541_);
v_it_2545_ = v___x_2581_;
v_startInclusive_2546_ = v_currPos_2552_;
v_endExclusive_2547_ = v___x_2541_;
goto v___jp_2544_;
}
}
}
else
{
lean_dec(v___x_2541_);
lean_dec_ref(v___x_2539_);
return v_b_2543_;
}
v___jp_2544_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_inc_ref(v___x_2539_);
v___x_2548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2539_);
lean_ctor_set(v___x_2548_, 1, v_startInclusive_2546_);
lean_ctor_set(v___x_2548_, 2, v_endExclusive_2547_);
v___x_2549_ = l_String_Slice_toString(v___x_2548_);
lean_dec_ref_known(v___x_2548_, 3);
v___x_2550_ = lean_array_push(v_b_2543_, v___x_2549_);
v___x_2551_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2539_, v___x_2540_, v___x_2541_, v_it_2545_, v___x_2550_);
return v___x_2551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2583_, lean_object* v___x_2584_, lean_object* v___x_2585_, lean_object* v_a_2586_, lean_object* v_b_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2583_, v___x_2584_, v___x_2585_, v_a_2586_, v_b_2587_);
lean_dec_ref(v___x_2584_);
return v_res_2588_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2592_; lean_object* v_infoState_2593_; uint8_t v_enabled_2594_; 
v___x_2592_ = lean_st_ref_get(v___y_2590_);
v_infoState_2593_ = lean_ctor_get(v___x_2592_, 8);
lean_inc_ref(v_infoState_2593_);
lean_dec(v___x_2592_);
v_enabled_2594_ = lean_ctor_get_uint8(v_infoState_2593_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2593_);
if (v_enabled_2594_ == 0)
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
lean_dec_ref(v_t_2589_);
v___x_2595_ = lean_box(0);
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
else
{
lean_object* v___x_2597_; lean_object* v_infoState_2598_; lean_object* v_env_2599_; lean_object* v_messages_2600_; lean_object* v_scopes_2601_; lean_object* v_usedQuotCtxts_2602_; lean_object* v_nextMacroScope_2603_; lean_object* v_maxRecDepth_2604_; lean_object* v_ngen_2605_; lean_object* v_auxDeclNGen_2606_; lean_object* v_traceState_2607_; lean_object* v_snapshotTasks_2608_; lean_object* v_prevLinterStates_2609_; lean_object* v_codeQualityEntryTasks_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2632_; 
v___x_2597_ = lean_st_ref_take(v___y_2590_);
v_infoState_2598_ = lean_ctor_get(v___x_2597_, 8);
v_env_2599_ = lean_ctor_get(v___x_2597_, 0);
v_messages_2600_ = lean_ctor_get(v___x_2597_, 1);
v_scopes_2601_ = lean_ctor_get(v___x_2597_, 2);
v_usedQuotCtxts_2602_ = lean_ctor_get(v___x_2597_, 3);
v_nextMacroScope_2603_ = lean_ctor_get(v___x_2597_, 4);
v_maxRecDepth_2604_ = lean_ctor_get(v___x_2597_, 5);
v_ngen_2605_ = lean_ctor_get(v___x_2597_, 6);
v_auxDeclNGen_2606_ = lean_ctor_get(v___x_2597_, 7);
v_traceState_2607_ = lean_ctor_get(v___x_2597_, 9);
v_snapshotTasks_2608_ = lean_ctor_get(v___x_2597_, 10);
v_prevLinterStates_2609_ = lean_ctor_get(v___x_2597_, 11);
v_codeQualityEntryTasks_2610_ = lean_ctor_get(v___x_2597_, 12);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2612_ = v___x_2597_;
v_isShared_2613_ = v_isSharedCheck_2632_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2610_);
lean_inc(v_prevLinterStates_2609_);
lean_inc(v_snapshotTasks_2608_);
lean_inc(v_traceState_2607_);
lean_inc(v_infoState_2598_);
lean_inc(v_auxDeclNGen_2606_);
lean_inc(v_ngen_2605_);
lean_inc(v_maxRecDepth_2604_);
lean_inc(v_nextMacroScope_2603_);
lean_inc(v_usedQuotCtxts_2602_);
lean_inc(v_scopes_2601_);
lean_inc(v_messages_2600_);
lean_inc(v_env_2599_);
lean_dec(v___x_2597_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2632_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
uint8_t v_enabled_2614_; lean_object* v_assignment_2615_; lean_object* v_lazyAssignment_2616_; lean_object* v_trees_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2631_; 
v_enabled_2614_ = lean_ctor_get_uint8(v_infoState_2598_, sizeof(void*)*3);
v_assignment_2615_ = lean_ctor_get(v_infoState_2598_, 0);
v_lazyAssignment_2616_ = lean_ctor_get(v_infoState_2598_, 1);
v_trees_2617_ = lean_ctor_get(v_infoState_2598_, 2);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_infoState_2598_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2619_ = v_infoState_2598_;
v_isShared_2620_ = v_isSharedCheck_2631_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_trees_2617_);
lean_inc(v_lazyAssignment_2616_);
lean_inc(v_assignment_2615_);
lean_dec(v_infoState_2598_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2631_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2621_ = lean_box(0);
v___x_2622_ = l_Lean_PersistentArray_push___redArg(v_trees_2617_, v_t_2589_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 2, v___x_2622_);
v___x_2624_ = v___x_2619_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_assignment_2615_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_lazyAssignment_2616_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v___x_2622_);
lean_ctor_set_uint8(v_reuseFailAlloc_2630_, sizeof(void*)*3, v_enabled_2614_);
v___x_2624_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2626_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 8, v___x_2624_);
v___x_2626_ = v___x_2612_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_env_2599_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_messages_2600_);
lean_ctor_set(v_reuseFailAlloc_2629_, 2, v_scopes_2601_);
lean_ctor_set(v_reuseFailAlloc_2629_, 3, v_usedQuotCtxts_2602_);
lean_ctor_set(v_reuseFailAlloc_2629_, 4, v_nextMacroScope_2603_);
lean_ctor_set(v_reuseFailAlloc_2629_, 5, v_maxRecDepth_2604_);
lean_ctor_set(v_reuseFailAlloc_2629_, 6, v_ngen_2605_);
lean_ctor_set(v_reuseFailAlloc_2629_, 7, v_auxDeclNGen_2606_);
lean_ctor_set(v_reuseFailAlloc_2629_, 8, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2629_, 9, v_traceState_2607_);
lean_ctor_set(v_reuseFailAlloc_2629_, 10, v_snapshotTasks_2608_);
lean_ctor_set(v_reuseFailAlloc_2629_, 11, v_prevLinterStates_2609_);
lean_ctor_set(v_reuseFailAlloc_2629_, 12, v_codeQualityEntryTasks_2610_);
v___x_2626_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = lean_st_ref_put(v___y_2590_, v___x_2626_);
v___x_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2621_);
return v___x_2628_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2589_ = stack[0].m_obj;
lean_object* v___y_2590_ = stack[1].m_obj;
lean_object* v_res_2633_;
v_res_2633_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2589_, v___y_2590_);
stack->m_obj
 = v_res_2633_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2634_, v___y_2635_);
lean_dec(v___y_2635_);
return v_res_2637_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_unsigned_to_nat(32u);
v___x_2639_ = lean_mk_empty_array_with_capacity(v___x_2638_);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2641_ = ((size_t)5ULL);
v___x_2642_ = lean_unsigned_to_nat(0u);
v___x_2643_ = lean_unsigned_to_nat(32u);
v___x_2644_ = lean_mk_empty_array_with_capacity(v___x_2643_);
v___x_2645_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2646_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
lean_ctor_set(v___x_2646_, 1, v___x_2644_);
lean_ctor_set(v___x_2646_, 2, v___x_2642_);
lean_ctor_set(v___x_2646_, 3, v___x_2642_);
lean_ctor_set_usize(v___x_2646_, 4, v___x_2641_);
return v___x_2646_;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; lean_object* v_infoState_2652_; uint8_t v_enabled_2653_; 
v___x_2651_ = lean_st_ref_get(v___y_2649_);
v_infoState_2652_ = lean_ctor_get(v___x_2651_, 8);
lean_inc_ref(v_infoState_2652_);
lean_dec(v___x_2651_);
v_enabled_2653_ = lean_ctor_get_uint8(v_infoState_2652_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2652_);
if (v_enabled_2653_ == 0)
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec_ref(v_t_2647_);
v___x_2654_ = lean_box(0);
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
return v___x_2655_;
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2657_, 0, v_t_2647_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2657_, v___y_2649_);
return v___x_2658_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2647_ = stack[0].m_obj;
lean_object* v___y_2648_ = stack[1].m_obj;
lean_object* v___y_2649_ = stack[2].m_obj;
lean_object* v_res_2659_;
v_res_2659_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2647_, v___y_2648_, v___y_2649_);
stack->m_obj
 = v_res_2659_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v___x_2665_, lean_object* v_edited_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_fst_2669_; lean_object* v_snd_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2694_; 
v_fst_2669_ = lean_ctor_get(v_a_2668_, 0);
v_snd_2670_ = lean_ctor_get(v_a_2668_, 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_a_2668_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2672_ = v_a_2668_;
v_isShared_2673_ = v_isSharedCheck_2694_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_snd_2670_);
lean_inc(v_fst_2669_);
lean_dec(v_a_2668_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2694_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
uint8_t v___x_2674_; 
v___x_2674_ = lean_nat_dec_lt(v_snd_2670_, v___x_2665_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2676_; 
if (v_isShared_2673_ == 0)
{
v___x_2676_ = v___x_2672_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_fst_2669_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_snd_2670_);
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
lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2678_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2679_ = lean_array_get_borrowed(v___x_2678_, v_edited_2666_, v_snd_2670_);
v___x_2680_ = lean_string_dec_eq(v___x_2679_, v_a_2667_);
if (v___x_2680_ == 0)
{
uint8_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2681_ = 0;
v___x_2682_ = lean_box(v___x_2681_);
lean_inc(v___x_2679_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v___x_2679_);
lean_ctor_set(v___x_2672_, 0, v___x_2682_);
v___x_2684_ = v___x_2672_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2679_);
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
else
{
lean_object* v___x_2692_; 
if (v_isShared_2673_ == 0)
{
v___x_2692_ = v___x_2672_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_fst_2669_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_snd_2670_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v___x_2695_, lean_object* v_edited_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2695_, v_edited_2696_, v_a_2697_, v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec_ref(v_edited_2696_);
lean_dec(v___x_2695_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(lean_object* v___x_2700_, lean_object* v_original_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v_fst_2704_; lean_object* v_snd_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2729_; 
v_fst_2704_ = lean_ctor_get(v_a_2703_, 0);
v_snd_2705_ = lean_ctor_get(v_a_2703_, 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_a_2703_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2707_ = v_a_2703_;
v_isShared_2708_ = v_isSharedCheck_2729_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_snd_2705_);
lean_inc(v_fst_2704_);
lean_dec(v_a_2703_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2729_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
uint8_t v___x_2709_; 
v___x_2709_ = lean_nat_dec_lt(v_snd_2705_, v___x_2700_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2711_; 
if (v_isShared_2708_ == 0)
{
v___x_2711_ = v___x_2707_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_fst_2704_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_snd_2705_);
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
lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2714_ = lean_array_get_borrowed(v___x_2713_, v_original_2701_, v_snd_2705_);
v___x_2715_ = lean_string_dec_eq(v___x_2714_, v_a_2702_);
if (v___x_2715_ == 0)
{
uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2716_ = 1;
v___x_2717_ = lean_box(v___x_2716_);
lean_inc(v___x_2714_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 1, v___x_2714_);
lean_ctor_set(v___x_2707_, 0, v___x_2717_);
v___x_2719_ = v___x_2707_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2717_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v___x_2714_);
v___x_2719_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2720_ = lean_array_push(v_fst_2704_, v___x_2719_);
v___x_2721_ = lean_unsigned_to_nat(1u);
v___x_2722_ = lean_nat_add(v_snd_2705_, v___x_2721_);
lean_dec(v_snd_2705_);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2720_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v_a_2703_ = v___x_2723_;
goto _start;
}
}
else
{
lean_object* v___x_2727_; 
if (v_isShared_2708_ == 0)
{
v___x_2727_ = v___x_2707_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_fst_2704_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_snd_2705_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg___boxed(lean_object* v___x_2730_, lean_object* v_original_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2730_, v_original_2731_, v_a_2732_, v_a_2733_);
lean_dec_ref(v_a_2732_);
lean_dec_ref(v_original_2731_);
lean_dec(v___x_2730_);
return v_res_2734_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v___x_2735_, lean_object* v_original_2736_, lean_object* v___x_2737_, lean_object* v_edited_2738_, lean_object* v_as_2739_, size_t v_sz_2740_, size_t v_i_2741_, lean_object* v_b_2742_){
_start:
{
uint8_t v___x_2743_; 
v___x_2743_ = lean_usize_dec_lt(v_i_2741_, v_sz_2740_);
if (v___x_2743_ == 0)
{
return v_b_2742_;
}
else
{
lean_object* v_snd_2744_; lean_object* v_fst_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2792_; 
v_snd_2744_ = lean_ctor_get(v_b_2742_, 1);
v_fst_2745_ = lean_ctor_get(v_b_2742_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_b_2742_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2747_ = v_b_2742_;
v_isShared_2748_ = v_isSharedCheck_2792_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_snd_2744_);
lean_inc(v_fst_2745_);
lean_dec(v_b_2742_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2792_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v_fst_2749_; lean_object* v_snd_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2791_; 
v_fst_2749_ = lean_ctor_get(v_snd_2744_, 0);
v_snd_2750_ = lean_ctor_get(v_snd_2744_, 1);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_snd_2744_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2752_ = v_snd_2744_;
v_isShared_2753_ = v_isSharedCheck_2791_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_snd_2750_);
lean_inc(v_fst_2749_);
lean_dec(v_snd_2744_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2791_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v_a_2754_; lean_object* v___x_2756_; 
v_a_2754_ = lean_array_uget_borrowed(v_as_2739_, v_i_2741_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 1, v_fst_2749_);
lean_ctor_set(v___x_2752_, 0, v_fst_2745_);
v___x_2756_ = v___x_2752_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_fst_2745_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_fst_2749_);
v___x_2756_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
lean_object* v___x_2757_; lean_object* v_fst_2758_; lean_object* v_snd_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2789_; 
v___x_2757_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2735_, v_original_2736_, v_a_2754_, v___x_2756_);
v_fst_2758_ = lean_ctor_get(v___x_2757_, 0);
v_snd_2759_ = lean_ctor_get(v___x_2757_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2761_ = v___x_2757_;
v_isShared_2762_ = v_isSharedCheck_2789_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_snd_2759_);
lean_inc(v_fst_2758_);
lean_dec(v___x_2757_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2789_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v_snd_2750_);
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_fst_2758_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_snd_2750_);
v___x_2764_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2765_; lean_object* v_fst_2766_; lean_object* v_snd_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2787_; 
v___x_2765_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2737_, v_edited_2738_, v_a_2754_, v___x_2764_);
v_fst_2766_ = lean_ctor_get(v___x_2765_, 0);
v_snd_2767_ = lean_ctor_get(v___x_2765_, 1);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2769_ = v___x_2765_;
v_isShared_2770_ = v_isSharedCheck_2787_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_snd_2767_);
lean_inc(v_fst_2766_);
lean_dec(v___x_2765_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2787_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2771_ = 2;
v___x_2772_ = lean_box(v___x_2771_);
lean_inc(v_a_2754_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v_a_2754_);
lean_ctor_set(v___x_2769_, 0, v___x_2772_);
v___x_2774_ = v___x_2769_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_a_2754_);
v___x_2774_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
v___x_2775_ = lean_array_push(v_fst_2766_, v___x_2774_);
v___x_2776_ = lean_unsigned_to_nat(1u);
v___x_2777_ = lean_nat_add(v_snd_2759_, v___x_2776_);
lean_dec(v_snd_2759_);
v___x_2778_ = lean_nat_add(v_snd_2767_, v___x_2776_);
lean_dec(v_snd_2767_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 1, v___x_2778_);
lean_ctor_set(v___x_2747_, 0, v___x_2777_);
v___x_2780_ = v___x_2747_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2777_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; size_t v___x_2782_; size_t v___x_2783_; 
v___x_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2775_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = ((size_t)1ULL);
v___x_2783_ = lean_usize_add(v_i_2741_, v___x_2782_);
v_i_2741_ = v___x_2783_;
v_b_2742_ = v___x_2781_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2735_ = stack[0].m_obj;
lean_object* v_original_2736_ = stack[1].m_obj;
lean_object* v___x_2737_ = stack[2].m_obj;
lean_object* v_edited_2738_ = stack[3].m_obj;
lean_object* v_as_2739_ = stack[4].m_obj;
size_t v_sz_2740_ = stack[5].m_num;
size_t v_i_2741_ = stack[6].m_num;
lean_object* v_b_2742_ = stack[7].m_obj;
lean_object* v_res_2793_;
v_res_2793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2735_, v_original_2736_, v___x_2737_, v_edited_2738_, v_as_2739_, v_sz_2740_, v_i_2741_, v_b_2742_);
stack->m_obj
 = v_res_2793_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v___x_2794_, lean_object* v_original_2795_, lean_object* v___x_2796_, lean_object* v_edited_2797_, lean_object* v_as_2798_, lean_object* v_sz_2799_, lean_object* v_i_2800_, lean_object* v_b_2801_){
_start:
{
size_t v_sz_boxed_2802_; size_t v_i_boxed_2803_; lean_object* v_res_2804_; 
v_sz_boxed_2802_ = lean_unbox_usize(v_sz_2799_);
lean_dec(v_sz_2799_);
v_i_boxed_2803_ = lean_unbox_usize(v_i_2800_);
lean_dec(v_i_2800_);
v_res_2804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2794_, v_original_2795_, v___x_2796_, v_edited_2797_, v_as_2798_, v_sz_boxed_2802_, v_i_boxed_2803_, v_b_2801_);
lean_dec_ref(v_as_2798_);
lean_dec_ref(v_edited_2797_);
lean_dec(v___x_2796_);
lean_dec_ref(v_original_2795_);
lean_dec(v___x_2794_);
return v_res_2804_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v___x_2805_, lean_object* v_edited_2806_, lean_object* v___x_2807_, lean_object* v_original_2808_, lean_object* v_as_2809_, size_t v_sz_2810_, size_t v_i_2811_, lean_object* v_b_2812_){
_start:
{
uint8_t v___x_2813_; 
v___x_2813_ = lean_usize_dec_lt(v_i_2811_, v_sz_2810_);
if (v___x_2813_ == 0)
{
return v_b_2812_;
}
else
{
lean_object* v_snd_2814_; lean_object* v_fst_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2862_; 
v_snd_2814_ = lean_ctor_get(v_b_2812_, 1);
v_fst_2815_ = lean_ctor_get(v_b_2812_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_b_2812_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2817_ = v_b_2812_;
v_isShared_2818_ = v_isSharedCheck_2862_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_snd_2814_);
lean_inc(v_fst_2815_);
lean_dec(v_b_2812_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2862_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_fst_2819_; lean_object* v_snd_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2861_; 
v_fst_2819_ = lean_ctor_get(v_snd_2814_, 0);
v_snd_2820_ = lean_ctor_get(v_snd_2814_, 1);
v_isSharedCheck_2861_ = !lean_is_exclusive(v_snd_2814_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2822_ = v_snd_2814_;
v_isShared_2823_ = v_isSharedCheck_2861_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_snd_2820_);
lean_inc(v_fst_2819_);
lean_dec(v_snd_2814_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2861_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v_a_2824_; lean_object* v___x_2826_; 
v_a_2824_ = lean_array_uget_borrowed(v_as_2809_, v_i_2811_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 1, v_fst_2819_);
lean_ctor_set(v___x_2822_, 0, v_fst_2815_);
v___x_2826_ = v___x_2822_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_fst_2815_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_fst_2819_);
v___x_2826_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; lean_object* v_fst_2828_; lean_object* v_snd_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2859_; 
v___x_2827_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2807_, v_original_2808_, v_a_2824_, v___x_2826_);
v_fst_2828_ = lean_ctor_get(v___x_2827_, 0);
v_snd_2829_ = lean_ctor_get(v___x_2827_, 1);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2831_ = v___x_2827_;
v_isShared_2832_ = v_isSharedCheck_2859_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_snd_2829_);
lean_inc(v_fst_2828_);
lean_dec(v___x_2827_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2859_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v_snd_2820_);
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_fst_2828_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_snd_2820_);
v___x_2834_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2835_; lean_object* v_fst_2836_; lean_object* v_snd_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2857_; 
v___x_2835_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2805_, v_edited_2806_, v_a_2824_, v___x_2834_);
v_fst_2836_ = lean_ctor_get(v___x_2835_, 0);
v_snd_2837_ = lean_ctor_get(v___x_2835_, 1);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2839_ = v___x_2835_;
v_isShared_2840_ = v_isSharedCheck_2857_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_snd_2837_);
lean_inc(v_fst_2836_);
lean_dec(v___x_2835_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2857_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
uint8_t v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2841_ = 2;
v___x_2842_ = lean_box(v___x_2841_);
lean_inc(v_a_2824_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v_a_2824_);
lean_ctor_set(v___x_2839_, 0, v___x_2842_);
v___x_2844_ = v___x_2839_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_a_2824_);
v___x_2844_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2845_ = lean_array_push(v_fst_2836_, v___x_2844_);
v___x_2846_ = lean_unsigned_to_nat(1u);
v___x_2847_ = lean_nat_add(v_snd_2829_, v___x_2846_);
lean_dec(v_snd_2829_);
v___x_2848_ = lean_nat_add(v_snd_2837_, v___x_2846_);
lean_dec(v_snd_2837_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v___x_2848_);
lean_ctor_set(v___x_2817_, 0, v___x_2847_);
v___x_2850_ = v___x_2817_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; size_t v___x_2852_; size_t v___x_2853_; lean_object* v___x_2854_; 
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2845_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = ((size_t)1ULL);
v___x_2853_ = lean_usize_add(v_i_2811_, v___x_2852_);
v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2807_, v_original_2808_, v___x_2805_, v_edited_2806_, v_as_2809_, v_sz_2810_, v___x_2853_, v___x_2851_);
return v___x_2854_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2805_ = stack[0].m_obj;
lean_object* v_edited_2806_ = stack[1].m_obj;
lean_object* v___x_2807_ = stack[2].m_obj;
lean_object* v_original_2808_ = stack[3].m_obj;
lean_object* v_as_2809_ = stack[4].m_obj;
size_t v_sz_2810_ = stack[5].m_num;
size_t v_i_2811_ = stack[6].m_num;
lean_object* v_b_2812_ = stack[7].m_obj;
lean_object* v_res_2863_;
v_res_2863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_2805_, v_edited_2806_, v___x_2807_, v_original_2808_, v_as_2809_, v_sz_2810_, v_i_2811_, v_b_2812_);
stack->m_obj
 = v_res_2863_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v___x_2864_, lean_object* v_edited_2865_, lean_object* v___x_2866_, lean_object* v_original_2867_, lean_object* v_as_2868_, lean_object* v_sz_2869_, lean_object* v_i_2870_, lean_object* v_b_2871_){
_start:
{
size_t v_sz_boxed_2872_; size_t v_i_boxed_2873_; lean_object* v_res_2874_; 
v_sz_boxed_2872_ = lean_unbox_usize(v_sz_2869_);
lean_dec(v_sz_2869_);
v_i_boxed_2873_ = lean_unbox_usize(v_i_2870_);
lean_dec(v_i_2870_);
v_res_2874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_2864_, v_edited_2865_, v___x_2866_, v_original_2867_, v_as_2868_, v_sz_boxed_2872_, v_i_boxed_2873_, v_b_2871_);
lean_dec_ref(v_as_2868_);
lean_dec_ref(v_original_2867_);
lean_dec(v___x_2866_);
lean_dec_ref(v_edited_2865_);
lean_dec(v___x_2864_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_2875_, lean_object* v_original_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_fst_2878_; lean_object* v_snd_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2898_; 
v_fst_2878_ = lean_ctor_get(v_a_2877_, 0);
v_snd_2879_ = lean_ctor_get(v_a_2877_, 1);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_a_2877_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2881_ = v_a_2877_;
v_isShared_2882_ = v_isSharedCheck_2898_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_snd_2879_);
lean_inc(v_fst_2878_);
lean_dec(v_a_2877_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2898_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
uint8_t v___x_2883_; 
v___x_2883_ = lean_nat_dec_lt(v_snd_2879_, v___x_2875_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2885_; 
if (v_isShared_2882_ == 0)
{
v___x_2885_ = v___x_2881_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_fst_2878_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_snd_2879_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
else
{
uint8_t v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2887_ = 1;
v___x_2888_ = lean_array_fget_borrowed(v_original_2876_, v_snd_2879_);
v___x_2889_ = lean_box(v___x_2887_);
lean_inc(v___x_2888_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v___x_2888_);
lean_ctor_set(v___x_2881_, 0, v___x_2889_);
v___x_2891_ = v___x_2881_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v___x_2888_);
v___x_2891_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2892_ = lean_array_push(v_fst_2878_, v___x_2891_);
v___x_2893_ = lean_unsigned_to_nat(1u);
v___x_2894_ = lean_nat_add(v_snd_2879_, v___x_2893_);
lean_dec(v_snd_2879_);
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2892_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v_a_2877_ = v___x_2895_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_2899_, lean_object* v_original_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_2899_, v_original_2900_, v_a_2901_);
lean_dec_ref(v_original_2900_);
lean_dec(v___x_2899_);
return v_res_2902_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_2903_, size_t v_i_2904_, lean_object* v_bs_2905_){
_start:
{
uint8_t v___x_2906_; 
v___x_2906_ = lean_usize_dec_lt(v_i_2904_, v_sz_2903_);
if (v___x_2906_ == 0)
{
return v_bs_2905_;
}
else
{
lean_object* v_v_2907_; lean_object* v___x_2908_; lean_object* v_bs_x27_2909_; uint8_t v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; size_t v___x_2913_; size_t v___x_2914_; lean_object* v___x_2915_; 
v_v_2907_ = lean_array_uget(v_bs_2905_, v_i_2904_);
v___x_2908_ = lean_unsigned_to_nat(0u);
v_bs_x27_2909_ = lean_array_uset(v_bs_2905_, v_i_2904_, v___x_2908_);
v___x_2910_ = 0;
v___x_2911_ = lean_box(v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v_v_2907_);
v___x_2913_ = ((size_t)1ULL);
v___x_2914_ = lean_usize_add(v_i_2904_, v___x_2913_);
v___x_2915_ = lean_array_uset(v_bs_x27_2909_, v_i_2904_, v___x_2912_);
v_i_2904_ = v___x_2914_;
v_bs_2905_ = v___x_2915_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2903_ = stack[0].m_num;
size_t v_i_2904_ = stack[1].m_num;
lean_object* v_bs_2905_ = stack[2].m_obj;
lean_object* v_res_2917_;
v_res_2917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_2903_, v_i_2904_, v_bs_2905_);
stack->m_obj
 = v_res_2917_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_2918_, lean_object* v_i_2919_, lean_object* v_bs_2920_){
_start:
{
size_t v_sz_boxed_2921_; size_t v_i_boxed_2922_; lean_object* v_res_2923_; 
v_sz_boxed_2921_ = lean_unbox_usize(v_sz_2918_);
lean_dec(v_sz_2918_);
v_i_boxed_2922_ = lean_unbox_usize(v_i_2919_);
lean_dec(v_i_2919_);
v_res_2923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_2921_, v_i_boxed_2922_, v_bs_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_2924_, lean_object* v_edited_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v_fst_2927_; lean_object* v_snd_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2947_; 
v_fst_2927_ = lean_ctor_get(v_a_2926_, 0);
v_snd_2928_ = lean_ctor_get(v_a_2926_, 1);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_a_2926_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2930_ = v_a_2926_;
v_isShared_2931_ = v_isSharedCheck_2947_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_snd_2928_);
lean_inc(v_fst_2927_);
lean_dec(v_a_2926_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2947_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
uint8_t v___x_2932_; 
v___x_2932_ = lean_nat_dec_lt(v_snd_2928_, v___x_2924_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2934_; 
if (v_isShared_2931_ == 0)
{
v___x_2934_ = v___x_2930_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_fst_2927_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_snd_2928_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
else
{
uint8_t v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2936_ = 0;
v___x_2937_ = lean_array_fget_borrowed(v_edited_2925_, v_snd_2928_);
v___x_2938_ = lean_box(v___x_2936_);
lean_inc(v___x_2937_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 1, v___x_2937_);
lean_ctor_set(v___x_2930_, 0, v___x_2938_);
v___x_2940_ = v___x_2930_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v___x_2937_);
v___x_2940_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2941_ = lean_array_push(v_fst_2927_, v___x_2940_);
v___x_2942_ = lean_unsigned_to_nat(1u);
v___x_2943_ = lean_nat_add(v_snd_2928_, v___x_2942_);
lean_dec(v_snd_2928_);
v___x_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2941_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v_a_2926_ = v___x_2944_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_2948_, lean_object* v_edited_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_2948_, v_edited_2949_, v_a_2950_);
lean_dec_ref(v_edited_2949_);
lean_dec(v___x_2948_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(lean_object* v_x_2952_, lean_object* v_x_2953_){
_start:
{
if (lean_obj_tag(v_x_2953_) == 0)
{
lean_inc(v_x_2952_);
return v_x_2952_;
}
else
{
lean_object* v_key_2954_; lean_object* v_value_2955_; lean_object* v_tail_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v_key_2954_ = lean_ctor_get(v_x_2953_, 0);
v_value_2955_ = lean_ctor_get(v_x_2953_, 1);
v_tail_2956_ = lean_ctor_get(v_x_2953_, 2);
v___x_2957_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2952_, v_tail_2956_);
lean_inc(v_value_2955_);
lean_inc(v_key_2954_);
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v_key_2954_);
lean_ctor_set(v___x_2958_, 1, v_value_2955_);
v___x_2959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v___x_2957_);
return v___x_2959_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17___boxed(lean_object* v_x_2960_, lean_object* v_x_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2960_, v_x_2961_);
lean_dec(v_x_2961_);
lean_dec(v_x_2960_);
return v_res_2962_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(lean_object* v_as_2963_, size_t v_i_2964_, size_t v_stop_2965_, lean_object* v_b_2966_){
_start:
{
uint8_t v___x_2967_; 
v___x_2967_ = lean_usize_dec_eq(v_i_2964_, v_stop_2965_);
if (v___x_2967_ == 0)
{
size_t v___x_2968_; size_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2968_ = ((size_t)1ULL);
v___x_2969_ = lean_usize_sub(v_i_2964_, v___x_2968_);
v___x_2970_ = lean_array_uget_borrowed(v_as_2963_, v___x_2969_);
v___x_2971_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_b_2966_, v___x_2970_);
lean_dec(v_b_2966_);
v_i_2964_ = v___x_2969_;
v_b_2966_ = v___x_2971_;
goto _start;
}
else
{
return v_b_2966_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2963_ = stack[0].m_obj;
size_t v_i_2964_ = stack[1].m_num;
size_t v_stop_2965_ = stack[2].m_num;
lean_object* v_b_2966_ = stack[3].m_obj;
lean_object* v_res_2973_;
v_res_2973_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_as_2963_, v_i_2964_, v_stop_2965_, v_b_2966_);
stack->m_obj
 = v_res_2973_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18___boxed(lean_object* v_as_2974_, lean_object* v_i_2975_, lean_object* v_stop_2976_, lean_object* v_b_2977_){
_start:
{
size_t v_i_boxed_2978_; size_t v_stop_boxed_2979_; lean_object* v_res_2980_; 
v_i_boxed_2978_ = lean_unbox_usize(v_i_2975_);
lean_dec(v_i_2975_);
v_stop_boxed_2979_ = lean_unbox_usize(v_stop_2976_);
lean_dec(v_stop_2976_);
v_res_2980_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_as_2974_, v_i_boxed_2978_, v_stop_boxed_2979_, v_b_2977_);
lean_dec_ref(v_as_2974_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(lean_object* v_left_2981_, lean_object* v_right_2982_, lean_object* v_pref_2983_){
_start:
{
lean_object* v_start_2984_; lean_object* v_stop_2985_; lean_object* v_i_2986_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v_start_2984_ = lean_ctor_get(v_left_2981_, 1);
v_stop_2985_ = lean_ctor_get(v_left_2981_, 2);
v_i_2986_ = lean_array_get_size(v_pref_2983_);
v___x_2992_ = lean_nat_sub(v_stop_2985_, v_start_2984_);
v___x_2993_ = lean_nat_dec_lt(v_i_2986_, v___x_2992_);
lean_dec(v___x_2992_);
if (v___x_2993_ == 0)
{
goto v___jp_2987_;
}
else
{
lean_object* v_start_2994_; lean_object* v_stop_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v_start_2994_ = lean_ctor_get(v_right_2982_, 1);
v_stop_2995_ = lean_ctor_get(v_right_2982_, 2);
v___x_2996_ = lean_nat_sub(v_stop_2995_, v_start_2994_);
v___x_2997_ = lean_nat_dec_lt(v_i_2986_, v___x_2996_);
lean_dec(v___x_2996_);
if (v___x_2997_ == 0)
{
goto v___jp_2987_;
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2998_ = l_Subarray_get___redArg(v_left_2981_, v_i_2986_);
v___x_2999_ = l_Subarray_get___redArg(v_right_2982_, v_i_2986_);
v___x_3000_ = lean_string_dec_eq(v___x_2998_, v___x_2999_);
lean_dec(v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec(v___x_2998_);
v___x_3001_ = l_Subarray_drop___redArg(v_left_2981_, v_i_2986_);
v___x_3002_ = l_Subarray_drop___redArg(v_right_2982_, v_i_2986_);
v___x_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3001_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v_pref_2983_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
return v___x_3004_;
}
else
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_array_push(v_pref_2983_, v___x_2998_);
v_pref_2983_ = v___x_3005_;
goto _start;
}
}
}
v___jp_2987_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2988_ = l_Subarray_drop___redArg(v_left_2981_, v_i_2986_);
v___x_2989_ = l_Subarray_drop___redArg(v_right_2982_, v_i_2986_);
v___x_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2988_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2991_, 0, v_pref_2983_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
return v___x_2991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(lean_object* v_left_3009_, lean_object* v_right_3010_){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3012_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(v_left_3009_, v_right_3010_, v___x_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(lean_object* v_a_3013_, lean_object* v_b_3014_, lean_object* v_x_3015_){
_start:
{
if (lean_obj_tag(v_x_3015_) == 0)
{
lean_dec(v_b_3014_);
lean_dec_ref(v_a_3013_);
return v_x_3015_;
}
else
{
lean_object* v_key_3016_; lean_object* v_value_3017_; lean_object* v_tail_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3030_; 
v_key_3016_ = lean_ctor_get(v_x_3015_, 0);
v_value_3017_ = lean_ctor_get(v_x_3015_, 1);
v_tail_3018_ = lean_ctor_get(v_x_3015_, 2);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_x_3015_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3020_ = v_x_3015_;
v_isShared_3021_ = v_isSharedCheck_3030_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_tail_3018_);
lean_inc(v_value_3017_);
lean_inc(v_key_3016_);
lean_dec(v_x_3015_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3030_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
uint8_t v___x_3022_; 
v___x_3022_ = lean_string_dec_eq(v_key_3016_, v_a_3013_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_3013_, v_b_3014_, v_tail_3018_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 2, v___x_3023_);
v___x_3025_ = v___x_3020_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_key_3016_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v_value_3017_);
lean_ctor_set(v_reuseFailAlloc_3026_, 2, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
else
{
lean_object* v___x_3028_; 
lean_dec(v_value_3017_);
lean_dec(v_key_3016_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 1, v_b_3014_);
lean_ctor_set(v___x_3020_, 0, v_a_3013_);
v___x_3028_ = v___x_3020_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3013_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v_b_3014_);
lean_ctor_set(v_reuseFailAlloc_3029_, 2, v_tail_3018_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(lean_object* v_x_3031_, lean_object* v_x_3032_){
_start:
{
if (lean_obj_tag(v_x_3032_) == 0)
{
return v_x_3031_;
}
else
{
lean_object* v_key_3033_; lean_object* v_value_3034_; lean_object* v_tail_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3058_; 
v_key_3033_ = lean_ctor_get(v_x_3032_, 0);
v_value_3034_ = lean_ctor_get(v_x_3032_, 1);
v_tail_3035_ = lean_ctor_get(v_x_3032_, 2);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_x_3032_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3037_ = v_x_3032_;
v_isShared_3038_ = v_isSharedCheck_3058_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_tail_3035_);
lean_inc(v_value_3034_);
lean_inc(v_key_3033_);
lean_dec(v_x_3032_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3058_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; uint64_t v___x_3040_; uint64_t v___x_3041_; uint64_t v___x_3042_; uint64_t v_fold_3043_; uint64_t v___x_3044_; uint64_t v___x_3045_; uint64_t v___x_3046_; size_t v___x_3047_; size_t v___x_3048_; size_t v___x_3049_; size_t v___x_3050_; size_t v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3054_; 
v___x_3039_ = lean_array_get_size(v_x_3031_);
v___x_3040_ = lean_string_hash(v_key_3033_);
v___x_3041_ = 32ULL;
v___x_3042_ = lean_uint64_shift_right(v___x_3040_, v___x_3041_);
v_fold_3043_ = lean_uint64_xor(v___x_3040_, v___x_3042_);
v___x_3044_ = 16ULL;
v___x_3045_ = lean_uint64_shift_right(v_fold_3043_, v___x_3044_);
v___x_3046_ = lean_uint64_xor(v_fold_3043_, v___x_3045_);
v___x_3047_ = lean_uint64_to_usize(v___x_3046_);
v___x_3048_ = lean_usize_of_nat(v___x_3039_);
v___x_3049_ = ((size_t)1ULL);
v___x_3050_ = lean_usize_sub(v___x_3048_, v___x_3049_);
v___x_3051_ = lean_usize_land(v___x_3047_, v___x_3050_);
v___x_3052_ = lean_array_uget_borrowed(v_x_3031_, v___x_3051_);
lean_inc(v___x_3052_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 2, v___x_3052_);
v___x_3054_ = v___x_3037_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_key_3033_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v_value_3034_);
lean_ctor_set(v_reuseFailAlloc_3057_, 2, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_array_uset(v_x_3031_, v___x_3051_, v___x_3054_);
v_x_3031_ = v___x_3055_;
v_x_3032_ = v_tail_3035_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(lean_object* v_i_3059_, lean_object* v_source_3060_, lean_object* v_target_3061_){
_start:
{
lean_object* v___x_3062_; uint8_t v___x_3063_; 
v___x_3062_ = lean_array_get_size(v_source_3060_);
v___x_3063_ = lean_nat_dec_lt(v_i_3059_, v___x_3062_);
if (v___x_3063_ == 0)
{
lean_dec_ref(v_source_3060_);
lean_dec(v_i_3059_);
return v_target_3061_;
}
else
{
lean_object* v_es_3064_; lean_object* v___x_3065_; lean_object* v_source_3066_; lean_object* v_target_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_es_3064_ = lean_array_fget(v_source_3060_, v_i_3059_);
v___x_3065_ = lean_box(0);
v_source_3066_ = lean_array_fset(v_source_3060_, v_i_3059_, v___x_3065_);
v_target_3067_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_target_3061_, v_es_3064_);
v___x_3068_ = lean_unsigned_to_nat(1u);
v___x_3069_ = lean_nat_add(v_i_3059_, v___x_3068_);
lean_dec(v_i_3059_);
v_i_3059_ = v___x_3069_;
v_source_3060_ = v_source_3066_;
v_target_3061_ = v_target_3067_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(lean_object* v_data_3071_){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v_nbuckets_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3072_ = lean_array_get_size(v_data_3071_);
v___x_3073_ = lean_unsigned_to_nat(2u);
v_nbuckets_3074_ = lean_nat_mul(v___x_3072_, v___x_3073_);
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = lean_box(0);
v___x_3077_ = lean_mk_array(v_nbuckets_3074_, v___x_3076_);
v___x_3078_ = lean_array_propagate_mark(v_data_3071_, v___x_3077_);
v___x_3079_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v___x_3075_, v_data_3071_, v___x_3078_);
return v___x_3079_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(lean_object* v_a_3080_, lean_object* v_x_3081_){
_start:
{
if (lean_obj_tag(v_x_3081_) == 0)
{
uint8_t v___x_3082_; 
v___x_3082_ = 0;
return v___x_3082_;
}
else
{
lean_object* v_key_3083_; lean_object* v_tail_3084_; uint8_t v___x_3085_; 
v_key_3083_ = lean_ctor_get(v_x_3081_, 0);
v_tail_3084_ = lean_ctor_get(v_x_3081_, 2);
v___x_3085_ = lean_string_dec_eq(v_key_3083_, v_a_3080_);
if (v___x_3085_ == 0)
{
v_x_3081_ = v_tail_3084_;
goto _start;
}
else
{
return v___x_3085_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3080_ = stack[0].m_obj;
lean_object* v_x_3081_ = stack[1].m_obj;
uint8_t v_res_3087_;
v_res_3087_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_3080_, v_x_3081_);
stack->m_num = v_res_3087_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg___boxed(lean_object* v_a_3088_, lean_object* v_x_3089_){
_start:
{
uint8_t v_res_3090_; lean_object* v_r_3091_; 
v_res_3090_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_3088_, v_x_3089_);
lean_dec(v_x_3089_);
lean_dec_ref(v_a_3088_);
v_r_3091_ = lean_box(v_res_3090_);
return v_r_3091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(lean_object* v_m_3092_, lean_object* v_a_3093_, lean_object* v_b_3094_){
_start:
{
lean_object* v_size_3095_; lean_object* v_buckets_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3139_; 
v_size_3095_ = lean_ctor_get(v_m_3092_, 0);
v_buckets_3096_ = lean_ctor_get(v_m_3092_, 1);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_m_3092_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3098_ = v_m_3092_;
v_isShared_3099_ = v_isSharedCheck_3139_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_buckets_3096_);
lean_inc(v_size_3095_);
lean_dec(v_m_3092_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3139_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3100_; uint64_t v___x_3101_; uint64_t v___x_3102_; uint64_t v___x_3103_; uint64_t v_fold_3104_; uint64_t v___x_3105_; uint64_t v___x_3106_; uint64_t v___x_3107_; size_t v___x_3108_; size_t v___x_3109_; size_t v___x_3110_; size_t v___x_3111_; size_t v___x_3112_; lean_object* v_bkt_3113_; uint8_t v___x_3114_; 
v___x_3100_ = lean_array_get_size(v_buckets_3096_);
v___x_3101_ = lean_string_hash(v_a_3093_);
v___x_3102_ = 32ULL;
v___x_3103_ = lean_uint64_shift_right(v___x_3101_, v___x_3102_);
v_fold_3104_ = lean_uint64_xor(v___x_3101_, v___x_3103_);
v___x_3105_ = 16ULL;
v___x_3106_ = lean_uint64_shift_right(v_fold_3104_, v___x_3105_);
v___x_3107_ = lean_uint64_xor(v_fold_3104_, v___x_3106_);
v___x_3108_ = lean_uint64_to_usize(v___x_3107_);
v___x_3109_ = lean_usize_of_nat(v___x_3100_);
v___x_3110_ = ((size_t)1ULL);
v___x_3111_ = lean_usize_sub(v___x_3109_, v___x_3110_);
v___x_3112_ = lean_usize_land(v___x_3108_, v___x_3111_);
v_bkt_3113_ = lean_array_uget_borrowed(v_buckets_3096_, v___x_3112_);
v___x_3114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_3093_, v_bkt_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v_size_x27_3116_; lean_object* v___x_3117_; lean_object* v_buckets_x27_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3115_ = lean_unsigned_to_nat(1u);
v_size_x27_3116_ = lean_nat_add(v_size_3095_, v___x_3115_);
lean_dec(v_size_3095_);
lean_inc(v_bkt_3113_);
v___x_3117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3117_, 0, v_a_3093_);
lean_ctor_set(v___x_3117_, 1, v_b_3094_);
lean_ctor_set(v___x_3117_, 2, v_bkt_3113_);
v_buckets_x27_3118_ = lean_array_uset(v_buckets_3096_, v___x_3112_, v___x_3117_);
v___x_3119_ = lean_unsigned_to_nat(4u);
v___x_3120_ = lean_nat_mul(v_size_x27_3116_, v___x_3119_);
v___x_3121_ = lean_unsigned_to_nat(3u);
v___x_3122_ = lean_nat_div(v___x_3120_, v___x_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_array_get_size(v_buckets_x27_3118_);
v___x_3124_ = lean_nat_dec_le(v___x_3122_, v___x_3123_);
lean_dec(v___x_3122_);
if (v___x_3124_ == 0)
{
lean_object* v_val_3125_; lean_object* v___x_3127_; 
v_val_3125_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_buckets_x27_3118_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 1, v_val_3125_);
lean_ctor_set(v___x_3098_, 0, v_size_x27_3116_);
v___x_3127_ = v___x_3098_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_size_x27_3116_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_val_3125_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
else
{
lean_object* v___x_3130_; 
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 1, v_buckets_x27_3118_);
lean_ctor_set(v___x_3098_, 0, v_size_x27_3116_);
v___x_3130_ = v___x_3098_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_size_x27_3116_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_buckets_x27_3118_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
else
{
lean_object* v___x_3132_; lean_object* v_buckets_x27_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3137_; 
lean_inc(v_bkt_3113_);
v___x_3132_ = lean_box(0);
v_buckets_x27_3133_ = lean_array_uset(v_buckets_3096_, v___x_3112_, v___x_3132_);
v___x_3134_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_3093_, v_b_3094_, v_bkt_3113_);
v___x_3135_ = lean_array_uset(v_buckets_x27_3133_, v___x_3112_, v___x_3134_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 1, v___x_3135_);
v___x_3137_ = v___x_3098_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_size_3095_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(lean_object* v_a_3140_, lean_object* v_x_3141_){
_start:
{
if (lean_obj_tag(v_x_3141_) == 0)
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_box(0);
return v___x_3142_;
}
else
{
lean_object* v_key_3143_; lean_object* v_value_3144_; lean_object* v_tail_3145_; uint8_t v___x_3146_; 
v_key_3143_ = lean_ctor_get(v_x_3141_, 0);
v_value_3144_ = lean_ctor_get(v_x_3141_, 1);
v_tail_3145_ = lean_ctor_get(v_x_3141_, 2);
v___x_3146_ = lean_string_dec_eq(v_key_3143_, v_a_3140_);
if (v___x_3146_ == 0)
{
v_x_3141_ = v_tail_3145_;
goto _start;
}
else
{
lean_object* v___x_3148_; 
lean_inc(v_value_3144_);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_value_3144_);
return v___x_3148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg___boxed(lean_object* v_a_3149_, lean_object* v_x_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3149_, v_x_3150_);
lean_dec(v_x_3150_);
lean_dec_ref(v_a_3149_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(lean_object* v_m_3152_, lean_object* v_a_3153_){
_start:
{
lean_object* v_buckets_3154_; lean_object* v___x_3155_; uint64_t v___x_3156_; uint64_t v___x_3157_; uint64_t v___x_3158_; uint64_t v_fold_3159_; uint64_t v___x_3160_; uint64_t v___x_3161_; uint64_t v___x_3162_; size_t v___x_3163_; size_t v___x_3164_; size_t v___x_3165_; size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v_buckets_3154_ = lean_ctor_get(v_m_3152_, 1);
v___x_3155_ = lean_array_get_size(v_buckets_3154_);
v___x_3156_ = lean_string_hash(v_a_3153_);
v___x_3157_ = 32ULL;
v___x_3158_ = lean_uint64_shift_right(v___x_3156_, v___x_3157_);
v_fold_3159_ = lean_uint64_xor(v___x_3156_, v___x_3158_);
v___x_3160_ = 16ULL;
v___x_3161_ = lean_uint64_shift_right(v_fold_3159_, v___x_3160_);
v___x_3162_ = lean_uint64_xor(v_fold_3159_, v___x_3161_);
v___x_3163_ = lean_uint64_to_usize(v___x_3162_);
v___x_3164_ = lean_usize_of_nat(v___x_3155_);
v___x_3165_ = ((size_t)1ULL);
v___x_3166_ = lean_usize_sub(v___x_3164_, v___x_3165_);
v___x_3167_ = lean_usize_land(v___x_3163_, v___x_3166_);
v___x_3168_ = lean_array_uget_borrowed(v_buckets_3154_, v___x_3167_);
v___x_3169_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3153_, v___x_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg___boxed(lean_object* v_m_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_3170_, v_a_3171_);
lean_dec_ref(v_a_3171_);
lean_dec_ref(v_m_3170_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(lean_object* v_histogram_3173_, lean_object* v_index_3174_, lean_object* v_val_3175_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3173_, v_val_3175_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3177_ = lean_unsigned_to_nat(1u);
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v_index_3174_);
v___x_3179_ = lean_unsigned_to_nat(0u);
v___x_3180_ = lean_box(0);
v___x_3181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3177_);
lean_ctor_set(v___x_3181_, 1, v___x_3178_);
lean_ctor_set(v___x_3181_, 2, v___x_3179_);
lean_ctor_set(v___x_3181_, 3, v___x_3180_);
v___x_3182_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3173_, v_val_3175_, v___x_3181_);
return v___x_3182_;
}
else
{
lean_object* v_val_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3204_; 
v_val_3183_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3185_ = v___x_3176_;
v_isShared_3186_ = v_isSharedCheck_3204_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_val_3183_);
lean_dec(v___x_3176_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3204_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_leftCount_3187_; lean_object* v_rightCount_3188_; lean_object* v_rightIndex_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3202_; 
v_leftCount_3187_ = lean_ctor_get(v_val_3183_, 0);
v_rightCount_3188_ = lean_ctor_get(v_val_3183_, 2);
v_rightIndex_3189_ = lean_ctor_get(v_val_3183_, 3);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_val_3183_);
if (v_isSharedCheck_3202_ == 0)
{
lean_object* v_unused_3203_; 
v_unused_3203_ = lean_ctor_get(v_val_3183_, 1);
lean_dec(v_unused_3203_);
v___x_3191_ = v_val_3183_;
v_isShared_3192_ = v_isSharedCheck_3202_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_rightIndex_3189_);
lean_inc(v_rightCount_3188_);
lean_inc(v_leftCount_3187_);
lean_dec(v_val_3183_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3202_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3196_; 
v___x_3193_ = lean_unsigned_to_nat(1u);
v___x_3194_ = lean_nat_add(v_leftCount_3187_, v___x_3193_);
lean_dec(v_leftCount_3187_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v_index_3174_);
v___x_3196_ = v___x_3185_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_index_3174_);
v___x_3196_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3198_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3196_);
lean_ctor_set(v___x_3191_, 0, v___x_3194_);
v___x_3198_ = v___x_3191_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3200_, 2, v_rightCount_3188_);
lean_ctor_set(v_reuseFailAlloc_3200_, 3, v_rightIndex_3189_);
v___x_3198_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3173_, v_val_3175_, v___x_3198_);
return v___x_3199_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(lean_object* v_upperBound_3205_, lean_object* v_fst_3206_, lean_object* v___x_3207_, lean_object* v_fst_3208_, lean_object* v_a_3209_, lean_object* v_b_3210_){
_start:
{
uint8_t v___x_3211_; 
v___x_3211_ = lean_nat_dec_lt(v_a_3209_, v_upperBound_3205_);
if (v___x_3211_ == 0)
{
lean_dec(v_a_3209_);
return v_b_3210_;
}
else
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3212_ = l_Subarray_get___redArg(v_fst_3208_, v_a_3209_);
lean_inc(v_a_3209_);
v___x_3213_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_b_3210_, v_a_3209_, v___x_3212_);
v___x_3214_ = lean_unsigned_to_nat(1u);
v___x_3215_ = lean_nat_add(v_a_3209_, v___x_3214_);
lean_dec(v_a_3209_);
v_a_3209_ = v___x_3215_;
v_b_3210_ = v___x_3213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_upperBound_3217_, lean_object* v_fst_3218_, lean_object* v___x_3219_, lean_object* v_fst_3220_, lean_object* v_a_3221_, lean_object* v_b_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3217_, v_fst_3218_, v___x_3219_, v_fst_3220_, v_a_3221_, v_b_3222_);
lean_dec_ref(v_fst_3220_);
lean_dec(v___x_3219_);
lean_dec_ref(v_fst_3218_);
lean_dec(v_upperBound_3217_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(lean_object* v_as_x27_3224_, lean_object* v_b_3225_){
_start:
{
if (lean_obj_tag(v_as_x27_3224_) == 0)
{
return v_b_3225_;
}
else
{
lean_object* v_head_3226_; lean_object* v_snd_3227_; lean_object* v_leftIndex_3228_; 
v_head_3226_ = lean_ctor_get(v_as_x27_3224_, 0);
v_snd_3227_ = lean_ctor_get(v_head_3226_, 1);
v_leftIndex_3228_ = lean_ctor_get(v_snd_3227_, 1);
if (lean_obj_tag(v_leftIndex_3228_) == 1)
{
lean_object* v_rightIndex_3229_; 
v_rightIndex_3229_ = lean_ctor_get(v_snd_3227_, 3);
if (lean_obj_tag(v_rightIndex_3229_) == 1)
{
if (lean_obj_tag(v_b_3225_) == 0)
{
lean_object* v_tail_3230_; lean_object* v_fst_3231_; lean_object* v_leftCount_3232_; lean_object* v_rightCount_3233_; lean_object* v_val_3234_; lean_object* v_val_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v_tail_3230_ = lean_ctor_get(v_as_x27_3224_, 1);
v_fst_3231_ = lean_ctor_get(v_head_3226_, 0);
v_leftCount_3232_ = lean_ctor_get(v_snd_3227_, 0);
v_rightCount_3233_ = lean_ctor_get(v_snd_3227_, 2);
v_val_3234_ = lean_ctor_get(v_leftIndex_3228_, 0);
v_val_3235_ = lean_ctor_get(v_rightIndex_3229_, 0);
v___x_3236_ = lean_nat_add(v_leftCount_3232_, v_rightCount_3233_);
lean_inc(v_val_3235_);
lean_inc(v_val_3234_);
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v_val_3234_);
lean_ctor_set(v___x_3237_, 1, v_val_3235_);
lean_inc(v_fst_3231_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v_fst_3231_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3236_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
v_as_x27_3224_ = v_tail_3230_;
v_b_3225_ = v___x_3240_;
goto _start;
}
else
{
lean_object* v_val_3242_; lean_object* v_tail_3243_; lean_object* v_fst_3244_; lean_object* v_leftCount_3245_; lean_object* v_rightCount_3246_; lean_object* v_val_3247_; lean_object* v_val_3248_; lean_object* v_fst_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3270_; 
v_val_3242_ = lean_ctor_get(v_b_3225_, 0);
lean_inc(v_val_3242_);
v_tail_3243_ = lean_ctor_get(v_as_x27_3224_, 1);
v_fst_3244_ = lean_ctor_get(v_head_3226_, 0);
v_leftCount_3245_ = lean_ctor_get(v_snd_3227_, 0);
v_rightCount_3246_ = lean_ctor_get(v_snd_3227_, 2);
v_val_3247_ = lean_ctor_get(v_leftIndex_3228_, 0);
v_val_3248_ = lean_ctor_get(v_rightIndex_3229_, 0);
v_fst_3249_ = lean_ctor_get(v_val_3242_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v_val_3242_);
if (v_isSharedCheck_3270_ == 0)
{
lean_object* v_unused_3271_; 
v_unused_3271_ = lean_ctor_get(v_val_3242_, 1);
lean_dec(v_unused_3271_);
v___x_3251_ = v_val_3242_;
v_isShared_3252_ = v_isSharedCheck_3270_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_fst_3249_);
lean_dec(v_val_3242_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3270_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = lean_nat_add(v_leftCount_3245_, v_rightCount_3246_);
v___x_3254_ = lean_nat_dec_lt(v___x_3253_, v_fst_3249_);
lean_dec(v_fst_3249_);
if (v___x_3254_ == 0)
{
lean_dec(v___x_3253_);
lean_del_object(v___x_3251_);
v_as_x27_3224_ = v_tail_3243_;
goto _start;
}
else
{
lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3268_; 
v_isSharedCheck_3268_ = !lean_is_exclusive(v_b_3225_);
if (v_isSharedCheck_3268_ == 0)
{
lean_object* v_unused_3269_; 
v_unused_3269_ = lean_ctor_get(v_b_3225_, 0);
lean_dec(v_unused_3269_);
v___x_3257_ = v_b_3225_;
v_isShared_3258_ = v_isSharedCheck_3268_;
goto v_resetjp_3256_;
}
else
{
lean_dec(v_b_3225_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3268_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
lean_inc(v_val_3248_);
lean_inc(v_val_3247_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 1, v_val_3248_);
lean_ctor_set(v___x_3251_, 0, v_val_3247_);
v___x_3260_ = v___x_3251_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_val_3247_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_val_3248_);
v___x_3260_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
lean_inc(v_fst_3244_);
v___x_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3261_, 0, v_fst_3244_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
v___x_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3253_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v___x_3262_);
v___x_3264_ = v___x_3257_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
v_as_x27_3224_ = v_tail_3243_;
v_b_3225_ = v___x_3264_;
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
lean_object* v_tail_3272_; 
v_tail_3272_ = lean_ctor_get(v_as_x27_3224_, 1);
v_as_x27_3224_ = v_tail_3272_;
goto _start;
}
}
else
{
lean_object* v_tail_3274_; 
v_tail_3274_ = lean_ctor_get(v_as_x27_3224_, 1);
v_as_x27_3224_ = v_tail_3274_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg___boxed(lean_object* v_as_x27_3276_, lean_object* v_b_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3276_, v_b_3277_);
lean_dec(v_as_x27_3276_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(lean_object* v_histogram_3279_, lean_object* v_index_3280_, lean_object* v_val_3281_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3279_, v_val_3281_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3283_ = lean_unsigned_to_nat(0u);
v___x_3284_ = lean_box(0);
v___x_3285_ = lean_unsigned_to_nat(1u);
v___x_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_index_3280_);
v___x_3287_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3283_);
lean_ctor_set(v___x_3287_, 1, v___x_3284_);
lean_ctor_set(v___x_3287_, 2, v___x_3285_);
lean_ctor_set(v___x_3287_, 3, v___x_3286_);
v___x_3288_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3279_, v_val_3281_, v___x_3287_);
return v___x_3288_;
}
else
{
lean_object* v_val_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3310_; 
v_val_3289_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3291_ = v___x_3282_;
v_isShared_3292_ = v_isSharedCheck_3310_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_val_3289_);
lean_dec(v___x_3282_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3310_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v_leftCount_3293_; lean_object* v_leftIndex_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3307_; 
v_leftCount_3293_ = lean_ctor_get(v_val_3289_, 0);
v_leftIndex_3294_ = lean_ctor_get(v_val_3289_, 1);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_val_3289_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; lean_object* v_unused_3309_; 
v_unused_3308_ = lean_ctor_get(v_val_3289_, 3);
lean_dec(v_unused_3308_);
v_unused_3309_ = lean_ctor_get(v_val_3289_, 2);
lean_dec(v_unused_3309_);
v___x_3296_ = v_val_3289_;
v_isShared_3297_ = v_isSharedCheck_3307_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_leftIndex_3294_);
lean_inc(v_leftCount_3293_);
lean_dec(v_val_3289_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3307_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3301_; 
v___x_3298_ = lean_unsigned_to_nat(1u);
v___x_3299_ = lean_nat_add(v_leftCount_3293_, v___x_3298_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v_index_3280_);
v___x_3301_ = v___x_3291_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_index_3280_);
v___x_3301_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
lean_object* v___x_3303_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 3, v___x_3301_);
lean_ctor_set(v___x_3296_, 2, v___x_3299_);
v___x_3303_ = v___x_3296_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_leftCount_3293_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_leftIndex_3294_);
lean_ctor_set(v_reuseFailAlloc_3305_, 2, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3305_, 3, v___x_3301_);
v___x_3303_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3279_, v_val_3281_, v___x_3303_);
return v___x_3304_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(lean_object* v_upperBound_3311_, lean_object* v___x_3312_, lean_object* v_fst_3313_, lean_object* v___x_3314_, lean_object* v_a_3315_, lean_object* v_b_3316_){
_start:
{
uint8_t v___x_3317_; 
v___x_3317_ = lean_nat_dec_lt(v_a_3315_, v_upperBound_3311_);
if (v___x_3317_ == 0)
{
lean_dec(v_a_3315_);
return v_b_3316_;
}
else
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3318_ = l_Subarray_get___redArg(v_fst_3313_, v_a_3315_);
lean_inc(v_a_3315_);
v___x_3319_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_b_3316_, v_a_3315_, v___x_3318_);
v___x_3320_ = lean_unsigned_to_nat(1u);
v___x_3321_ = lean_nat_add(v_a_3315_, v___x_3320_);
lean_dec(v_a_3315_);
v_a_3315_ = v___x_3321_;
v_b_3316_ = v___x_3319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg___boxed(lean_object* v_upperBound_3323_, lean_object* v___x_3324_, lean_object* v_fst_3325_, lean_object* v___x_3326_, lean_object* v_a_3327_, lean_object* v_b_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3323_, v___x_3324_, v_fst_3325_, v___x_3326_, v_a_3327_, v_b_3328_);
lean_dec(v___x_3326_);
lean_dec_ref(v_fst_3325_);
lean_dec(v___x_3324_);
lean_dec(v_upperBound_3323_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(lean_object* v_a_3330_, lean_object* v_b_3331_){
_start:
{
lean_object* v_array_3332_; lean_object* v_start_3333_; lean_object* v_stop_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3347_; 
v_array_3332_ = lean_ctor_get(v_a_3330_, 0);
v_start_3333_ = lean_ctor_get(v_a_3330_, 1);
v_stop_3334_ = lean_ctor_get(v_a_3330_, 2);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_a_3330_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3336_ = v_a_3330_;
v_isShared_3337_ = v_isSharedCheck_3347_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_stop_3334_);
lean_inc(v_start_3333_);
lean_inc(v_array_3332_);
lean_dec(v_a_3330_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3347_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
uint8_t v___x_3338_; 
v___x_3338_ = lean_nat_dec_lt(v_start_3333_, v_stop_3334_);
if (v___x_3338_ == 0)
{
lean_del_object(v___x_3336_);
lean_dec(v_stop_3334_);
lean_dec(v_start_3333_);
lean_dec_ref(v_array_3332_);
return v_b_3331_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3339_ = lean_unsigned_to_nat(1u);
v___x_3340_ = lean_nat_add(v_start_3333_, v___x_3339_);
lean_inc_ref(v_array_3332_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 1, v___x_3340_);
v___x_3342_ = v___x_3336_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_array_3332_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v___x_3340_);
lean_ctor_set(v_reuseFailAlloc_3346_, 2, v_stop_3334_);
v___x_3342_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = lean_array_fget(v_array_3332_, v_start_3333_);
lean_dec(v_start_3333_);
lean_dec_ref(v_array_3332_);
v___x_3344_ = lean_array_push(v_b_3331_, v___x_3343_);
v_a_3330_ = v___x_3342_;
v_b_3331_ = v___x_3344_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(lean_object* v_left_3348_, lean_object* v_right_3349_, lean_object* v_i_3350_){
_start:
{
lean_object* v_start_3351_; lean_object* v_stop_3352_; lean_object* v___x_3353_; uint8_t v___x_3367_; 
v_start_3351_ = lean_ctor_get(v_left_3348_, 1);
v_stop_3352_ = lean_ctor_get(v_left_3348_, 2);
v___x_3353_ = lean_nat_sub(v_stop_3352_, v_start_3351_);
v___x_3367_ = lean_nat_dec_lt(v_i_3350_, v___x_3353_);
if (v___x_3367_ == 0)
{
goto v___jp_3354_;
}
else
{
lean_object* v_start_3368_; lean_object* v_stop_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; 
v_start_3368_ = lean_ctor_get(v_right_3349_, 1);
v_stop_3369_ = lean_ctor_get(v_right_3349_, 2);
v___x_3370_ = lean_nat_sub(v_stop_3369_, v_start_3368_);
v___x_3371_ = lean_nat_dec_lt(v_i_3350_, v___x_3370_);
if (v___x_3371_ == 0)
{
lean_dec(v___x_3370_);
goto v___jp_3354_;
}
else
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3372_ = lean_nat_sub(v___x_3353_, v_i_3350_);
lean_dec(v___x_3353_);
v___x_3373_ = lean_unsigned_to_nat(1u);
v___x_3374_ = lean_nat_sub(v___x_3372_, v___x_3373_);
v___x_3375_ = l_Subarray_get___redArg(v_left_3348_, v___x_3374_);
lean_dec(v___x_3374_);
v___x_3376_ = lean_nat_sub(v___x_3370_, v_i_3350_);
lean_dec(v___x_3370_);
v___x_3377_ = lean_nat_sub(v___x_3376_, v___x_3373_);
v___x_3378_ = l_Subarray_get___redArg(v_right_3349_, v___x_3377_);
lean_dec(v___x_3377_);
v___x_3379_ = lean_string_dec_eq(v___x_3375_, v___x_3378_);
lean_dec(v___x_3378_);
lean_dec(v___x_3375_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
lean_dec(v_i_3350_);
lean_inc_ref(v_left_3348_);
v___x_3380_ = l_Subarray_take___redArg(v_left_3348_, v___x_3372_);
v___x_3381_ = l_Subarray_take___redArg(v_right_3349_, v___x_3376_);
lean_dec(v___x_3376_);
v___x_3382_ = l_Subarray_drop___redArg(v_left_3348_, v___x_3372_);
lean_dec(v___x_3372_);
v___x_3383_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3384_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3382_, v___x_3383_);
v___x_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3381_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3380_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
return v___x_3386_;
}
else
{
lean_object* v___x_3387_; 
lean_dec(v___x_3376_);
lean_dec(v___x_3372_);
v___x_3387_ = lean_nat_add(v_i_3350_, v___x_3373_);
lean_dec(v_i_3350_);
v_i_3350_ = v___x_3387_;
goto _start;
}
}
}
v___jp_3354_:
{
lean_object* v_start_3355_; lean_object* v_stop_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_start_3355_ = lean_ctor_get(v_right_3349_, 1);
v_stop_3356_ = lean_ctor_get(v_right_3349_, 2);
v___x_3357_ = lean_nat_sub(v___x_3353_, v_i_3350_);
lean_dec(v___x_3353_);
lean_inc_ref(v_left_3348_);
v___x_3358_ = l_Subarray_take___redArg(v_left_3348_, v___x_3357_);
v___x_3359_ = lean_nat_sub(v_stop_3356_, v_start_3355_);
v___x_3360_ = lean_nat_sub(v___x_3359_, v_i_3350_);
lean_dec(v_i_3350_);
lean_dec(v___x_3359_);
v___x_3361_ = l_Subarray_take___redArg(v_right_3349_, v___x_3360_);
lean_dec(v___x_3360_);
v___x_3362_ = l_Subarray_drop___redArg(v_left_3348_, v___x_3357_);
lean_dec(v___x_3357_);
v___x_3363_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3364_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3362_, v___x_3363_);
v___x_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3361_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3358_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(lean_object* v_left_3389_, lean_object* v_right_3390_){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = lean_unsigned_to_nat(0u);
v___x_3392_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(v_left_3389_, v_right_3390_, v___x_3391_);
return v___x_3392_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = lean_box(0);
v___x_3394_ = lean_unsigned_to_nat(16u);
v___x_3395_ = lean_mk_array(v___x_3394_, v___x_3393_);
return v___x_3395_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v_hist_3398_; 
v___x_3396_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0);
v___x_3397_ = lean_unsigned_to_nat(0u);
v_hist_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3398_, 0, v___x_3397_);
lean_ctor_set(v_hist_3398_, 1, v___x_3396_);
return v_hist_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_left_3399_, lean_object* v_right_3400_){
_start:
{
lean_object* v___x_3401_; lean_object* v_snd_3402_; lean_object* v_fst_3403_; lean_object* v_fst_3404_; lean_object* v_snd_3405_; lean_object* v___x_3406_; lean_object* v_snd_3407_; lean_object* v_fst_3408_; lean_object* v_fst_3409_; lean_object* v_snd_3410_; lean_object* v_start_3411_; lean_object* v_stop_3412_; lean_object* v___x_3413_; lean_object* v_hist_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v_start_3417_; lean_object* v_stop_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v_buckets_3421_; lean_object* v___x_3422_; lean_object* v___y_3424_; lean_object* v___x_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
v___x_3401_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(v_left_3399_, v_right_3400_);
v_snd_3402_ = lean_ctor_get(v___x_3401_, 1);
lean_inc(v_snd_3402_);
v_fst_3403_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_fst_3403_);
lean_dec_ref(v___x_3401_);
v_fst_3404_ = lean_ctor_get(v_snd_3402_, 0);
lean_inc(v_fst_3404_);
v_snd_3405_ = lean_ctor_get(v_snd_3402_, 1);
lean_inc(v_snd_3405_);
lean_dec(v_snd_3402_);
v___x_3406_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(v_fst_3404_, v_snd_3405_);
v_snd_3407_ = lean_ctor_get(v___x_3406_, 1);
lean_inc(v_snd_3407_);
v_fst_3408_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_fst_3408_);
lean_dec_ref(v___x_3406_);
v_fst_3409_ = lean_ctor_get(v_snd_3407_, 0);
lean_inc(v_fst_3409_);
v_snd_3410_ = lean_ctor_get(v_snd_3407_, 1);
lean_inc(v_snd_3410_);
lean_dec(v_snd_3407_);
v_start_3411_ = lean_ctor_get(v_fst_3408_, 1);
v_stop_3412_ = lean_ctor_get(v_fst_3408_, 2);
v___x_3413_ = lean_unsigned_to_nat(0u);
v_hist_3414_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1);
v___x_3415_ = lean_nat_sub(v_stop_3412_, v_start_3411_);
v___x_3416_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v___x_3415_, v_fst_3409_, v___x_3415_, v_fst_3408_, v___x_3413_, v_hist_3414_);
v_start_3417_ = lean_ctor_get(v_fst_3409_, 1);
v_stop_3418_ = lean_ctor_get(v_fst_3409_, 2);
v___x_3419_ = lean_nat_sub(v_stop_3418_, v_start_3417_);
v___x_3420_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v___x_3419_, v___x_3419_, v_fst_3409_, v___x_3415_, v___x_3413_, v___x_3416_);
lean_dec(v___x_3415_);
lean_dec(v___x_3419_);
v_buckets_3421_ = lean_ctor_get(v___x_3420_, 1);
lean_inc_ref(v_buckets_3421_);
lean_dec_ref(v___x_3420_);
v___x_3422_ = lean_box(0);
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_array_get_size(v_buckets_3421_);
v___x_3452_ = lean_nat_dec_lt(v___x_3413_, v___x_3451_);
if (v___x_3452_ == 0)
{
lean_dec_ref(v_buckets_3421_);
v___y_3424_ = v___x_3450_;
goto v___jp_3423_;
}
else
{
size_t v___x_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
v___x_3453_ = lean_usize_of_nat(v___x_3451_);
v___x_3454_ = ((size_t)0ULL);
v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_buckets_3421_, v___x_3453_, v___x_3454_, v___x_3450_);
lean_dec_ref(v_buckets_3421_);
v___y_3424_ = v___x_3455_;
goto v___jp_3423_;
}
v___jp_3423_:
{
lean_object* v___x_3425_; 
v___x_3425_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v___y_3424_, v___x_3422_);
lean_dec(v___y_3424_);
if (lean_obj_tag(v___x_3425_) == 1)
{
lean_object* v_val_3426_; lean_object* v_snd_3427_; lean_object* v_snd_3428_; lean_object* v_fst_3429_; lean_object* v_fst_3430_; lean_object* v_snd_3431_; lean_object* v___x_3432_; lean_object* v_fst_3433_; lean_object* v_snd_3434_; lean_object* v___x_3435_; lean_object* v_fst_3436_; lean_object* v_snd_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v_val_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_val_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v_snd_3427_ = lean_ctor_get(v_val_3426_, 1);
lean_inc(v_snd_3427_);
lean_dec(v_val_3426_);
v_snd_3428_ = lean_ctor_get(v_snd_3427_, 1);
lean_inc(v_snd_3428_);
v_fst_3429_ = lean_ctor_get(v_snd_3427_, 0);
lean_inc(v_fst_3429_);
lean_dec(v_snd_3427_);
v_fst_3430_ = lean_ctor_get(v_snd_3428_, 0);
lean_inc(v_fst_3430_);
v_snd_3431_ = lean_ctor_get(v_snd_3428_, 1);
lean_inc(v_snd_3431_);
lean_dec(v_snd_3428_);
v___x_3432_ = l_Subarray_split___redArg(v_fst_3408_, v_fst_3430_);
lean_dec(v_fst_3430_);
v_fst_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_fst_3433_);
v_snd_3434_ = lean_ctor_get(v___x_3432_, 1);
lean_inc(v_snd_3434_);
lean_dec_ref(v___x_3432_);
v___x_3435_ = l_Subarray_split___redArg(v_fst_3409_, v_snd_3431_);
lean_dec(v_snd_3431_);
v_fst_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_fst_3436_);
v_snd_3437_ = lean_ctor_get(v___x_3435_, 1);
lean_inc(v_snd_3437_);
lean_dec_ref(v___x_3435_);
v___x_3438_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_fst_3433_, v_fst_3436_);
v___x_3439_ = l_Array_append___redArg(v_fst_3403_, v___x_3438_);
lean_dec_ref(v___x_3438_);
v___x_3440_ = lean_unsigned_to_nat(1u);
v___x_3441_ = lean_mk_empty_array_with_capacity(v___x_3440_);
v___x_3442_ = lean_array_push(v___x_3441_, v_fst_3429_);
v___x_3443_ = l_Array_append___redArg(v___x_3439_, v___x_3442_);
lean_dec_ref(v___x_3442_);
v___x_3444_ = l_Subarray_drop___redArg(v_snd_3434_, v___x_3440_);
v___x_3445_ = l_Subarray_drop___redArg(v_snd_3437_, v___x_3440_);
v___x_3446_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3444_, v___x_3445_);
v___x_3447_ = l_Array_append___redArg(v___x_3443_, v___x_3446_);
lean_dec_ref(v___x_3446_);
v___x_3448_ = l_Array_append___redArg(v___x_3447_, v_snd_3410_);
lean_dec(v_snd_3410_);
return v___x_3448_;
}
else
{
lean_object* v___x_3449_; 
lean_dec(v___x_3425_);
lean_dec(v_fst_3409_);
lean_dec(v_fst_3408_);
v___x_3449_ = l_Array_append___redArg(v_fst_3403_, v_snd_3410_);
lean_dec(v_snd_3410_);
return v___x_3449_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3456_, size_t v_i_3457_, lean_object* v_bs_3458_){
_start:
{
uint8_t v___x_3459_; 
v___x_3459_ = lean_usize_dec_lt(v_i_3457_, v_sz_3456_);
if (v___x_3459_ == 0)
{
return v_bs_3458_;
}
else
{
lean_object* v_v_3460_; lean_object* v___x_3461_; lean_object* v_bs_x27_3462_; uint8_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; size_t v___x_3466_; size_t v___x_3467_; lean_object* v___x_3468_; 
v_v_3460_ = lean_array_uget(v_bs_3458_, v_i_3457_);
v___x_3461_ = lean_unsigned_to_nat(0u);
v_bs_x27_3462_ = lean_array_uset(v_bs_3458_, v_i_3457_, v___x_3461_);
v___x_3463_ = 1;
v___x_3464_ = lean_box(v___x_3463_);
v___x_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
lean_ctor_set(v___x_3465_, 1, v_v_3460_);
v___x_3466_ = ((size_t)1ULL);
v___x_3467_ = lean_usize_add(v_i_3457_, v___x_3466_);
v___x_3468_ = lean_array_uset(v_bs_x27_3462_, v_i_3457_, v___x_3465_);
v_i_3457_ = v___x_3467_;
v_bs_3458_ = v___x_3468_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3456_ = stack[0].m_num;
size_t v_i_3457_ = stack[1].m_num;
lean_object* v_bs_3458_ = stack[2].m_obj;
lean_object* v_res_3470_;
v_res_3470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3456_, v_i_3457_, v_bs_3458_);
stack->m_obj
 = v_res_3470_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3471_, lean_object* v_i_3472_, lean_object* v_bs_3473_){
_start:
{
size_t v_sz_boxed_3474_; size_t v_i_boxed_3475_; lean_object* v_res_3476_; 
v_sz_boxed_3474_ = lean_unbox_usize(v_sz_3471_);
lean_dec(v_sz_3471_);
v_i_boxed_3475_ = lean_unbox_usize(v_i_3472_);
lean_dec(v_i_3472_);
v_res_3476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3474_, v_i_boxed_3475_, v_bs_3473_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3484_, lean_object* v_edited_3485_){
_start:
{
lean_object* v_i_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
v_i_3486_ = lean_unsigned_to_nat(0u);
v___x_3487_ = lean_array_get_size(v_original_3484_);
v___x_3488_ = lean_nat_dec_lt(v_i_3486_, v___x_3487_);
if (v___x_3488_ == 0)
{
size_t v_sz_3489_; size_t v___x_3490_; lean_object* v___x_3491_; 
lean_dec_ref(v_original_3484_);
v_sz_3489_ = lean_array_size(v_edited_3485_);
v___x_3490_ = ((size_t)0ULL);
v___x_3491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3489_, v___x_3490_, v_edited_3485_);
return v___x_3491_;
}
else
{
lean_object* v___x_3492_; uint8_t v___x_3493_; 
v___x_3492_ = lean_array_get_size(v_edited_3485_);
v___x_3493_ = lean_nat_dec_lt(v_i_3486_, v___x_3492_);
if (v___x_3493_ == 0)
{
size_t v_sz_3494_; size_t v___x_3495_; lean_object* v___x_3496_; 
lean_dec_ref(v_edited_3485_);
v_sz_3494_ = lean_array_size(v_original_3484_);
v___x_3495_ = ((size_t)0ULL);
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3494_, v___x_3495_, v_original_3484_);
return v___x_3496_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v_ds_3499_; lean_object* v___x_3500_; size_t v_sz_3501_; size_t v___x_3502_; lean_object* v___x_3503_; lean_object* v_snd_3504_; lean_object* v_fst_3505_; lean_object* v_fst_3506_; lean_object* v_snd_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3526_; 
lean_inc_ref(v_original_3484_);
v___x_3497_ = l_Array_toSubarray___redArg(v_original_3484_, v_i_3486_, v___x_3487_);
lean_inc_ref(v_edited_3485_);
v___x_3498_ = l_Array_toSubarray___redArg(v_edited_3485_, v_i_3486_, v___x_3492_);
v_ds_3499_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3497_, v___x_3498_);
v___x_3500_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3501_ = lean_array_size(v_ds_3499_);
v___x_3502_ = ((size_t)0ULL);
v___x_3503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_3492_, v_edited_3485_, v___x_3487_, v_original_3484_, v_ds_3499_, v_sz_3501_, v___x_3502_, v___x_3500_);
lean_dec_ref(v_ds_3499_);
v_snd_3504_ = lean_ctor_get(v___x_3503_, 1);
lean_inc(v_snd_3504_);
v_fst_3505_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_fst_3505_);
lean_dec_ref(v___x_3503_);
v_fst_3506_ = lean_ctor_get(v_snd_3504_, 0);
v_snd_3507_ = lean_ctor_get(v_snd_3504_, 1);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_snd_3504_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3509_ = v_snd_3504_;
v_isShared_3510_ = v_isSharedCheck_3526_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_snd_3507_);
lean_inc(v_fst_3506_);
lean_dec(v_snd_3504_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3526_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 1, v_fst_3506_);
lean_ctor_set(v___x_3509_, 0, v_fst_3505_);
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_fst_3505_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_fst_3506_);
v___x_3512_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3513_; lean_object* v_fst_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3523_; 
v___x_3513_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3487_, v_original_3484_, v___x_3512_);
lean_dec_ref(v_original_3484_);
v_fst_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3523_ == 0)
{
lean_object* v_unused_3524_; 
v_unused_3524_ = lean_ctor_get(v___x_3513_, 1);
lean_dec(v_unused_3524_);
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3523_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_fst_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3523_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 1, v_snd_3507_);
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_fst_3514_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_snd_3507_);
v___x_3519_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3520_; lean_object* v_fst_3521_; 
v___x_3520_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3492_, v_edited_3485_, v___x_3519_);
lean_dec_ref(v_edited_3485_);
v_fst_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_fst_3521_);
lean_dec_ref(v___x_3520_);
return v_fst_3521_;
}
}
}
}
}
}
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3527_, lean_object* v_x_3528_, lean_object* v_x_3529_){
_start:
{
if (lean_obj_tag(v_x_3528_) == 0)
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = l_List_reverse___redArg(v_x_3529_);
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
return v___x_3532_;
}
else
{
lean_object* v_head_3533_; lean_object* v_tail_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3543_; 
v_head_3533_ = lean_ctor_get(v_x_3528_, 0);
v_tail_3534_ = lean_ctor_get(v_x_3528_, 1);
v_isSharedCheck_3543_ = !lean_is_exclusive(v_x_3528_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3536_ = v_x_3528_;
v_isShared_3537_ = v_isSharedCheck_3543_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_tail_3534_);
lean_inc(v_head_3533_);
lean_dec(v_x_3528_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3543_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3538_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3533_, v___y_3527_);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 1, v_x_3529_);
lean_ctor_set(v___x_3536_, 0, v___x_3538_);
v___x_3540_ = v___x_3536_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_x_3529_);
v___x_3540_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
v_x_3528_ = v_tail_3534_;
v_x_3529_ = v___x_3540_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3527_ = stack[0].m_obj;
lean_object* v_x_3528_ = stack[1].m_obj;
lean_object* v_x_3529_ = stack[2].m_obj;
lean_object* v_res_3544_;
v_res_3544_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3527_, v_x_3528_, v_x_3529_);
stack->m_obj
 = v_res_3544_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3545_, lean_object* v_x_3546_, lean_object* v_x_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3545_, v_x_3546_, v_x_3547_);
lean_dec(v___y_3545_);
return v_res_3549_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3556_ = l_Lean_stringToMessageData(v___x_3555_);
return v___x_3556_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = l_Lean_MessageLog_empty;
v___x_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
return v___x_3559_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3570_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
lean_inc(v_x_3566_);
v___x_3571_ = l_Lean_Syntax_isOfKind(v_x_3566_, v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; 
lean_dec(v_x_3566_);
v___x_3572_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3572_;
}
else
{
lean_object* v___x_3573_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; uint8_t v___y_3614_; lean_object* v___y_3679_; uint8_t v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; uint8_t v___y_3688_; uint8_t v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v_dc_x3f_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___x_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v___x_3573_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3822_ = lean_unsigned_to_nat(0u);
v___x_3823_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3822_);
v___x_3824_ = l_Lean_Syntax_isNone(v___x_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; uint8_t v___x_3826_; 
v___x_3825_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3823_);
v___x_3826_ = l_Lean_Syntax_matchesNull(v___x_3823_, v___x_3825_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3827_; 
lean_dec(v___x_3823_);
lean_dec(v_x_3566_);
v___x_3827_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3827_;
}
else
{
lean_object* v_dc_x3f_3828_; 
v_dc_x3f_3828_ = l_Lean_Syntax_getArg(v___x_3823_, v___x_3822_);
lean_dec(v___x_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3831_; uint8_t v___x_3832_; 
v___x_3831_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3828_);
v___x_3832_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3828_, v___x_3831_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; 
lean_dec(v_dc_x3f_3828_);
lean_dec(v_x_3566_);
v___x_3833_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3833_;
}
else
{
goto v___jp_3829_;
}
}
else
{
goto v___jp_3829_;
}
v___jp_3829_:
{
lean_object* v___x_3830_; 
v___x_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3830_, 0, v_dc_x3f_3828_);
v_dc_x3f_3803_ = v___x_3830_;
v___y_3804_ = v_a_3567_;
v___y_3805_ = v_a_3568_;
goto v___jp_3802_;
}
}
}
else
{
lean_object* v___x_3834_; 
lean_dec(v___x_3823_);
v___x_3834_ = lean_box(0);
v_dc_x3f_3803_ = v___x_3834_;
v___y_3804_ = v_a_3567_;
v___y_3805_ = v_a_3568_;
goto v___jp_3802_;
}
v___jp_3574_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3580_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3581_ = l_Lean_stringToMessageData(v___y_3579_);
v___x_3582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3580_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
v___x_3583_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3578_, v___x_3582_, v___y_3577_, v___y_3575_);
lean_dec(v___y_3578_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3603_; 
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v___x_3583_, 0);
lean_dec(v_unused_3604_);
v___x_3585_ = v___x_3583_;
v_isShared_3586_ = v_isSharedCheck_3603_;
goto v_resetjp_3584_;
}
else
{
lean_dec(v___x_3583_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3603_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_Elab_Command_getRef___redArg(v___y_3577_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_a_3588_);
lean_dec_ref_known(v___x_3587_, 1);
v___x_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3573_);
lean_ctor_set(v___x_3589_, 1, v___y_3576_);
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v_a_3588_);
lean_ctor_set(v___x_3590_, 1, v___x_3589_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set_tag(v___x_3585_, 10);
lean_ctor_set(v___x_3585_, 0, v___x_3590_);
v___x_3592_ = v___x_3585_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3593_; 
v___x_3593_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3592_, v___y_3577_, v___y_3575_);
return v___x_3593_;
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_del_object(v___x_3585_);
lean_dec_ref(v___y_3576_);
v_a_3595_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3587_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3587_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3576_);
return v___x_3583_;
}
}
v___jp_3605_:
{
if (v___y_3614_ == 0)
{
lean_object* v___x_3615_; lean_object* v_env_3616_; lean_object* v_scopes_3617_; lean_object* v_usedQuotCtxts_3618_; lean_object* v_nextMacroScope_3619_; lean_object* v_maxRecDepth_3620_; lean_object* v_ngen_3621_; lean_object* v_auxDeclNGen_3622_; lean_object* v_infoState_3623_; lean_object* v_traceState_3624_; lean_object* v_snapshotTasks_3625_; lean_object* v_prevLinterStates_3626_; lean_object* v_codeQualityEntryTasks_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v___y_3607_);
v___x_3615_ = lean_st_ref_take(v___y_3606_);
v_env_3616_ = lean_ctor_get(v___x_3615_, 0);
v_scopes_3617_ = lean_ctor_get(v___x_3615_, 2);
v_usedQuotCtxts_3618_ = lean_ctor_get(v___x_3615_, 3);
v_nextMacroScope_3619_ = lean_ctor_get(v___x_3615_, 4);
v_maxRecDepth_3620_ = lean_ctor_get(v___x_3615_, 5);
v_ngen_3621_ = lean_ctor_get(v___x_3615_, 6);
v_auxDeclNGen_3622_ = lean_ctor_get(v___x_3615_, 7);
v_infoState_3623_ = lean_ctor_get(v___x_3615_, 8);
v_traceState_3624_ = lean_ctor_get(v___x_3615_, 9);
v_snapshotTasks_3625_ = lean_ctor_get(v___x_3615_, 10);
v_prevLinterStates_3626_ = lean_ctor_get(v___x_3615_, 11);
v_codeQualityEntryTasks_3627_ = lean_ctor_get(v___x_3615_, 12);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3652_ == 0)
{
lean_object* v_unused_3653_; 
v_unused_3653_ = lean_ctor_get(v___x_3615_, 1);
lean_dec(v_unused_3653_);
v___x_3629_ = v___x_3615_;
v_isShared_3630_ = v_isSharedCheck_3652_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3627_);
lean_inc(v_prevLinterStates_3626_);
lean_inc(v_snapshotTasks_3625_);
lean_inc(v_traceState_3624_);
lean_inc(v_infoState_3623_);
lean_inc(v_auxDeclNGen_3622_);
lean_inc(v_ngen_3621_);
lean_inc(v_maxRecDepth_3620_);
lean_inc(v_nextMacroScope_3619_);
lean_inc(v_usedQuotCtxts_3618_);
lean_inc(v_scopes_3617_);
lean_inc(v_env_3616_);
lean_dec(v___x_3615_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3652_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 1, v___y_3611_);
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_env_3616_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v___y_3611_);
lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_scopes_3617_);
lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_usedQuotCtxts_3618_);
lean_ctor_set(v_reuseFailAlloc_3651_, 4, v_nextMacroScope_3619_);
lean_ctor_set(v_reuseFailAlloc_3651_, 5, v_maxRecDepth_3620_);
lean_ctor_set(v_reuseFailAlloc_3651_, 6, v_ngen_3621_);
lean_ctor_set(v_reuseFailAlloc_3651_, 7, v_auxDeclNGen_3622_);
lean_ctor_set(v_reuseFailAlloc_3651_, 8, v_infoState_3623_);
lean_ctor_set(v_reuseFailAlloc_3651_, 9, v_traceState_3624_);
lean_ctor_set(v_reuseFailAlloc_3651_, 10, v_snapshotTasks_3625_);
lean_ctor_set(v_reuseFailAlloc_3651_, 11, v_prevLinterStates_3626_);
lean_ctor_set(v_reuseFailAlloc_3651_, 12, v_codeQualityEntryTasks_3627_);
v___x_3632_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v_scopes_3636_; lean_object* v___x_3637_; lean_object* v_opts_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3633_ = lean_st_ref_put(v___y_3606_, v___x_3632_);
v___x_3634_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3635_ = lean_st_ref_get(v___y_3606_);
v_scopes_3636_ = lean_ctor_get(v___x_3635_, 2);
lean_inc(v_scopes_3636_);
lean_dec(v___x_3635_);
v___x_3637_ = l_List_head_x21___redArg(v___x_3634_, v_scopes_3636_);
lean_dec(v_scopes_3636_);
v_opts_3638_ = lean_ctor_get(v___x_3637_, 1);
lean_inc_ref(v_opts_3638_);
lean_dec(v___x_3637_);
v___x_3639_ = l_Lean_guard__msgs_diff;
v___x_3640_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3638_, v___x_3639_);
lean_dec_ref(v_opts_3638_);
if (v___x_3640_ == 0)
{
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3608_);
lean_inc_ref(v___y_3609_);
v___y_3575_ = v___y_3606_;
v___y_3576_ = v___y_3609_;
v___y_3577_ = v___y_3610_;
v___y_3578_ = v___y_3612_;
v___y_3579_ = v___y_3609_;
goto v___jp_3574_;
}
else
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3641_ = lean_string_utf8_byte_size(v___y_3608_);
lean_inc(v___y_3613_);
lean_inc_ref(v___y_3608_);
v___x_3642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3642_, 0, v___y_3608_);
lean_ctor_set(v___x_3642_, 1, v___y_3613_);
lean_ctor_set(v___x_3642_, 2, v___x_3641_);
v___x_3643_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
v___x_3644_ = lean_mk_empty_array_with_capacity(v___y_3613_);
lean_inc_ref(v___x_3644_);
v___x_3645_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3608_, v___x_3642_, v___x_3641_, v___x_3643_, v___x_3644_);
lean_dec_ref_known(v___x_3642_, 3);
v___x_3646_ = lean_string_utf8_byte_size(v___y_3609_);
lean_inc_ref_n(v___y_3609_, 2);
v___x_3647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3647_, 0, v___y_3609_);
lean_ctor_set(v___x_3647_, 1, v___y_3613_);
lean_ctor_set(v___x_3647_, 2, v___x_3646_);
v___x_3648_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3609_, v___x_3647_, v___x_3646_, v___x_3643_, v___x_3644_);
lean_dec_ref_known(v___x_3647_, 3);
v___x_3649_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3645_, v___x_3648_);
v___x_3650_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3649_);
lean_dec_ref(v___x_3649_);
v___y_3575_ = v___y_3606_;
v___y_3576_ = v___y_3609_;
v___y_3577_ = v___y_3610_;
v___y_3578_ = v___y_3612_;
v___y_3579_ = v___x_3650_;
goto v___jp_3574_;
}
}
}
}
else
{
lean_object* v___x_3654_; lean_object* v_env_3655_; lean_object* v_scopes_3656_; lean_object* v_usedQuotCtxts_3657_; lean_object* v_nextMacroScope_3658_; lean_object* v_maxRecDepth_3659_; lean_object* v_ngen_3660_; lean_object* v_auxDeclNGen_3661_; lean_object* v_infoState_3662_; lean_object* v_traceState_3663_; lean_object* v_snapshotTasks_3664_; lean_object* v_prevLinterStates_3665_; lean_object* v_codeQualityEntryTasks_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3676_; 
lean_dec(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v___y_3608_);
v___x_3654_ = lean_st_ref_take(v___y_3606_);
v_env_3655_ = lean_ctor_get(v___x_3654_, 0);
v_scopes_3656_ = lean_ctor_get(v___x_3654_, 2);
v_usedQuotCtxts_3657_ = lean_ctor_get(v___x_3654_, 3);
v_nextMacroScope_3658_ = lean_ctor_get(v___x_3654_, 4);
v_maxRecDepth_3659_ = lean_ctor_get(v___x_3654_, 5);
v_ngen_3660_ = lean_ctor_get(v___x_3654_, 6);
v_auxDeclNGen_3661_ = lean_ctor_get(v___x_3654_, 7);
v_infoState_3662_ = lean_ctor_get(v___x_3654_, 8);
v_traceState_3663_ = lean_ctor_get(v___x_3654_, 9);
v_snapshotTasks_3664_ = lean_ctor_get(v___x_3654_, 10);
v_prevLinterStates_3665_ = lean_ctor_get(v___x_3654_, 11);
v_codeQualityEntryTasks_3666_ = lean_ctor_get(v___x_3654_, 12);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3676_ == 0)
{
lean_object* v_unused_3677_; 
v_unused_3677_ = lean_ctor_get(v___x_3654_, 1);
lean_dec(v_unused_3677_);
v___x_3668_ = v___x_3654_;
v_isShared_3669_ = v_isSharedCheck_3676_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3666_);
lean_inc(v_prevLinterStates_3665_);
lean_inc(v_snapshotTasks_3664_);
lean_inc(v_traceState_3663_);
lean_inc(v_infoState_3662_);
lean_inc(v_auxDeclNGen_3661_);
lean_inc(v_ngen_3660_);
lean_inc(v_maxRecDepth_3659_);
lean_inc(v_nextMacroScope_3658_);
lean_inc(v_usedQuotCtxts_3657_);
lean_inc(v_scopes_3656_);
lean_inc(v_env_3655_);
lean_dec(v___x_3654_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3676_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3670_ = lean_box(0);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 1, v___y_3607_);
v___x_3672_ = v___x_3668_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_env_3655_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v___y_3607_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_scopes_3656_);
lean_ctor_set(v_reuseFailAlloc_3675_, 3, v_usedQuotCtxts_3657_);
lean_ctor_set(v_reuseFailAlloc_3675_, 4, v_nextMacroScope_3658_);
lean_ctor_set(v_reuseFailAlloc_3675_, 5, v_maxRecDepth_3659_);
lean_ctor_set(v_reuseFailAlloc_3675_, 6, v_ngen_3660_);
lean_ctor_set(v_reuseFailAlloc_3675_, 7, v_auxDeclNGen_3661_);
lean_ctor_set(v_reuseFailAlloc_3675_, 8, v_infoState_3662_);
lean_ctor_set(v_reuseFailAlloc_3675_, 9, v_traceState_3663_);
lean_ctor_set(v_reuseFailAlloc_3675_, 10, v_snapshotTasks_3664_);
lean_ctor_set(v_reuseFailAlloc_3675_, 11, v_prevLinterStates_3665_);
lean_ctor_set(v_reuseFailAlloc_3675_, 12, v_codeQualityEntryTasks_3666_);
v___x_3672_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = lean_st_ref_put(v___y_3606_, v___x_3672_);
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3670_);
return v___x_3674_;
}
}
}
}
v___jp_3678_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v_a_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v_str_3701_; lean_object* v_startInclusive_3702_; lean_object* v_endExclusive_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3718_; 
v___x_3691_ = l_Lean_MessageLog_toList(v___y_3685_);
lean_dec(v___y_3685_);
v___x_3692_ = lean_box(0);
v___x_3693_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3690_, v___x_3691_, v___x_3692_);
lean_dec(v___y_3690_);
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref(v___x_3693_);
v___x_3695_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3689_, v_a_3694_);
v___x_3696_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4));
v___x_3697_ = l_String_intercalate(v___x_3696_, v___x_3695_);
v___x_3698_ = lean_string_utf8_byte_size(v___x_3697_);
lean_inc(v___y_3687_);
v___x_3699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3697_);
lean_ctor_set(v___x_3699_, 1, v___y_3687_);
lean_ctor_set(v___x_3699_, 2, v___x_3698_);
v___x_3700_ = l_String_Slice_trimAscii(v___x_3699_);
v_str_3701_ = lean_ctor_get(v___x_3700_, 0);
v_startInclusive_3702_ = lean_ctor_get(v___x_3700_, 1);
v_endExclusive_3703_ = lean_ctor_get(v___x_3700_, 2);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3705_ = v___x_3700_;
v_isShared_3706_ = v_isSharedCheck_3718_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_endExclusive_3703_);
lean_inc(v_startInclusive_3702_);
lean_inc(v_str_3701_);
lean_dec(v___x_3700_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3718_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; 
v___x_3707_ = lean_string_utf8_extract_fast(v_str_3701_, v_startInclusive_3702_, v_endExclusive_3703_);
lean_dec(v_endExclusive_3703_);
lean_dec(v_startInclusive_3702_);
lean_dec_ref(v_str_3701_);
if (v___y_3688_ == 0)
{
lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; 
lean_del_object(v___x_3705_);
lean_inc_ref(v___y_3682_);
v___x_3708_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3680_, v___y_3682_);
lean_inc_ref(v___x_3707_);
v___x_3709_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3680_, v___x_3707_);
v___x_3710_ = lean_string_dec_eq(v___x_3708_, v___x_3709_);
lean_dec_ref(v___x_3709_);
lean_dec_ref(v___x_3708_);
v___y_3606_ = v___y_3679_;
v___y_3607_ = v___y_3681_;
v___y_3608_ = v___y_3682_;
v___y_3609_ = v___x_3707_;
v___y_3610_ = v___y_3684_;
v___y_3611_ = v___y_3683_;
v___y_3612_ = v___y_3686_;
v___y_3613_ = v___y_3687_;
v___y_3614_ = v___x_3710_;
goto v___jp_3605_;
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3715_; 
lean_inc_ref(v___x_3707_);
v___x_3711_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3680_, v___x_3707_);
lean_inc_ref(v___y_3682_);
v___x_3712_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3680_, v___y_3682_);
v___x_3713_ = lean_string_utf8_byte_size(v___x_3711_);
lean_inc(v___y_3687_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 2, v___x_3713_);
lean_ctor_set(v___x_3705_, 1, v___y_3687_);
lean_ctor_set(v___x_3705_, 0, v___x_3711_);
v___x_3715_ = v___x_3705_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3711_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v___y_3687_);
lean_ctor_set(v_reuseFailAlloc_3717_, 2, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
uint8_t v___x_3716_; 
v___x_3716_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3712_, v___x_3715_);
lean_dec_ref(v___x_3715_);
v___y_3606_ = v___y_3679_;
v___y_3607_ = v___y_3681_;
v___y_3608_ = v___y_3682_;
v___y_3609_ = v___x_3707_;
v___y_3610_ = v___y_3684_;
v___y_3611_ = v___y_3683_;
v___y_3612_ = v___y_3686_;
v___y_3613_ = v___y_3687_;
v___y_3614_ = v___x_3716_;
goto v___jp_3605_;
}
}
}
}
v___jp_3719_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v_str_3730_; lean_object* v_startInclusive_3731_; lean_object* v_endExclusive_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3726_ = lean_unsigned_to_nat(0u);
v___x_3727_ = lean_string_utf8_byte_size(v___y_3725_);
v___x_3728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3728_, 0, v___y_3725_);
lean_ctor_set(v___x_3728_, 1, v___x_3726_);
lean_ctor_set(v___x_3728_, 2, v___x_3727_);
v___x_3729_ = l_String_Slice_trimAscii(v___x_3728_);
v_str_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc_ref(v_str_3730_);
v_startInclusive_3731_ = lean_ctor_get(v___x_3729_, 1);
lean_inc(v_startInclusive_3731_);
v_endExclusive_3732_ = lean_ctor_get(v___x_3729_, 2);
lean_inc(v_endExclusive_3732_);
lean_dec_ref(v___x_3729_);
v___x_3733_ = lean_string_utf8_extract_fast(v_str_3730_, v_startInclusive_3731_, v_endExclusive_3732_);
lean_dec(v_endExclusive_3732_);
lean_dec(v_startInclusive_3731_);
lean_dec_ref(v_str_3730_);
v___x_3734_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3733_);
v___x_3735_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3724_, v___y_3721_, v___y_3720_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v_filterFn_3737_; uint8_t v_whitespace_3738_; uint8_t v_ordering_3739_; uint8_t v_reportPositions_3740_; uint8_t v_substring_3741_; lean_object* v___x_3742_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
v_filterFn_3737_ = lean_ctor_get(v_a_3736_, 0);
lean_inc_ref(v_filterFn_3737_);
v_whitespace_3738_ = lean_ctor_get_uint8(v_a_3736_, sizeof(void*)*1);
v_ordering_3739_ = lean_ctor_get_uint8(v_a_3736_, sizeof(void*)*1 + 1);
v_reportPositions_3740_ = lean_ctor_get_uint8(v_a_3736_, sizeof(void*)*1 + 2);
v_substring_3741_ = lean_ctor_get_uint8(v_a_3736_, sizeof(void*)*1 + 3);
lean_dec(v_a_3736_);
v___x_3742_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3723_, v___y_3721_, v___y_3720_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v_a_3747_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___x_3744_ = l_Lean_MessageLog_toList(v_a_3743_);
v___x_3745_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5);
v___x_3746_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3737_, v___x_3744_, v___x_3745_);
lean_dec(v___x_3744_);
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref(v___x_3746_);
if (v_reportPositions_3740_ == 0)
{
lean_object* v_fst_3748_; lean_object* v_snd_3749_; lean_object* v___x_3750_; 
v_fst_3748_ = lean_ctor_get(v_a_3747_, 0);
lean_inc(v_fst_3748_);
v_snd_3749_ = lean_ctor_get(v_a_3747_, 1);
lean_inc(v_snd_3749_);
lean_dec(v_a_3747_);
v___x_3750_ = lean_box(0);
v___y_3679_ = v___y_3720_;
v___y_3680_ = v_whitespace_3738_;
v___y_3681_ = v_snd_3749_;
v___y_3682_ = v___x_3734_;
v___y_3683_ = v_a_3743_;
v___y_3684_ = v___y_3721_;
v___y_3685_ = v_fst_3748_;
v___y_3686_ = v___y_3722_;
v___y_3687_ = v___x_3726_;
v___y_3688_ = v_substring_3741_;
v___y_3689_ = v_ordering_3739_;
v___y_3690_ = v___x_3750_;
goto v___jp_3678_;
}
else
{
lean_object* v_fst_3751_; lean_object* v_snd_3752_; uint8_t v___x_3753_; lean_object* v___x_3754_; 
v_fst_3751_ = lean_ctor_get(v_a_3747_, 0);
lean_inc(v_fst_3751_);
v_snd_3752_ = lean_ctor_get(v_a_3747_, 1);
lean_inc(v_snd_3752_);
lean_dec(v_a_3747_);
v___x_3753_ = 0;
v___x_3754_ = l_Lean_Syntax_getPos_x3f(v___y_3722_, v___x_3753_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_box(0);
v___y_3679_ = v___y_3720_;
v___y_3680_ = v_whitespace_3738_;
v___y_3681_ = v_snd_3752_;
v___y_3682_ = v___x_3734_;
v___y_3683_ = v_a_3743_;
v___y_3684_ = v___y_3721_;
v___y_3685_ = v_fst_3751_;
v___y_3686_ = v___y_3722_;
v___y_3687_ = v___x_3726_;
v___y_3688_ = v_substring_3741_;
v___y_3689_ = v_ordering_3739_;
v___y_3690_ = v___x_3755_;
goto v___jp_3678_;
}
else
{
lean_object* v_val_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3766_; 
v_val_3756_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3758_ = v___x_3754_;
v_isShared_3759_ = v_isSharedCheck_3766_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_val_3756_);
lean_dec(v___x_3754_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3766_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v_fileMap_3760_; lean_object* v___x_3761_; lean_object* v_line_3762_; lean_object* v___x_3764_; 
v_fileMap_3760_ = lean_ctor_get(v___y_3721_, 1);
lean_inc_ref(v_fileMap_3760_);
v___x_3761_ = l_Lean_FileMap_toPosition(v_fileMap_3760_, v_val_3756_);
lean_dec(v_val_3756_);
v_line_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_line_3762_);
lean_dec_ref(v___x_3761_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v_line_3762_);
v___x_3764_ = v___x_3758_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_line_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
v___y_3679_ = v___y_3720_;
v___y_3680_ = v_whitespace_3738_;
v___y_3681_ = v_snd_3752_;
v___y_3682_ = v___x_3734_;
v___y_3683_ = v_a_3743_;
v___y_3684_ = v___y_3721_;
v___y_3685_ = v_fst_3751_;
v___y_3686_ = v___y_3722_;
v___y_3687_ = v___x_3726_;
v___y_3688_ = v_substring_3741_;
v___y_3689_ = v_ordering_3739_;
v___y_3690_ = v___x_3764_;
goto v___jp_3678_;
}
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec_ref(v_filterFn_3737_);
lean_dec_ref(v___x_3734_);
lean_dec(v___y_3722_);
v_a_3767_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3742_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3742_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec_ref(v___x_3734_);
lean_dec(v___y_3723_);
lean_dec(v___y_3722_);
v_a_3775_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3735_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3735_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
v___jp_3783_:
{
if (lean_obj_tag(v___y_3786_) == 0)
{
lean_object* v___x_3790_; 
v___x_3790_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_3720_ = v___y_3784_;
v___y_3721_ = v___y_3785_;
v___y_3722_ = v___y_3787_;
v___y_3723_ = v___y_3788_;
v___y_3724_ = v___y_3789_;
v___y_3725_ = v___x_3790_;
goto v___jp_3719_;
}
else
{
lean_object* v_val_3791_; lean_object* v___x_3792_; 
v_val_3791_ = lean_ctor_get(v___y_3786_, 0);
lean_inc(v_val_3791_);
lean_dec_ref_known(v___y_3786_, 1);
v___x_3792_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3791_, v___y_3785_, v___y_3784_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v___y_3720_ = v___y_3784_;
v___y_3721_ = v___y_3785_;
v___y_3722_ = v___y_3787_;
v___y_3723_ = v___y_3788_;
v___y_3724_ = v___y_3789_;
v___y_3725_ = v_a_3793_;
goto v___jp_3719_;
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec(v___y_3787_);
v_a_3794_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3792_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3792_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
}
v___jp_3802_:
{
lean_object* v___x_3806_; lean_object* v_tk_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3806_ = lean_unsigned_to_nat(1u);
v_tk_3807_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3806_);
v___x_3808_ = lean_unsigned_to_nat(2u);
v___x_3809_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3808_);
v___x_3810_ = lean_unsigned_to_nat(4u);
v___x_3811_ = l_Lean_Syntax_getArg(v_x_3566_, v___x_3810_);
lean_dec(v_x_3566_);
v___x_3812_ = l_Lean_Syntax_getOptional_x3f(v___x_3809_);
lean_dec(v___x_3809_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v___x_3813_; 
v___x_3813_ = lean_box(0);
v___y_3784_ = v___y_3805_;
v___y_3785_ = v___y_3804_;
v___y_3786_ = v_dc_x3f_3803_;
v___y_3787_ = v_tk_3807_;
v___y_3788_ = v___x_3811_;
v___y_3789_ = v___x_3813_;
goto v___jp_3783_;
}
else
{
lean_object* v_val_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
v_val_3814_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3812_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_val_3814_);
lean_dec(v___x_3812_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_val_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
v___y_3784_ = v___y_3805_;
v___y_3785_ = v___y_3804_;
v___y_3786_ = v_dc_x3f_3803_;
v___y_3787_ = v_tk_3807_;
v___y_3788_ = v___x_3811_;
v___y_3789_ = v___x_3819_;
goto v___jp_3783_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3566_ = stack[0].m_obj;
lean_object* v_a_3567_ = stack[1].m_obj;
lean_object* v_a_3568_ = stack[2].m_obj;
lean_object* v_res_3835_;
v_res_3835_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3566_, v_a_3567_, v_a_3568_);
stack->m_obj
 = v_res_3835_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3836_, v_a_3837_, v_a_3838_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
return v_res_3840_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3841_, lean_object* v_as_3842_, lean_object* v_as_x27_3843_, lean_object* v_b_3844_, lean_object* v_a_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3841_, v_as_x27_3843_, v_b_3844_);
return v___x_3849_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_filterFn_3841_ = stack[0].m_obj;
lean_object* v_as_3842_ = stack[1].m_obj;
lean_object* v_as_x27_3843_ = stack[2].m_obj;
lean_object* v_b_3844_ = stack[3].m_obj;
lean_object* v___y_3846_ = stack[5].m_obj;
lean_object* v___y_3847_ = stack[6].m_obj;
lean_object* v_res_3850_;
v_res_3850_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3841_, v_as_3842_, v_as_x27_3843_, v_b_3844_, lean_box(0), v___y_3846_, v___y_3847_);
stack->m_obj
 = v_res_3850_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3851_, lean_object* v_as_3852_, lean_object* v_as_x27_3853_, lean_object* v_b_3854_, lean_object* v_a_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3851_, v_as_3852_, v_as_x27_3853_, v_b_3854_, v_a_3855_, v___y_3856_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v_as_x27_3853_);
lean_dec(v_as_3852_);
return v_res_3859_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3860_, lean_object* v_x_3861_, lean_object* v_x_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3860_, v_x_3861_, v_x_3862_);
return v___x_3866_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3860_ = stack[0].m_obj;
lean_object* v_x_3861_ = stack[1].m_obj;
lean_object* v_x_3862_ = stack[2].m_obj;
lean_object* v___y_3863_ = stack[3].m_obj;
lean_object* v___y_3864_ = stack[4].m_obj;
lean_object* v_res_3867_;
v_res_3867_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3860_, v_x_3861_, v_x_3862_, v___y_3863_, v___y_3864_);
stack->m_obj
 = v_res_3867_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3868_, lean_object* v_x_3869_, lean_object* v_x_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3868_, v_x_3869_, v_x_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3868_);
return v_res_3874_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3875_, v___y_3877_);
return v___x_3879_;
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3875_ = stack[0].m_obj;
lean_object* v___y_3876_ = stack[1].m_obj;
lean_object* v___y_3877_ = stack[2].m_obj;
lean_object* v_res_3880_;
v_res_3880_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3875_, v___y_3876_, v___y_3877_);
stack->m_obj
 = v_res_3880_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3881_, v___y_3882_, v___y_3883_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3886_, lean_object* v___x_3887_, lean_object* v___x_3888_, lean_object* v_inst_3889_, lean_object* v_R_3890_, lean_object* v_a_3891_, lean_object* v_b_3892_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3886_, v___x_3887_, v___x_3888_, v_a_3891_, v_b_3892_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3894_, lean_object* v___x_3895_, lean_object* v___x_3896_, lean_object* v_inst_3897_, lean_object* v_R_3898_, lean_object* v_a_3899_, lean_object* v_b_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3894_, v___x_3895_, v___x_3896_, v_inst_3897_, v_R_3898_, v_a_3899_, v_b_3900_);
lean_dec_ref(v___x_3895_);
return v_res_3901_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3902_, v___y_3904_);
return v___x_3906_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3902_ = stack[0].m_obj;
lean_object* v___y_3903_ = stack[1].m_obj;
lean_object* v___y_3904_ = stack[2].m_obj;
lean_object* v_res_3907_;
v_res_3907_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3902_, v___y_3903_, v___y_3904_);
stack->m_obj
 = v_res_3907_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3908_, v___y_3909_, v___y_3910_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3913_, lean_object* v___x_3914_, lean_object* v___x_3915_, lean_object* v_inst_3916_, lean_object* v_R_3917_, lean_object* v_a_3918_, lean_object* v_b_3919_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3913_, v___x_3914_, v___x_3915_, v_a_3918_, v_b_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3921_, lean_object* v___x_3922_, lean_object* v___x_3923_, lean_object* v_inst_3924_, lean_object* v_R_3925_, lean_object* v_a_3926_, lean_object* v_b_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3921_, v___x_3922_, v___x_3923_, v_inst_3924_, v_R_3925_, v_a_3926_, v_b_3927_);
lean_dec_ref(v___x_3922_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v___x_3929_, lean_object* v_original_3930_, lean_object* v_a_3931_, lean_object* v_inst_3932_, lean_object* v_a_3933_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_3929_, v_original_3930_, v_a_3931_, v_a_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___boxed(lean_object* v___x_3935_, lean_object* v_original_3936_, lean_object* v_a_3937_, lean_object* v_inst_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3935_, v_original_3936_, v_a_3937_, v_inst_3938_, v_a_3939_);
lean_dec_ref(v_a_3937_);
lean_dec_ref(v_original_3936_);
lean_dec(v___x_3935_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v___x_3941_, lean_object* v_edited_3942_, lean_object* v_a_3943_, lean_object* v_inst_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_3941_, v_edited_3942_, v_a_3943_, v_a_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v___x_3947_, lean_object* v_edited_3948_, lean_object* v_a_3949_, lean_object* v_inst_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v___x_3947_, v_edited_3948_, v_a_3949_, v_inst_3950_, v_a_3951_);
lean_dec_ref(v_a_3949_);
lean_dec_ref(v_edited_3948_);
lean_dec(v___x_3947_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3953_, lean_object* v_original_3954_, lean_object* v_inst_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3953_, v_original_3954_, v_a_3956_);
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3958_, lean_object* v_original_3959_, lean_object* v_inst_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3958_, v_original_3959_, v_inst_3960_, v_a_3961_);
lean_dec_ref(v_original_3959_);
lean_dec(v___x_3958_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3963_, lean_object* v_edited_3964_, lean_object* v_inst_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v___x_3967_; 
v___x_3967_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3963_, v_edited_3964_, v_a_3966_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3968_, lean_object* v_edited_3969_, lean_object* v_inst_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3968_, v_edited_3969_, v_inst_3970_, v_a_3971_);
lean_dec_ref(v_edited_3969_);
lean_dec(v___x_3968_);
return v_res_3972_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3973_, lean_object* v_inst_3974_, lean_object* v_R_3975_, lean_object* v_a_3976_, uint8_t v_b_3977_, lean_object* v_c_3978_){
_start:
{
uint8_t v___x_3979_; 
v___x_3979_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3973_, v_a_3976_, v_b_3977_);
return v___x_3979_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3973_ = stack[0].m_obj;
lean_object* v_a_3976_ = stack[3].m_obj;
uint8_t v_b_3977_ = stack[4].m_num;
uint8_t v_res_3980_;
v_res_3980_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3973_, lean_box(0), lean_box(0), v_a_3976_, v_b_3977_, lean_box(0));
stack->m_num = v_res_3980_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3981_, lean_object* v_inst_3982_, lean_object* v_R_3983_, lean_object* v_a_3984_, lean_object* v_b_3985_, lean_object* v_c_3986_){
_start:
{
uint8_t v_b_boxed_3987_; uint8_t v_res_3988_; lean_object* v_r_3989_; 
v_b_boxed_3987_ = lean_unbox(v_b_3985_);
v_res_3988_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3981_, v_inst_3982_, v_R_3983_, v_a_3984_, v_b_boxed_3987_, v_c_3986_);
lean_dec_ref(v_s_3981_);
v_r_3989_ = lean_box(v_res_3988_);
return v_r_3989_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3990_, lean_object* v_ref_3991_, lean_object* v_msg_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3991_, v_msg_3992_, v___y_3993_, v___y_3994_);
return v___x_3996_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3991_ = stack[1].m_obj;
lean_object* v_msg_3992_ = stack[2].m_obj;
lean_object* v___y_3993_ = stack[3].m_obj;
lean_object* v___y_3994_ = stack[4].m_obj;
lean_object* v_res_3997_;
v_res_3997_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_box(0), v_ref_3991_, v_msg_3992_, v___y_3993_, v___y_3994_);
stack->m_obj
 = v_res_3997_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3998_, lean_object* v_ref_3999_, lean_object* v_msg_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3998_, v_ref_3999_, v_msg_4000_, v___y_4001_, v___y_4002_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v_ref_3999_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(lean_object* v_as_4005_, lean_object* v_as_x27_4006_, lean_object* v_b_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_4006_, v_b_4007_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___boxed(lean_object* v_as_4010_, lean_object* v_as_x27_4011_, lean_object* v_b_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(v_as_4010_, v_as_x27_4011_, v_b_4012_, v_a_4013_);
lean_dec(v_as_x27_4011_);
lean_dec(v_as_4010_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(lean_object* v_lsize_4015_, lean_object* v_rsize_4016_, lean_object* v_histogram_4017_, lean_object* v_index_4018_, lean_object* v_val_4019_){
_start:
{
lean_object* v___x_4020_; 
v___x_4020_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_histogram_4017_, v_index_4018_, v_val_4019_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___boxed(lean_object* v_lsize_4021_, lean_object* v_rsize_4022_, lean_object* v_histogram_4023_, lean_object* v_index_4024_, lean_object* v_val_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(v_lsize_4021_, v_rsize_4022_, v_histogram_4023_, v_index_4024_, v_val_4025_);
lean_dec(v_rsize_4022_);
lean_dec(v_lsize_4021_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(lean_object* v_upperBound_4027_, lean_object* v___x_4028_, lean_object* v_fst_4029_, lean_object* v___x_4030_, lean_object* v_inst_4031_, lean_object* v_R_4032_, lean_object* v_a_4033_, lean_object* v_b_4034_, lean_object* v_c_4035_){
_start:
{
lean_object* v___x_4036_; 
v___x_4036_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_4027_, v___x_4028_, v_fst_4029_, v___x_4030_, v_a_4033_, v_b_4034_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___boxed(lean_object* v_upperBound_4037_, lean_object* v___x_4038_, lean_object* v_fst_4039_, lean_object* v___x_4040_, lean_object* v_inst_4041_, lean_object* v_R_4042_, lean_object* v_a_4043_, lean_object* v_b_4044_, lean_object* v_c_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(v_upperBound_4037_, v___x_4038_, v_fst_4039_, v___x_4040_, v_inst_4041_, v_R_4042_, v_a_4043_, v_b_4044_, v_c_4045_);
lean_dec(v___x_4040_);
lean_dec_ref(v_fst_4039_);
lean_dec(v___x_4038_);
lean_dec(v_upperBound_4037_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(lean_object* v_lsize_4047_, lean_object* v_rsize_4048_, lean_object* v_histogram_4049_, lean_object* v_index_4050_, lean_object* v_val_4051_){
_start:
{
lean_object* v___x_4052_; 
v___x_4052_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_histogram_4049_, v_index_4050_, v_val_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___boxed(lean_object* v_lsize_4053_, lean_object* v_rsize_4054_, lean_object* v_histogram_4055_, lean_object* v_index_4056_, lean_object* v_val_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(v_lsize_4053_, v_rsize_4054_, v_histogram_4055_, v_index_4056_, v_val_4057_);
lean_dec(v_rsize_4054_);
lean_dec(v_lsize_4053_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(lean_object* v_upperBound_4059_, lean_object* v_fst_4060_, lean_object* v___x_4061_, lean_object* v_fst_4062_, lean_object* v_inst_4063_, lean_object* v_R_4064_, lean_object* v_a_4065_, lean_object* v_b_4066_, lean_object* v_c_4067_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_4059_, v_fst_4060_, v___x_4061_, v_fst_4062_, v_a_4065_, v_b_4066_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___boxed(lean_object* v_upperBound_4069_, lean_object* v_fst_4070_, lean_object* v___x_4071_, lean_object* v_fst_4072_, lean_object* v_inst_4073_, lean_object* v_R_4074_, lean_object* v_a_4075_, lean_object* v_b_4076_, lean_object* v_c_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(v_upperBound_4069_, v_fst_4070_, v___x_4071_, v_fst_4072_, v_inst_4073_, v_R_4074_, v_a_4075_, v_b_4076_, v_c_4077_);
lean_dec_ref(v_fst_4072_);
lean_dec(v___x_4071_);
lean_dec_ref(v_fst_4070_);
lean_dec(v_upperBound_4069_);
return v_res_4078_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_4079_, lean_object* v_msg_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_4080_, v___y_4081_, v___y_4082_);
return v___x_4084_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4080_ = stack[1].m_obj;
lean_object* v___y_4081_ = stack[2].m_obj;
lean_object* v___y_4082_ = stack[3].m_obj;
lean_object* v_res_4085_;
v_res_4085_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_box(0), v_msg_4080_, v___y_4081_, v___y_4082_);
stack->m_obj
 = v_res_4085_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_4086_, lean_object* v_msg_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_4086_, v_msg_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(lean_object* v_00_u03b2_4092_, lean_object* v_m_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_4093_, v_a_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___boxed(lean_object* v_00_u03b2_4096_, lean_object* v_m_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(v_00_u03b2_4096_, v_m_4097_, v_a_4098_);
lean_dec_ref(v_a_4098_);
lean_dec_ref(v_m_4097_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26(lean_object* v_00_u03b2_4100_, lean_object* v_m_4101_, lean_object* v_a_4102_, lean_object* v_b_4103_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_m_4101_, v_a_4102_, v_b_4103_);
return v___x_4104_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_4105_, lean_object* v_macroStack_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_4105_, v_macroStack_4106_, v___y_4108_);
return v___x_4110_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_4105_ = stack[0].m_obj;
lean_object* v_macroStack_4106_ = stack[1].m_obj;
lean_object* v___y_4107_ = stack[2].m_obj;
lean_object* v___y_4108_ = stack[3].m_obj;
lean_object* v_res_4111_;
v_res_4111_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4105_, v_macroStack_4106_, v___y_4107_, v___y_4108_);
stack->m_obj
 = v_res_4111_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4112_, lean_object* v_macroStack_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4112_, v_macroStack_4113_, v___y_4114_, v___y_4115_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29(lean_object* v_inst_4118_, lean_object* v_R_4119_, lean_object* v_a_4120_, lean_object* v_b_4121_){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v_a_4120_, v_b_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(lean_object* v_00_u03b2_4123_, lean_object* v_a_4124_, lean_object* v_x_4125_){
_start:
{
lean_object* v___x_4126_; 
v___x_4126_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_4124_, v_x_4125_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___boxed(lean_object* v_00_u03b2_4127_, lean_object* v_a_4128_, lean_object* v_x_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(v_00_u03b2_4127_, v_a_4128_, v_x_4129_);
lean_dec(v_x_4129_);
lean_dec_ref(v_a_4128_);
return v_res_4130_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(lean_object* v_00_u03b2_4131_, lean_object* v_a_4132_, lean_object* v_x_4133_){
_start:
{
uint8_t v___x_4134_; 
v___x_4134_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_4132_, v_x_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4132_ = stack[1].m_obj;
lean_object* v_x_4133_ = stack[2].m_obj;
uint8_t v_res_4135_;
v_res_4135_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(lean_box(0), v_a_4132_, v_x_4133_);
stack->m_num = v_res_4135_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___boxed(lean_object* v_00_u03b2_4136_, lean_object* v_a_4137_, lean_object* v_x_4138_){
_start:
{
uint8_t v_res_4139_; lean_object* v_r_4140_; 
v_res_4139_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(v_00_u03b2_4136_, v_a_4137_, v_x_4138_);
lean_dec(v_x_4138_);
lean_dec_ref(v_a_4137_);
v_r_4140_ = lean_box(v_res_4139_);
return v_r_4140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38(lean_object* v_00_u03b2_4141_, lean_object* v_data_4142_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_data_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39(lean_object* v_00_u03b2_4144_, lean_object* v_a_4145_, lean_object* v_b_4146_, lean_object* v_x_4147_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_4145_, v_b_4146_, v_x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44(lean_object* v_00_u03b2_4149_, lean_object* v_i_4150_, lean_object* v_source_4151_, lean_object* v_target_4152_){
_start:
{
lean_object* v___x_4153_; 
v___x_4153_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v_i_4150_, v_source_4151_, v_target_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4154_, lean_object* v_x_4155_, lean_object* v_x_4156_){
_start:
{
lean_object* v___x_4157_; 
v___x_4157_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_x_4155_, v_x_4156_);
return v___x_4157_;
}
}
lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4166_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4167_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
v___x_4168_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4169_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4170_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4166_, v___x_4167_, v___x_4168_, v___x_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4171_;
v_res_4171_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
stack->m_obj
 = v_res_4171_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4173_;
}
}
lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4200_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4201_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4202_ = l_Lean_addBuiltinDeclarationRanges(v___x_4200_, v___x_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4203_;
v_res_4203_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
stack->m_obj
 = v_res_4203_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4205_;
}
}
lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4206_){
_start:
{
lean_object* v_doc_4208_; lean_object* v___x_4209_; 
v_doc_4208_ = lean_ctor_get(v___y_4206_, 1);
lean_inc_ref(v_doc_4208_);
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v_doc_4208_);
return v___x_4209_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4206_ = stack[0].m_obj;
lean_object* v_res_4210_;
v_res_4210_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4206_);
stack->m_obj
 = v_res_4210_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4211_);
lean_dec_ref(v___y_4211_);
return v_res_4213_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4214_, lean_object* v_a_4215_, uint8_t v_b_4216_){
_start:
{
lean_object* v_str_4217_; lean_object* v_startInclusive_4218_; lean_object* v_endExclusive_4219_; lean_object* v___x_4220_; uint8_t v_decide_4221_; 
v_str_4217_ = lean_ctor_get(v_s_4214_, 0);
v_startInclusive_4218_ = lean_ctor_get(v_s_4214_, 1);
v_endExclusive_4219_ = lean_ctor_get(v_s_4214_, 2);
v___x_4220_ = lean_nat_sub(v_endExclusive_4219_, v_startInclusive_4218_);
v_decide_4221_ = lean_nat_dec_eq(v_a_4215_, v___x_4220_);
lean_dec(v___x_4220_);
if (v_decide_4221_ == 0)
{
lean_object* v___x_4222_; uint32_t v___x_4223_; uint32_t v___x_4224_; uint8_t v___x_4225_; 
v___x_4222_ = lean_nat_add(v_startInclusive_4218_, v_a_4215_);
lean_dec(v_a_4215_);
v___x_4223_ = lean_string_utf8_get_fast(v_str_4217_, v___x_4222_);
v___x_4224_ = 10;
v___x_4225_ = lean_uint32_dec_eq(v___x_4223_, v___x_4224_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = lean_string_utf8_next_fast(v_str_4217_, v___x_4222_);
lean_dec(v___x_4222_);
v___x_4227_ = lean_nat_sub(v___x_4226_, v_startInclusive_4218_);
v_a_4215_ = v___x_4227_;
v_b_4216_ = v___x_4225_;
goto _start;
}
else
{
lean_dec(v___x_4222_);
return v___x_4225_;
}
}
else
{
lean_dec(v_a_4215_);
return v_b_4216_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4214_ = stack[0].m_obj;
lean_object* v_a_4215_ = stack[1].m_obj;
uint8_t v_b_4216_ = stack[2].m_num;
uint8_t v_res_4229_;
v_res_4229_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4214_, v_a_4215_, v_b_4216_);
stack->m_num = v_res_4229_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4230_, lean_object* v_a_4231_, lean_object* v_b_4232_){
_start:
{
uint8_t v_b_boxed_4233_; uint8_t v_res_4234_; lean_object* v_r_4235_; 
v_b_boxed_4233_ = lean_unbox(v_b_4232_);
v_res_4234_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4230_, v_a_4231_, v_b_boxed_4233_);
lean_dec_ref(v_s_4230_);
v_r_4235_ = lean_box(v_res_4234_);
return v_r_4235_;
}
}
uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4236_){
_start:
{
lean_object* v_searcher_4237_; uint8_t v___x_4238_; uint8_t v___x_4239_; 
v_searcher_4237_ = lean_unsigned_to_nat(0u);
v___x_4238_ = 0;
v___x_4239_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4236_, v_searcher_4237_, v___x_4238_);
return v___x_4239_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4236_ = stack[0].m_obj;
uint8_t v_res_4240_;
v_res_4240_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4236_);
stack->m_num = v_res_4240_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4241_){
_start:
{
uint8_t v_res_4242_; lean_object* v_r_4243_; 
v_res_4242_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4241_);
lean_dec_ref(v_s_4241_);
v_r_4243_ = lean_box(v_res_4242_);
return v_r_4243_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4255_, lean_object* v_fst_4256_, uint8_t v___x_4257_, lean_object* v_a_4258_, lean_object* v___x_4259_, lean_object* v___x_4260_, lean_object* v___x_4261_, lean_object* v___x_4262_, lean_object* v___x_4263_, lean_object* v___x_4264_, lean_object* v___x_4265_, lean_object* v___x_4266_, lean_object* v_snd_4267_, lean_object* v___x_4268_){
_start:
{
if (lean_obj_tag(v___x_4255_) == 1)
{
lean_object* v_val_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4331_; 
v_val_4270_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4272_ = v___x_4255_;
v_isShared_4273_ = v_isSharedCheck_4331_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_val_4270_);
lean_dec(v___x_4255_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4331_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4274_ = lean_unsigned_to_nat(0u);
v___x_4275_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4276_ = l_Lean_Syntax_setArg(v_fst_4256_, v___x_4274_, v___x_4275_);
v___x_4277_ = l_Lean_Syntax_getPos_x3f(v___x_4276_, v___x_4257_);
lean_dec(v___x_4276_);
if (lean_obj_tag(v___x_4277_) == 1)
{
lean_object* v_val_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4327_; 
lean_dec_ref(v___x_4268_);
v_val_4278_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4280_ = v___x_4277_;
v_isShared_4281_ = v_isSharedCheck_4327_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_val_4278_);
lean_dec(v___x_4277_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4327_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___y_4283_; lean_object* v___x_4309_; lean_object* v___x_4315_; uint8_t v___x_4316_; 
v___x_4309_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4267_);
v___x_4315_ = lean_string_utf8_byte_size(v___x_4309_);
v___x_4316_ = lean_nat_dec_eq(v___x_4315_, v___x_4274_);
if (v___x_4316_ == 0)
{
lean_object* v___x_4317_; lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4317_ = lean_string_length(v___x_4309_);
v___x_4318_ = lean_unsigned_to_nat(93u);
v___x_4319_ = lean_nat_dec_le(v___x_4317_, v___x_4318_);
if (v___x_4319_ == 0)
{
goto v___jp_4310_;
}
else
{
lean_object* v___x_4320_; uint8_t v___x_4321_; 
lean_inc_ref(v___x_4309_);
v___x_4320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4309_);
lean_ctor_set(v___x_4320_, 1, v___x_4274_);
lean_ctor_set(v___x_4320_, 2, v___x_4315_);
v___x_4321_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4320_);
lean_dec_ref_known(v___x_4320_, 3);
if (v___x_4321_ == 0)
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4322_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4323_ = lean_string_append(v___x_4322_, v___x_4309_);
lean_dec_ref(v___x_4309_);
v___x_4324_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4325_ = lean_string_append(v___x_4323_, v___x_4324_);
v___y_4283_ = v___x_4325_;
goto v___jp_4282_;
}
else
{
goto v___jp_4310_;
}
}
}
else
{
lean_object* v___x_4326_; 
lean_dec_ref(v___x_4309_);
v___x_4326_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_4283_ = v___x_4326_;
goto v___jp_4282_;
}
v___jp_4282_:
{
lean_object* v_toEditableDocumentCore_4284_; lean_object* v_meta_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4305_; 
v_toEditableDocumentCore_4284_ = lean_ctor_get(v_a_4258_, 0);
lean_inc_ref(v_toEditableDocumentCore_4284_);
v_meta_4285_ = lean_ctor_get(v_toEditableDocumentCore_4284_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v_toEditableDocumentCore_4284_);
if (v_isSharedCheck_4305_ == 0)
{
lean_object* v_unused_4306_; lean_object* v_unused_4307_; lean_object* v_unused_4308_; 
v_unused_4306_ = lean_ctor_get(v_toEditableDocumentCore_4284_, 3);
lean_dec(v_unused_4306_);
v_unused_4307_ = lean_ctor_get(v_toEditableDocumentCore_4284_, 2);
lean_dec(v_unused_4307_);
v_unused_4308_ = lean_ctor_get(v_toEditableDocumentCore_4284_, 1);
lean_dec(v_unused_4308_);
v___x_4287_ = v_toEditableDocumentCore_4284_;
v_isShared_4288_ = v_isSharedCheck_4305_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_meta_4285_);
lean_dec(v_toEditableDocumentCore_4284_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4305_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v_text_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4295_; 
v_text_4289_ = lean_ctor_get(v_meta_4285_, 3);
lean_inc_ref(v_text_4289_);
lean_dec_ref(v_meta_4285_);
v___x_4290_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4258_);
v___x_4291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4291_, 0, v_val_4270_);
lean_ctor_set(v___x_4291_, 1, v_val_4278_);
v___x_4292_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4289_, v___x_4291_);
v___x_4293_ = lean_box(0);
lean_inc(v___x_4259_);
if (v_isShared_4288_ == 0)
{
lean_ctor_set(v___x_4287_, 3, v___x_4259_);
lean_ctor_set(v___x_4287_, 2, v___x_4293_);
lean_ctor_set(v___x_4287_, 1, v___y_4283_);
lean_ctor_set(v___x_4287_, 0, v___x_4292_);
v___x_4295_ = v___x_4287_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v___x_4292_);
lean_ctor_set(v_reuseFailAlloc_4304_, 1, v___y_4283_);
lean_ctor_set(v_reuseFailAlloc_4304_, 2, v___x_4293_);
lean_ctor_set(v_reuseFailAlloc_4304_, 3, v___x_4259_);
v___x_4295_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
lean_object* v___x_4296_; lean_object* v___x_4298_; 
v___x_4296_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4290_, v___x_4295_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 0, v___x_4296_);
v___x_4298_ = v___x_4280_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v___x_4296_);
v___x_4298_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
lean_object* v___x_4299_; lean_object* v___x_4301_; 
lean_inc(v___x_4259_);
v___x_4299_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4259_);
lean_ctor_set(v___x_4299_, 1, v___x_4259_);
lean_ctor_set(v___x_4299_, 2, v___x_4260_);
lean_ctor_set(v___x_4299_, 3, v___x_4261_);
lean_ctor_set(v___x_4299_, 4, v___x_4262_);
lean_ctor_set(v___x_4299_, 5, v___x_4263_);
lean_ctor_set(v___x_4299_, 6, v___x_4264_);
lean_ctor_set(v___x_4299_, 7, v___x_4298_);
lean_ctor_set(v___x_4299_, 8, v___x_4265_);
lean_ctor_set(v___x_4299_, 9, v___x_4266_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set_tag(v___x_4272_, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4299_);
v___x_4301_ = v___x_4272_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
return v___x_4301_;
}
}
}
}
}
v___jp_4310_:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4311_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4312_ = lean_string_append(v___x_4311_, v___x_4309_);
lean_dec_ref(v___x_4309_);
v___x_4313_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4314_ = lean_string_append(v___x_4312_, v___x_4313_);
v___y_4283_ = v___x_4314_;
goto v___jp_4282_;
}
}
}
else
{
lean_object* v___x_4329_; 
lean_dec(v___x_4277_);
lean_dec(v_val_4270_);
lean_dec_ref(v_snd_4267_);
lean_dec(v___x_4266_);
lean_dec(v___x_4265_);
lean_dec(v___x_4264_);
lean_dec(v___x_4263_);
lean_dec(v___x_4262_);
lean_dec(v___x_4261_);
lean_dec_ref(v___x_4260_);
lean_dec(v___x_4259_);
lean_dec_ref(v_a_4258_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set_tag(v___x_4272_, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4268_);
v___x_4329_ = v___x_4272_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4268_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
else
{
lean_object* v___x_4332_; 
lean_dec_ref(v_snd_4267_);
lean_dec(v___x_4266_);
lean_dec(v___x_4265_);
lean_dec(v___x_4264_);
lean_dec(v___x_4263_);
lean_dec(v___x_4262_);
lean_dec(v___x_4261_);
lean_dec_ref(v___x_4260_);
lean_dec(v___x_4259_);
lean_dec_ref(v_a_4258_);
lean_dec(v_fst_4256_);
lean_dec(v___x_4255_);
v___x_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4268_);
return v___x_4332_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4255_ = stack[0].m_obj;
lean_object* v_fst_4256_ = stack[1].m_obj;
uint8_t v___x_4257_ = stack[2].m_num;
lean_object* v_a_4258_ = stack[3].m_obj;
lean_object* v___x_4259_ = stack[4].m_obj;
lean_object* v___x_4260_ = stack[5].m_obj;
lean_object* v___x_4261_ = stack[6].m_obj;
lean_object* v___x_4262_ = stack[7].m_obj;
lean_object* v___x_4263_ = stack[8].m_obj;
lean_object* v___x_4264_ = stack[9].m_obj;
lean_object* v___x_4265_ = stack[10].m_obj;
lean_object* v___x_4266_ = stack[11].m_obj;
lean_object* v_snd_4267_ = stack[12].m_obj;
lean_object* v___x_4268_ = stack[13].m_obj;
lean_object* v_res_4333_;
v_res_4333_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4255_, v_fst_4256_, v___x_4257_, v_a_4258_, v___x_4259_, v___x_4260_, v___x_4261_, v___x_4262_, v___x_4263_, v___x_4264_, v___x_4265_, v___x_4266_, v_snd_4267_, v___x_4268_);
stack->m_obj
 = v_res_4333_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4334_, lean_object* v_fst_4335_, lean_object* v___x_4336_, lean_object* v_a_4337_, lean_object* v___x_4338_, lean_object* v___x_4339_, lean_object* v___x_4340_, lean_object* v___x_4341_, lean_object* v___x_4342_, lean_object* v___x_4343_, lean_object* v___x_4344_, lean_object* v___x_4345_, lean_object* v_snd_4346_, lean_object* v___x_4347_, lean_object* v___y_4348_){
_start:
{
uint8_t v___x_4498__boxed_4349_; lean_object* v_res_4350_; 
v___x_4498__boxed_4349_ = lean_unbox(v___x_4336_);
v_res_4350_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4334_, v_fst_4335_, v___x_4498__boxed_4349_, v_a_4337_, v___x_4338_, v___x_4339_, v___x_4340_, v___x_4341_, v___x_4342_, v___x_4343_, v___x_4344_, v___x_4345_, v_snd_4346_, v___x_4347_);
return v_res_4350_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4354_, size_t v_sz_4355_, size_t v_i_4356_, lean_object* v_b_4357_){
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
size_t v___x_4360_; size_t v___x_4361_; 
v___x_4360_ = ((size_t)1ULL);
v___x_4361_ = lean_usize_add(v_i_4356_, v___x_4360_);
v_i_4356_ = v___x_4361_;
v_b_4357_ = v_a_4359_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4354_ = stack[0].m_obj;
size_t v_sz_4355_ = stack[1].m_num;
size_t v_i_4356_ = stack[2].m_num;
lean_object* v_b_4357_ = stack[3].m_obj;
lean_object* v_res_4403_;
v_res_4403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4354_, v_sz_4355_, v_i_4356_, v_b_4357_);
stack->m_obj
 = v_res_4403_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4404_, lean_object* v_sz_4405_, lean_object* v_i_4406_, lean_object* v_b_4407_){
_start:
{
size_t v_sz_boxed_4408_; size_t v_i_boxed_4409_; lean_object* v_res_4410_; 
v_sz_boxed_4408_ = lean_unbox_usize(v_sz_4405_);
lean_dec(v_sz_4405_);
v_i_boxed_4409_ = lean_unbox_usize(v_i_4406_);
lean_dec(v_i_4406_);
v_res_4410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4404_, v_sz_boxed_4408_, v_i_boxed_4409_, v_b_4407_);
lean_dec_ref(v_b_4407_);
lean_dec_ref(v_as_4404_);
return v_res_4410_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4411_, size_t v_sz_4412_, size_t v_i_4413_, lean_object* v_b_4414_){
_start:
{
lean_object* v_a_4416_; uint8_t v___x_4420_; 
v___x_4420_ = lean_usize_dec_lt(v_i_4413_, v_sz_4412_);
if (v___x_4420_ == 0)
{
lean_inc_ref(v_b_4414_);
return v_b_4414_;
}
else
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v_a_4423_; 
v___x_4421_ = lean_box(0);
v___x_4422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4423_ = lean_array_uget(v_as_4411_, v_i_4413_);
if (lean_obj_tag(v_a_4423_) == 1)
{
lean_object* v_i_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4458_; 
v_i_4424_ = lean_ctor_get(v_a_4423_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v_a_4423_);
if (v_isSharedCheck_4458_ == 0)
{
lean_object* v_unused_4459_; 
v_unused_4459_ = lean_ctor_get(v_a_4423_, 1);
lean_dec(v_unused_4459_);
v___x_4426_ = v_a_4423_;
v_isShared_4427_ = v_isSharedCheck_4458_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_i_4424_);
lean_dec(v_a_4423_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4458_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
if (lean_obj_tag(v_i_4424_) == 10)
{
lean_object* v_i_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4457_; 
v_i_4428_ = lean_ctor_get(v_i_4424_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v_i_4424_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4430_ = v_i_4424_;
v_isShared_4431_ = v_isSharedCheck_4457_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_i_4428_);
lean_dec(v_i_4424_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4457_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v_stx_4432_; lean_object* v_value_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4456_; 
v_stx_4432_ = lean_ctor_get(v_i_4428_, 0);
v_value_4433_ = lean_ctor_get(v_i_4428_, 1);
v_isSharedCheck_4456_ = !lean_is_exclusive(v_i_4428_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4435_ = v_i_4428_;
v_isShared_4436_ = v_isSharedCheck_4456_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_value_4433_);
lean_inc(v_stx_4432_);
lean_dec(v_i_4428_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4456_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4437_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4438_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4433_, v___x_4437_);
lean_dec(v_value_4433_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_del_object(v___x_4435_);
lean_dec(v_stx_4432_);
lean_del_object(v___x_4430_);
lean_del_object(v___x_4426_);
v_a_4416_ = v___x_4422_;
goto v___jp_4415_;
}
else
{
lean_object* v_val_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4455_; 
v_val_4439_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4441_ = v___x_4438_;
v_isShared_4442_ = v_isSharedCheck_4455_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_val_4439_);
lean_dec(v___x_4438_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4455_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 1, v_val_4439_);
v___x_4444_ = v___x_4435_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_stx_4432_);
lean_ctor_set(v_reuseFailAlloc_4454_, 1, v_val_4439_);
v___x_4444_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
lean_object* v___x_4446_; 
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 0, v___x_4444_);
v___x_4446_ = v___x_4441_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4444_);
v___x_4446_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
lean_object* v___x_4448_; 
if (v_isShared_4431_ == 0)
{
lean_ctor_set_tag(v___x_4430_, 1);
lean_ctor_set(v___x_4430_, 0, v___x_4446_);
v___x_4448_ = v___x_4430_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
lean_object* v___x_4450_; 
if (v_isShared_4427_ == 0)
{
lean_ctor_set_tag(v___x_4426_, 0);
lean_ctor_set(v___x_4426_, 1, v___x_4421_);
lean_ctor_set(v___x_4426_, 0, v___x_4448_);
v___x_4450_ = v___x_4426_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4448_);
lean_ctor_set(v_reuseFailAlloc_4451_, 1, v___x_4421_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
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
lean_del_object(v___x_4426_);
lean_dec_ref(v_i_4424_);
v_a_4416_ = v___x_4422_;
goto v___jp_4415_;
}
}
}
else
{
lean_dec(v_a_4423_);
v_a_4416_ = v___x_4422_;
goto v___jp_4415_;
}
}
v___jp_4415_:
{
size_t v___x_4417_; size_t v___x_4418_; lean_object* v___x_4419_; 
v___x_4417_ = ((size_t)1ULL);
v___x_4418_ = lean_usize_add(v_i_4413_, v___x_4417_);
v___x_4419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4411_, v_sz_4412_, v___x_4418_, v_a_4416_);
return v___x_4419_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4411_ = stack[0].m_obj;
size_t v_sz_4412_ = stack[1].m_num;
size_t v_i_4413_ = stack[2].m_num;
lean_object* v_b_4414_ = stack[3].m_obj;
lean_object* v_res_4460_;
v_res_4460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4411_, v_sz_4412_, v_i_4413_, v_b_4414_);
stack->m_obj
 = v_res_4460_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4461_, lean_object* v_sz_4462_, lean_object* v_i_4463_, lean_object* v_b_4464_){
_start:
{
size_t v_sz_boxed_4465_; size_t v_i_boxed_4466_; lean_object* v_res_4467_; 
v_sz_boxed_4465_ = lean_unbox_usize(v_sz_4462_);
lean_dec(v_sz_4462_);
v_i_boxed_4466_ = lean_unbox_usize(v_i_4463_);
lean_dec(v_i_4463_);
v_res_4467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4461_, v_sz_boxed_4465_, v_i_boxed_4466_, v_b_4464_);
lean_dec_ref(v_b_4464_);
lean_dec_ref(v_as_4461_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4468_){
_start:
{
if (lean_obj_tag(v_x_4468_) == 0)
{
lean_object* v_cs_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; size_t v_sz_4472_; size_t v___x_4473_; lean_object* v___x_4474_; lean_object* v_fst_4475_; 
v_cs_4469_ = lean_ctor_get(v_x_4468_, 0);
v___x_4470_ = lean_box(0);
v___x_4471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4472_ = lean_array_size(v_cs_4469_);
v___x_4473_ = ((size_t)0ULL);
v___x_4474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4469_, v_sz_4472_, v___x_4473_, v___x_4471_);
v_fst_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_fst_4475_);
lean_dec_ref(v___x_4474_);
if (lean_obj_tag(v_fst_4475_) == 0)
{
return v___x_4470_;
}
else
{
lean_object* v_val_4476_; 
v_val_4476_ = lean_ctor_get(v_fst_4475_, 0);
lean_inc(v_val_4476_);
lean_dec_ref_known(v_fst_4475_, 1);
return v_val_4476_;
}
}
else
{
lean_object* v_vs_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; size_t v_sz_4480_; size_t v___x_4481_; lean_object* v___x_4482_; lean_object* v_fst_4483_; 
v_vs_4477_ = lean_ctor_get(v_x_4468_, 0);
v___x_4478_ = lean_box(0);
v___x_4479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4480_ = lean_array_size(v_vs_4477_);
v___x_4481_ = ((size_t)0ULL);
v___x_4482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4477_, v_sz_4480_, v___x_4481_, v___x_4479_);
v_fst_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_fst_4483_);
lean_dec_ref(v___x_4482_);
if (lean_obj_tag(v_fst_4483_) == 0)
{
return v___x_4478_;
}
else
{
lean_object* v_val_4484_; 
v_val_4484_ = lean_ctor_get(v_fst_4483_, 0);
lean_inc(v_val_4484_);
lean_dec_ref_known(v_fst_4483_, 1);
return v_val_4484_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4485_, size_t v_sz_4486_, size_t v_i_4487_, lean_object* v_b_4488_){
_start:
{
uint8_t v___x_4489_; 
v___x_4489_ = lean_usize_dec_lt(v_i_4487_, v_sz_4486_);
if (v___x_4489_ == 0)
{
lean_inc_ref(v_b_4488_);
return v_b_4488_;
}
else
{
lean_object* v___x_4490_; lean_object* v_a_4491_; lean_object* v___x_4492_; 
v___x_4490_ = lean_box(0);
v_a_4491_ = lean_array_uget_borrowed(v_as_4485_, v_i_4487_);
v___x_4492_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4491_);
if (lean_obj_tag(v___x_4492_) == 1)
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
v___x_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
lean_ctor_set(v___x_4494_, 1, v___x_4490_);
return v___x_4494_;
}
else
{
lean_object* v___x_4495_; size_t v___x_4496_; size_t v___x_4497_; 
lean_dec(v___x_4492_);
v___x_4495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4496_ = ((size_t)1ULL);
v___x_4497_ = lean_usize_add(v_i_4487_, v___x_4496_);
v_i_4487_ = v___x_4497_;
v_b_4488_ = v___x_4495_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4485_ = stack[0].m_obj;
size_t v_sz_4486_ = stack[1].m_num;
size_t v_i_4487_ = stack[2].m_num;
lean_object* v_b_4488_ = stack[3].m_obj;
lean_object* v_res_4499_;
v_res_4499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4485_, v_sz_4486_, v_i_4487_, v_b_4488_);
stack->m_obj
 = v_res_4499_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4500_, lean_object* v_sz_4501_, lean_object* v_i_4502_, lean_object* v_b_4503_){
_start:
{
size_t v_sz_boxed_4504_; size_t v_i_boxed_4505_; lean_object* v_res_4506_; 
v_sz_boxed_4504_ = lean_unbox_usize(v_sz_4501_);
lean_dec(v_sz_4501_);
v_i_boxed_4505_ = lean_unbox_usize(v_i_4502_);
lean_dec(v_i_4502_);
v_res_4506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4500_, v_sz_boxed_4504_, v_i_boxed_4505_, v_b_4503_);
lean_dec_ref(v_b_4503_);
lean_dec_ref(v_as_4500_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4507_);
lean_dec_ref(v_x_4507_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4509_){
_start:
{
lean_object* v_root_4510_; lean_object* v_tail_4511_; lean_object* v___x_4512_; 
v_root_4510_ = lean_ctor_get(v_t_4509_, 0);
v_tail_4511_ = lean_ctor_get(v_t_4509_, 1);
v___x_4512_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4510_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v___x_4513_; size_t v_sz_4514_; size_t v___x_4515_; lean_object* v___x_4516_; lean_object* v_fst_4517_; 
v___x_4513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4514_ = lean_array_size(v_tail_4511_);
v___x_4515_ = ((size_t)0ULL);
v___x_4516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4511_, v_sz_4514_, v___x_4515_, v___x_4513_);
v_fst_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc(v_fst_4517_);
lean_dec_ref(v___x_4516_);
if (lean_obj_tag(v_fst_4517_) == 0)
{
return v___x_4512_;
}
else
{
lean_object* v_val_4518_; 
v_val_4518_ = lean_ctor_get(v_fst_4517_, 0);
lean_inc(v_val_4518_);
lean_dec_ref_known(v_fst_4517_, 1);
return v_val_4518_;
}
}
else
{
return v___x_4512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4519_);
lean_dec_ref(v_t_4519_);
return v_res_4520_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4535_, lean_object* v_a_4536_){
_start:
{
if (lean_obj_tag(v_node_4535_) == 1)
{
lean_object* v_children_4538_; lean_object* v_res_4539_; 
v_children_4538_ = lean_ctor_get(v_node_4535_, 1);
v_res_4539_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4538_);
if (lean_obj_tag(v_res_4539_) == 1)
{
lean_object* v_val_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4577_; 
v_val_4540_ = lean_ctor_get(v_res_4539_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_res_4539_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4542_ = v_res_4539_;
v_isShared_4543_ = v_isSharedCheck_4577_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_val_4540_);
lean_dec(v_res_4539_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4577_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v_fst_4544_; lean_object* v_snd_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4576_; 
v_fst_4544_ = lean_ctor_get(v_val_4540_, 0);
v_snd_4545_ = lean_ctor_get(v_val_4540_, 1);
v_isSharedCheck_4576_ = !lean_is_exclusive(v_val_4540_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4547_ = v_val_4540_;
v_isShared_4548_ = v_isSharedCheck_4576_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_snd_4545_);
lean_inc(v_fst_4544_);
lean_dec(v_val_4540_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4576_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4549_; lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4575_; 
v___x_4549_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4536_);
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4552_ = v___x_4549_;
v_isShared_4553_ = v_isSharedCheck_4575_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4549_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4575_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; uint8_t v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___y_4562_; lean_object* v___x_4564_; 
v___x_4554_ = lean_box(0);
v___x_4555_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4556_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4557_ = 1;
v___x_4558_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4559_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4560_ = l_Lean_Syntax_getPos_x3f(v_fst_4544_, v___x_4557_);
v___x_4561_ = lean_box(v___x_4557_);
v___y_4562_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4562_, 0, v___x_4560_);
lean_closure_set(v___y_4562_, 1, v_fst_4544_);
lean_closure_set(v___y_4562_, 2, v___x_4561_);
lean_closure_set(v___y_4562_, 3, v_a_4550_);
lean_closure_set(v___y_4562_, 4, v___x_4554_);
lean_closure_set(v___y_4562_, 5, v___x_4555_);
lean_closure_set(v___y_4562_, 6, v___x_4556_);
lean_closure_set(v___y_4562_, 7, v___x_4554_);
lean_closure_set(v___y_4562_, 8, v___x_4558_);
lean_closure_set(v___y_4562_, 9, v___x_4554_);
lean_closure_set(v___y_4562_, 10, v___x_4554_);
lean_closure_set(v___y_4562_, 11, v___x_4554_);
lean_closure_set(v___y_4562_, 12, v_snd_4545_);
lean_closure_set(v___y_4562_, 13, v___x_4559_);
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 0, v___y_4562_);
v___x_4564_ = v___x_4542_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___y_4562_);
v___x_4564_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
lean_object* v___x_4566_; 
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 1, v___x_4564_);
lean_ctor_set(v___x_4547_, 0, v___x_4559_);
v___x_4566_ = v___x_4547_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4559_);
lean_ctor_set(v_reuseFailAlloc_4573_, 1, v___x_4564_);
v___x_4566_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4571_; 
v___x_4567_ = lean_unsigned_to_nat(1u);
v___x_4568_ = lean_mk_empty_array_with_capacity(v___x_4567_);
v___x_4569_ = lean_array_push(v___x_4568_, v___x_4566_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4569_);
v___x_4571_ = v___x_4552_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4569_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4578_; lean_object* v___x_4579_; 
lean_dec(v_res_4539_);
v___x_4578_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
return v___x_4579_;
}
}
else
{
lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4580_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4580_);
return v___x_4581_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_node_4535_ = stack[0].m_obj;
lean_object* v_a_4536_ = stack[1].m_obj;
lean_object* v_res_4582_;
v_res_4582_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4535_, v_a_4536_);
stack->m_obj
 = v_res_4582_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4583_, v_a_4584_);
lean_dec_ref(v_a_4584_);
lean_dec_ref(v_node_4583_);
return v_res_4586_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4587_, lean_object* v_x_4588_, lean_object* v_x_4589_, lean_object* v_node_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v___x_4593_; 
v___x_4593_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4590_, v_a_4591_);
return v___x_4593_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4587_ = stack[0].m_obj;
lean_object* v_x_4588_ = stack[1].m_obj;
lean_object* v_x_4589_ = stack[2].m_obj;
lean_object* v_node_4590_ = stack[3].m_obj;
lean_object* v_a_4591_ = stack[4].m_obj;
lean_object* v_res_4594_;
v_res_4594_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4587_, v_x_4588_, v_x_4589_, v_node_4590_, v_a_4591_);
stack->m_obj
 = v_res_4594_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4595_, lean_object* v_x_4596_, lean_object* v_x_4597_, lean_object* v_node_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4595_, v_x_4596_, v_x_4597_, v_node_4598_, v_a_4599_);
lean_dec_ref(v_a_4599_);
lean_dec_ref(v_node_4598_);
lean_dec_ref(v_x_4597_);
lean_dec_ref(v_x_4596_);
lean_dec_ref(v_x_4595_);
return v_res_4601_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4602_, lean_object* v_inst_4603_, lean_object* v_R_4604_, lean_object* v_a_4605_, uint8_t v_b_4606_, lean_object* v_c_4607_){
_start:
{
uint8_t v___x_4608_; 
v___x_4608_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4602_, v_a_4605_, v_b_4606_);
return v___x_4608_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4602_ = stack[0].m_obj;
lean_object* v_a_4605_ = stack[3].m_obj;
uint8_t v_b_4606_ = stack[4].m_num;
uint8_t v_res_4609_;
v_res_4609_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4602_, lean_box(0), lean_box(0), v_a_4605_, v_b_4606_, lean_box(0));
stack->m_num = v_res_4609_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4610_, lean_object* v_inst_4611_, lean_object* v_R_4612_, lean_object* v_a_4613_, lean_object* v_b_4614_, lean_object* v_c_4615_){
_start:
{
uint8_t v_b_boxed_4616_; uint8_t v_res_4617_; lean_object* v_r_4618_; 
v_b_boxed_4616_ = lean_unbox(v_b_4614_);
v_res_4617_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4610_, v_inst_4611_, v_R_4612_, v_a_4613_, v_b_boxed_4616_, v_c_4615_);
lean_dec_ref(v_s_4610_);
v_r_4618_ = lean_box(v_res_4617_);
return v_r_4618_;
}
}
lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_(){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4624_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_));
v___x_4625_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4626_ = l_Lean_CodeAction_insertBuiltin(v___x_4624_, v___x_4625_);
return v___x_4626_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4627_;
v_res_4627_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_();
stack->m_obj
 = v_res_4627_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354____boxed(lean_object* v_a_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_();
return v_res_4629_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4636_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4635_);
return v___x_4636_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4637_ = lean_unsigned_to_nat(0u);
v___x_4638_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
v___x_4639_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4640_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
lean_ctor_set(v___x_4640_, 1, v___x_4638_);
lean_ctor_set(v___x_4640_, 2, v___x_4637_);
lean_ctor_set(v___x_4640_, 3, v___x_4637_);
return v___x_4640_;
}
}
uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4641_){
_start:
{
lean_object* v___x_4642_; uint8_t v___x_4643_; uint8_t v___x_4644_; 
v___x_4642_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4643_ = 0;
v___x_4644_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4641_, v___x_4642_, v___x_4643_);
return v___x_4644_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4641_ = stack[0].m_obj;
uint8_t v_res_4645_;
v_res_4645_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4641_);
stack->m_num = v_res_4645_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4646_){
_start:
{
uint8_t v_res_4647_; lean_object* v_r_4648_; 
v_res_4647_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4646_);
lean_dec_ref(v_s_4646_);
v_r_4648_ = lean_box(v_res_4647_);
return v_r_4648_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4649_, lean_object* v_as_x27_4650_, uint8_t v_b_4651_){
_start:
{
if (lean_obj_tag(v_as_x27_4650_) == 0)
{
lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4653_ = lean_box(v_b_4651_);
v___x_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4654_, 0, v___x_4653_);
return v___x_4654_;
}
else
{
lean_object* v_head_4655_; uint8_t v_isSilent_4656_; 
v_head_4655_ = lean_ctor_get(v_as_x27_4650_, 0);
v_isSilent_4656_ = lean_ctor_get_uint8(v_head_4655_, sizeof(void*)*5 + 2);
if (v_isSilent_4656_ == 0)
{
lean_object* v_tail_4657_; lean_object* v_data_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; uint8_t v___x_4663_; 
v_tail_4657_ = lean_ctor_get(v_as_x27_4650_, 1);
v_data_4658_ = lean_ctor_get(v_head_4655_, 4);
lean_inc(v_data_4658_);
v___x_4659_ = l_Lean_MessageData_toString(v_data_4658_);
v___x_4660_ = lean_unsigned_to_nat(0u);
v___x_4661_ = lean_string_utf8_byte_size(v___x_4659_);
v___x_4662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4659_);
lean_ctor_set(v___x_4662_, 1, v___x_4660_);
lean_ctor_set(v___x_4662_, 2, v___x_4661_);
v___x_4663_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4662_);
lean_dec_ref_known(v___x_4662_, 3);
if (v___x_4663_ == 0)
{
v_as_x27_4650_ = v_tail_4657_;
goto _start;
}
else
{
lean_object* v___x_4665_; lean_object* v___x_4666_; 
v___x_4665_ = lean_box(v_foundPanic_4649_);
v___x_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
return v___x_4666_;
}
}
else
{
lean_object* v_tail_4667_; 
v_tail_4667_ = lean_ctor_get(v_as_x27_4650_, 1);
v_as_x27_4650_ = v_tail_4667_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_foundPanic_4649_ = stack[0].m_num;
lean_object* v_as_x27_4650_ = stack[1].m_obj;
uint8_t v_b_4651_ = stack[2].m_num;
lean_object* v_res_4669_;
v_res_4669_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4649_, v_as_x27_4650_, v_b_4651_);
stack->m_obj
 = v_res_4669_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4670_, lean_object* v_as_x27_4671_, lean_object* v_b_4672_, lean_object* v___y_4673_){
_start:
{
uint8_t v_foundPanic_boxed_4674_; uint8_t v_b_boxed_4675_; lean_object* v_res_4676_; 
v_foundPanic_boxed_4674_ = lean_unbox(v_foundPanic_4670_);
v_b_boxed_4675_ = lean_unbox(v_b_4672_);
v_res_4676_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4674_, v_as_x27_4671_, v_b_boxed_4675_);
lean_dec(v_as_x27_4671_);
return v_res_4676_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4677_, uint8_t v_severity_4678_, uint8_t v_isSilent_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l_Lean_Elab_Command_getRef___redArg(v___y_4680_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4685_; 
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc(v_a_4684_);
lean_dec_ref_known(v___x_4683_, 1);
v___x_4685_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4684_, v_msgData_4677_, v_severity_4678_, v_isSilent_4679_, v___y_4680_, v___y_4681_);
lean_dec(v_a_4684_);
return v___x_4685_;
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
lean_dec_ref(v_msgData_4677_);
v_a_4686_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4683_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4683_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_4677_ = stack[0].m_obj;
uint8_t v_severity_4678_ = stack[1].m_num;
uint8_t v_isSilent_4679_ = stack[2].m_num;
lean_object* v___y_4680_ = stack[3].m_obj;
lean_object* v___y_4681_ = stack[4].m_obj;
lean_object* v_res_4694_;
v_res_4694_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4677_, v_severity_4678_, v_isSilent_4679_, v___y_4680_, v___y_4681_);
stack->m_obj
 = v_res_4694_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4695_, lean_object* v_severity_4696_, lean_object* v_isSilent_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
uint8_t v_severity_boxed_4701_; uint8_t v_isSilent_boxed_4702_; lean_object* v_res_4703_; 
v_severity_boxed_4701_ = lean_unbox(v_severity_4696_);
v_isSilent_boxed_4702_ = lean_unbox(v_isSilent_4697_);
v_res_4703_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4695_, v_severity_boxed_4701_, v_isSilent_boxed_4702_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
return v_res_4703_;
}
}
lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
uint8_t v___x_4708_; uint8_t v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = 2;
v___x_4709_ = 0;
v___x_4710_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4704_, v___x_4708_, v___x_4709_, v___y_4705_, v___y_4706_);
return v___x_4710_;
}
}
LEAN_EXPORT void l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_4704_ = stack[0].m_obj;
lean_object* v___y_4705_ = stack[1].m_obj;
lean_object* v___y_4706_ = stack[2].m_obj;
lean_object* v_res_4711_;
v_res_4711_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4704_, v___y_4705_, v___y_4706_);
stack->m_obj
 = v_res_4711_;
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4712_, v___y_4713_, v___y_4714_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
return v_res_4716_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4724_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4725_ = l_Lean_MessageData_ofFormat(v___x_4724_);
return v___x_4725_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_){
_start:
{
lean_object* v___x_4730_; uint8_t v_foundPanic_4731_; 
v___x_4730_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4726_);
v_foundPanic_4731_ = l_Lean_Syntax_isOfKind(v_x_4726_, v___x_4730_);
if (v_foundPanic_4731_ == 0)
{
lean_object* v___x_4732_; 
lean_dec(v_x_4726_);
v___x_4732_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4732_;
}
else
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4733_ = lean_unsigned_to_nat(2u);
v___x_4734_ = l_Lean_Syntax_getArg(v_x_4726_, v___x_4733_);
lean_dec(v_x_4726_);
v___x_4735_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4734_, v_a_4727_, v_a_4728_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; uint8_t v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4796_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4736_);
lean_dec_ref_known(v___x_4735_, 1);
v___x_4737_ = 0;
v___x_4738_ = l_Lean_MessageLog_toList(v_a_4736_);
v___x_4739_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4731_, v___x_4738_, v___x_4737_);
lean_dec(v___x_4738_);
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4742_ = v___x_4739_;
v_isShared_4743_ = v_isSharedCheck_4796_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4739_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4796_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
uint8_t v___x_4744_; 
v___x_4744_ = lean_unbox(v_a_4740_);
lean_dec(v_a_4740_);
if (v___x_4744_ == 0)
{
lean_object* v___x_4745_; lean_object* v_env_4746_; lean_object* v_scopes_4747_; lean_object* v_usedQuotCtxts_4748_; lean_object* v_nextMacroScope_4749_; lean_object* v_maxRecDepth_4750_; lean_object* v_ngen_4751_; lean_object* v_auxDeclNGen_4752_; lean_object* v_infoState_4753_; lean_object* v_traceState_4754_; lean_object* v_snapshotTasks_4755_; lean_object* v_prevLinterStates_4756_; lean_object* v_codeQualityEntryTasks_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4767_; 
lean_del_object(v___x_4742_);
v___x_4745_ = lean_st_ref_take(v_a_4728_);
v_env_4746_ = lean_ctor_get(v___x_4745_, 0);
v_scopes_4747_ = lean_ctor_get(v___x_4745_, 2);
v_usedQuotCtxts_4748_ = lean_ctor_get(v___x_4745_, 3);
v_nextMacroScope_4749_ = lean_ctor_get(v___x_4745_, 4);
v_maxRecDepth_4750_ = lean_ctor_get(v___x_4745_, 5);
v_ngen_4751_ = lean_ctor_get(v___x_4745_, 6);
v_auxDeclNGen_4752_ = lean_ctor_get(v___x_4745_, 7);
v_infoState_4753_ = lean_ctor_get(v___x_4745_, 8);
v_traceState_4754_ = lean_ctor_get(v___x_4745_, 9);
v_snapshotTasks_4755_ = lean_ctor_get(v___x_4745_, 10);
v_prevLinterStates_4756_ = lean_ctor_get(v___x_4745_, 11);
v_codeQualityEntryTasks_4757_ = lean_ctor_get(v___x_4745_, 12);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4767_ == 0)
{
lean_object* v_unused_4768_; 
v_unused_4768_ = lean_ctor_get(v___x_4745_, 1);
lean_dec(v_unused_4768_);
v___x_4759_ = v___x_4745_;
v_isShared_4760_ = v_isSharedCheck_4767_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4757_);
lean_inc(v_prevLinterStates_4756_);
lean_inc(v_snapshotTasks_4755_);
lean_inc(v_traceState_4754_);
lean_inc(v_infoState_4753_);
lean_inc(v_auxDeclNGen_4752_);
lean_inc(v_ngen_4751_);
lean_inc(v_maxRecDepth_4750_);
lean_inc(v_nextMacroScope_4749_);
lean_inc(v_usedQuotCtxts_4748_);
lean_inc(v_scopes_4747_);
lean_inc(v_env_4746_);
lean_dec(v___x_4745_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4767_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 1, v_a_4736_);
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_env_4746_);
lean_ctor_set(v_reuseFailAlloc_4766_, 1, v_a_4736_);
lean_ctor_set(v_reuseFailAlloc_4766_, 2, v_scopes_4747_);
lean_ctor_set(v_reuseFailAlloc_4766_, 3, v_usedQuotCtxts_4748_);
lean_ctor_set(v_reuseFailAlloc_4766_, 4, v_nextMacroScope_4749_);
lean_ctor_set(v_reuseFailAlloc_4766_, 5, v_maxRecDepth_4750_);
lean_ctor_set(v_reuseFailAlloc_4766_, 6, v_ngen_4751_);
lean_ctor_set(v_reuseFailAlloc_4766_, 7, v_auxDeclNGen_4752_);
lean_ctor_set(v_reuseFailAlloc_4766_, 8, v_infoState_4753_);
lean_ctor_set(v_reuseFailAlloc_4766_, 9, v_traceState_4754_);
lean_ctor_set(v_reuseFailAlloc_4766_, 10, v_snapshotTasks_4755_);
lean_ctor_set(v_reuseFailAlloc_4766_, 11, v_prevLinterStates_4756_);
lean_ctor_set(v_reuseFailAlloc_4766_, 12, v_codeQualityEntryTasks_4757_);
v___x_4762_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4763_ = lean_st_ref_put(v_a_4728_, v___x_4762_);
v___x_4764_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4765_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4764_, v_a_4727_, v_a_4728_);
return v___x_4765_;
}
}
}
else
{
lean_object* v___x_4769_; lean_object* v_env_4770_; lean_object* v_scopes_4771_; lean_object* v_usedQuotCtxts_4772_; lean_object* v_nextMacroScope_4773_; lean_object* v_maxRecDepth_4774_; lean_object* v_ngen_4775_; lean_object* v_auxDeclNGen_4776_; lean_object* v_infoState_4777_; lean_object* v_traceState_4778_; lean_object* v_snapshotTasks_4779_; lean_object* v_prevLinterStates_4780_; lean_object* v_codeQualityEntryTasks_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4794_; 
lean_dec(v_a_4736_);
v___x_4769_ = lean_st_ref_take(v_a_4728_);
v_env_4770_ = lean_ctor_get(v___x_4769_, 0);
v_scopes_4771_ = lean_ctor_get(v___x_4769_, 2);
v_usedQuotCtxts_4772_ = lean_ctor_get(v___x_4769_, 3);
v_nextMacroScope_4773_ = lean_ctor_get(v___x_4769_, 4);
v_maxRecDepth_4774_ = lean_ctor_get(v___x_4769_, 5);
v_ngen_4775_ = lean_ctor_get(v___x_4769_, 6);
v_auxDeclNGen_4776_ = lean_ctor_get(v___x_4769_, 7);
v_infoState_4777_ = lean_ctor_get(v___x_4769_, 8);
v_traceState_4778_ = lean_ctor_get(v___x_4769_, 9);
v_snapshotTasks_4779_ = lean_ctor_get(v___x_4769_, 10);
v_prevLinterStates_4780_ = lean_ctor_get(v___x_4769_, 11);
v_codeQualityEntryTasks_4781_ = lean_ctor_get(v___x_4769_, 12);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4794_ == 0)
{
lean_object* v_unused_4795_; 
v_unused_4795_ = lean_ctor_get(v___x_4769_, 1);
lean_dec(v_unused_4795_);
v___x_4783_ = v___x_4769_;
v_isShared_4784_ = v_isSharedCheck_4794_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4781_);
lean_inc(v_prevLinterStates_4780_);
lean_inc(v_snapshotTasks_4779_);
lean_inc(v_traceState_4778_);
lean_inc(v_infoState_4777_);
lean_inc(v_auxDeclNGen_4776_);
lean_inc(v_ngen_4775_);
lean_inc(v_maxRecDepth_4774_);
lean_inc(v_nextMacroScope_4773_);
lean_inc(v_usedQuotCtxts_4772_);
lean_inc(v_scopes_4771_);
lean_inc(v_env_4770_);
lean_dec(v___x_4769_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4794_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4788_; 
v___x_4785_ = lean_box(0);
v___x_4786_ = l_Lean_MessageLog_empty;
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 1, v___x_4786_);
v___x_4788_ = v___x_4783_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_env_4770_);
lean_ctor_set(v_reuseFailAlloc_4793_, 1, v___x_4786_);
lean_ctor_set(v_reuseFailAlloc_4793_, 2, v_scopes_4771_);
lean_ctor_set(v_reuseFailAlloc_4793_, 3, v_usedQuotCtxts_4772_);
lean_ctor_set(v_reuseFailAlloc_4793_, 4, v_nextMacroScope_4773_);
lean_ctor_set(v_reuseFailAlloc_4793_, 5, v_maxRecDepth_4774_);
lean_ctor_set(v_reuseFailAlloc_4793_, 6, v_ngen_4775_);
lean_ctor_set(v_reuseFailAlloc_4793_, 7, v_auxDeclNGen_4776_);
lean_ctor_set(v_reuseFailAlloc_4793_, 8, v_infoState_4777_);
lean_ctor_set(v_reuseFailAlloc_4793_, 9, v_traceState_4778_);
lean_ctor_set(v_reuseFailAlloc_4793_, 10, v_snapshotTasks_4779_);
lean_ctor_set(v_reuseFailAlloc_4793_, 11, v_prevLinterStates_4780_);
lean_ctor_set(v_reuseFailAlloc_4793_, 12, v_codeQualityEntryTasks_4781_);
v___x_4788_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
lean_object* v___x_4789_; lean_object* v___x_4791_; 
v___x_4789_ = lean_st_ref_put(v_a_4728_, v___x_4788_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v___x_4785_);
v___x_4791_ = v___x_4742_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4785_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
}
}
else
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4804_; 
v_a_4797_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4799_ = v___x_4735_;
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4735_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4802_; 
if (v_isShared_4800_ == 0)
{
v___x_4802_ = v___x_4799_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4797_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4726_ = stack[0].m_obj;
lean_object* v_a_4727_ = stack[1].m_obj;
lean_object* v_a_4728_ = stack[2].m_obj;
lean_object* v_res_4805_;
v_res_4805_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4726_, v_a_4727_, v_a_4728_);
stack->m_obj
 = v_res_4805_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4806_, v_a_4807_, v_a_4808_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
return v_res_4810_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4811_, lean_object* v_as_4812_, lean_object* v_as_x27_4813_, uint8_t v_b_4814_, lean_object* v_a_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_){
_start:
{
lean_object* v___x_4819_; 
v___x_4819_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4811_, v_as_x27_4813_, v_b_4814_);
return v___x_4819_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_foundPanic_4811_ = stack[0].m_num;
lean_object* v_as_4812_ = stack[1].m_obj;
lean_object* v_as_x27_4813_ = stack[2].m_obj;
uint8_t v_b_4814_ = stack[3].m_num;
lean_object* v___y_4816_ = stack[5].m_obj;
lean_object* v___y_4817_ = stack[6].m_obj;
lean_object* v_res_4820_;
v_res_4820_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_4811_, v_as_4812_, v_as_x27_4813_, v_b_4814_, lean_box(0), v___y_4816_, v___y_4817_);
stack->m_obj
 = v_res_4820_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4821_, lean_object* v_as_4822_, lean_object* v_as_x27_4823_, lean_object* v_b_4824_, lean_object* v_a_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
uint8_t v_foundPanic_boxed_4829_; uint8_t v_b_boxed_4830_; lean_object* v_res_4831_; 
v_foundPanic_boxed_4829_ = lean_unbox(v_foundPanic_4821_);
v_b_boxed_4830_ = lean_unbox(v_b_4824_);
v_res_4831_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4829_, v_as_4822_, v_as_x27_4823_, v_b_boxed_4830_, v_a_4825_, v___y_4826_, v___y_4827_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec(v_as_x27_4823_);
lean_dec(v_as_4822_);
return v_res_4831_;
}
}
lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4840_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4841_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4842_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4843_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4844_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4840_, v___x_4841_, v___x_4842_, v___x_4843_);
return v___x_4844_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4845_;
v_res_4845_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
stack->m_obj
 = v_res_4845_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4847_;
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
