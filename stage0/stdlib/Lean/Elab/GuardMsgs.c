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
v___x_121_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___lam__0(v___y_117_, v_pos_111_);
v___x_122_ = lean_string_append(v___x_120_, v___x_121_);
lean_dec_ref(v___x_121_);
v___x_123_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__2));
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
v___x_125_ = lean_string_append(v___x_124_, v___y_119_);
lean_dec_ref(v___y_119_);
v___x_126_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
v___x_128_ = lean_string_append(v___x_127_, v___y_118_);
lean_dec_ref(v___y_118_);
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
v___y_117_ = v_val_131_;
v___y_118_ = v_str_130_;
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
v___y_117_ = v_val_134_;
v___y_118_ = v_str_130_;
v___y_119_ = v___x_139_;
goto v___jp_116_;
}
else
{
lean_object* v___x_140_; 
lean_inc(v_column_136_);
lean_dec(v_val_133_);
v___x_140_ = l_Nat_reprFast(v_column_136_);
v___y_117_ = v_val_134_;
v___y_118_ = v_str_130_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___impl(uint8_t v_x_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_box(v_x_174_);
v___x_176_ = lean_obj_tag_nat(v___x_175_);
lean_dec(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___impl___boxed(lean_object* v_x_177_){
_start:
{
uint8_t v_x_4__boxed_178_; lean_object* v_res_179_; 
v_x_4__boxed_178_ = lean_unbox(v_x_177_);
v_res_179_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorIdx___impl(v_x_4__boxed_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(lean_object* v_k_180_){
_start:
{
lean_inc(v_k_180_);
return v_k_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg___boxed(lean_object* v_k_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___redArg(v_k_181_);
lean_dec(v_k_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(lean_object* v_motive_183_, lean_object* v_ctorIdx_184_, uint8_t v_t_185_, lean_object* v_h_186_, lean_object* v_k_187_){
_start:
{
lean_inc(v_k_187_);
return v_k_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim___boxed(lean_object* v_motive_188_, lean_object* v_ctorIdx_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_k_192_){
_start:
{
uint8_t v_t_boxed_193_; lean_object* v_res_194_; 
v_t_boxed_193_ = lean_unbox(v_t_190_);
v_res_194_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_ctorElim(v_motive_188_, v_ctorIdx_189_, v_t_boxed_193_, v_h_191_, v_k_192_);
lean_dec(v_k_192_);
lean_dec(v_ctorIdx_189_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(lean_object* v_check_195_){
_start:
{
lean_inc(v_check_195_);
return v_check_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg___boxed(lean_object* v_check_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___redArg(v_check_196_);
lean_dec(v_check_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(lean_object* v_motive_198_, uint8_t v_t_199_, lean_object* v_h_200_, lean_object* v_check_201_){
_start:
{
lean_inc(v_check_201_);
return v_check_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim___boxed(lean_object* v_motive_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_check_205_){
_start:
{
uint8_t v_t_boxed_206_; lean_object* v_res_207_; 
v_t_boxed_206_ = lean_unbox(v_t_203_);
v_res_207_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_check_elim(v_motive_202_, v_t_boxed_206_, v_h_204_, v_check_205_);
lean_dec(v_check_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(lean_object* v_drop_208_){
_start:
{
lean_inc(v_drop_208_);
return v_drop_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg___boxed(lean_object* v_drop_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___redArg(v_drop_209_);
lean_dec(v_drop_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(lean_object* v_motive_211_, uint8_t v_t_212_, lean_object* v_h_213_, lean_object* v_drop_214_){
_start:
{
lean_inc(v_drop_214_);
return v_drop_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim___boxed(lean_object* v_motive_215_, lean_object* v_t_216_, lean_object* v_h_217_, lean_object* v_drop_218_){
_start:
{
uint8_t v_t_boxed_219_; lean_object* v_res_220_; 
v_t_boxed_219_ = lean_unbox(v_t_216_);
v_res_220_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_drop_elim(v_motive_215_, v_t_boxed_219_, v_h_217_, v_drop_218_);
lean_dec(v_drop_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(lean_object* v_pass_221_){
_start:
{
lean_inc(v_pass_221_);
return v_pass_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg___boxed(lean_object* v_pass_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___redArg(v_pass_222_);
lean_dec(v_pass_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(lean_object* v_motive_224_, uint8_t v_t_225_, lean_object* v_h_226_, lean_object* v_pass_227_){
_start:
{
lean_inc(v_pass_227_);
return v_pass_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim___boxed(lean_object* v_motive_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_pass_231_){
_start:
{
uint8_t v_t_boxed_232_; lean_object* v_res_233_; 
v_t_boxed_232_ = lean_unbox(v_t_229_);
v_res_233_ = l_Lean_Elab_Tactic_GuardMsgs_FilterSpec_pass_elim(v_motive_228_, v_t_boxed_232_, v_h_230_, v_pass_231_);
lean_dec(v_pass_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___impl(uint8_t v_x_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_box(v_x_234_);
v___x_236_ = lean_obj_tag_nat(v___x_235_);
lean_dec(v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___impl___boxed(lean_object* v_x_237_){
_start:
{
uint8_t v_x_4__boxed_238_; lean_object* v_res_239_; 
v_x_4__boxed_238_ = lean_unbox(v_x_237_);
v_res_239_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorIdx___impl(v_x_4__boxed_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(lean_object* v_k_240_){
_start:
{
lean_inc(v_k_240_);
return v_k_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg___boxed(lean_object* v_k_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___redArg(v_k_241_);
lean_dec(v_k_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(lean_object* v_motive_243_, lean_object* v_ctorIdx_244_, uint8_t v_t_245_, lean_object* v_h_246_, lean_object* v_k_247_){
_start:
{
lean_inc(v_k_247_);
return v_k_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim___boxed(lean_object* v_motive_248_, lean_object* v_ctorIdx_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_k_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_ctorElim(v_motive_248_, v_ctorIdx_249_, v_t_boxed_253_, v_h_251_, v_k_252_);
lean_dec(v_k_252_);
lean_dec(v_ctorIdx_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(lean_object* v_exact_255_){
_start:
{
lean_inc(v_exact_255_);
return v_exact_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg___boxed(lean_object* v_exact_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___redArg(v_exact_256_);
lean_dec(v_exact_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_exact_261_){
_start:
{
lean_inc(v_exact_261_);
return v_exact_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_exact_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_exact_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_exact_265_);
lean_dec(v_exact_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(lean_object* v_normalized_268_){
_start:
{
lean_inc(v_normalized_268_);
return v_normalized_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg___boxed(lean_object* v_normalized_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___redArg(v_normalized_269_);
lean_dec(v_normalized_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(lean_object* v_motive_271_, uint8_t v_t_272_, lean_object* v_h_273_, lean_object* v_normalized_274_){
_start:
{
lean_inc(v_normalized_274_);
return v_normalized_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim___boxed(lean_object* v_motive_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_normalized_278_){
_start:
{
uint8_t v_t_boxed_279_; lean_object* v_res_280_; 
v_t_boxed_279_ = lean_unbox(v_t_276_);
v_res_280_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_normalized_elim(v_motive_275_, v_t_boxed_279_, v_h_277_, v_normalized_278_);
lean_dec(v_normalized_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(lean_object* v_lax_281_){
_start:
{
lean_inc(v_lax_281_);
return v_lax_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg___boxed(lean_object* v_lax_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___redArg(v_lax_282_);
lean_dec(v_lax_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(lean_object* v_motive_284_, uint8_t v_t_285_, lean_object* v_h_286_, lean_object* v_lax_287_){
_start:
{
lean_inc(v_lax_287_);
return v_lax_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim___boxed(lean_object* v_motive_288_, lean_object* v_t_289_, lean_object* v_h_290_, lean_object* v_lax_291_){
_start:
{
uint8_t v_t_boxed_292_; lean_object* v_res_293_; 
v_t_boxed_292_ = lean_unbox(v_t_289_);
v_res_293_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_lax_elim(v_motive_288_, v_t_boxed_292_, v_h_290_, v_lax_291_);
lean_dec(v_lax_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___impl(uint8_t v_x_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_box(v_x_294_);
v___x_296_ = lean_obj_tag_nat(v___x_295_);
lean_dec(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___impl___boxed(lean_object* v_x_297_){
_start:
{
uint8_t v_x_4__boxed_298_; lean_object* v_res_299_; 
v_x_4__boxed_298_ = lean_unbox(v_x_297_);
v_res_299_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorIdx___impl(v_x_4__boxed_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(lean_object* v_k_300_){
_start:
{
lean_inc(v_k_300_);
return v_k_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg___boxed(lean_object* v_k_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___redArg(v_k_301_);
lean_dec(v_k_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(lean_object* v_motive_303_, lean_object* v_ctorIdx_304_, uint8_t v_t_305_, lean_object* v_h_306_, lean_object* v_k_307_){
_start:
{
lean_inc(v_k_307_);
return v_k_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim___boxed(lean_object* v_motive_308_, lean_object* v_ctorIdx_309_, lean_object* v_t_310_, lean_object* v_h_311_, lean_object* v_k_312_){
_start:
{
uint8_t v_t_boxed_313_; lean_object* v_res_314_; 
v_t_boxed_313_ = lean_unbox(v_t_310_);
v_res_314_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_ctorElim(v_motive_308_, v_ctorIdx_309_, v_t_boxed_313_, v_h_311_, v_k_312_);
lean_dec(v_k_312_);
lean_dec(v_ctorIdx_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(lean_object* v_exact_315_){
_start:
{
lean_inc(v_exact_315_);
return v_exact_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg___boxed(lean_object* v_exact_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___redArg(v_exact_316_);
lean_dec(v_exact_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(lean_object* v_motive_318_, uint8_t v_t_319_, lean_object* v_h_320_, lean_object* v_exact_321_){
_start:
{
lean_inc(v_exact_321_);
return v_exact_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim___boxed(lean_object* v_motive_322_, lean_object* v_t_323_, lean_object* v_h_324_, lean_object* v_exact_325_){
_start:
{
uint8_t v_t_boxed_326_; lean_object* v_res_327_; 
v_t_boxed_326_ = lean_unbox(v_t_323_);
v_res_327_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_exact_elim(v_motive_322_, v_t_boxed_326_, v_h_324_, v_exact_325_);
lean_dec(v_exact_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(lean_object* v_sorted_328_){
_start:
{
lean_inc(v_sorted_328_);
return v_sorted_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg___boxed(lean_object* v_sorted_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___redArg(v_sorted_329_);
lean_dec(v_sorted_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(lean_object* v_motive_331_, uint8_t v_t_332_, lean_object* v_h_333_, lean_object* v_sorted_334_){
_start:
{
lean_inc(v_sorted_334_);
return v_sorted_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim___boxed(lean_object* v_motive_335_, lean_object* v_t_336_, lean_object* v_h_337_, lean_object* v_sorted_338_){
_start:
{
uint8_t v_t_boxed_339_; lean_object* v_res_340_; 
v_t_boxed_339_ = lean_unbox(v_t_336_);
v_res_340_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_sorted_elim(v_motive_335_, v_t_boxed_339_, v_h_337_, v_sorted_338_);
lean_dec(v_sorted_338_);
return v_res_340_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_box(0);
v___x_342_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg(){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___closed__0);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg___boxed(lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(lean_object* v_00_u03b1_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___boxed(lean_object* v_00_u03b1_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0(v_00_u03b1_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(lean_object* v_action_x3f_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
if (lean_obj_tag(v_action_x3f_376_) == 1)
{
lean_object* v_val_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_411_; 
v_val_380_ = lean_ctor_get(v_action_x3f_376_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_action_x3f_376_);
if (v_isSharedCheck_411_ == 0)
{
v___x_382_ = v_action_x3f_376_;
v_isShared_383_ = v_isSharedCheck_411_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_val_380_);
lean_dec(v_action_x3f_376_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_411_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__1));
lean_inc(v_val_380_);
v___x_385_ = l_Lean_Syntax_isOfKind(v_val_380_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_del_object(v___x_382_);
lean_dec(v_val_380_);
v___x_386_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = l_Lean_Syntax_getArg(v_val_380_, v___x_387_);
lean_dec(v_val_380_);
v___x_389_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__4));
lean_inc(v___x_388_);
v___x_390_ = l_Lean_Syntax_isOfKind(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__6));
lean_inc(v___x_388_);
v___x_392_ = l_Lean_Syntax_isOfKind(v___x_388_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___closed__8));
v___x_394_ = l_Lean_Syntax_isOfKind(v___x_388_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
lean_del_object(v___x_382_);
v___x_395_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_395_;
}
else
{
uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = 2;
v___x_397_ = lean_box(v___x_396_);
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 0);
lean_ctor_set(v___x_382_, 0, v___x_397_);
v___x_399_ = v___x_382_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
else
{
uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
lean_dec(v___x_388_);
v___x_401_ = 1;
v___x_402_ = lean_box(v___x_401_);
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 0);
lean_ctor_set(v___x_382_, 0, v___x_402_);
v___x_404_ = v___x_382_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
lean_dec(v___x_388_);
v___x_406_ = 0;
v___x_407_ = lean_box(v___x_406_);
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 0);
lean_ctor_set(v___x_382_, 0, v___x_407_);
v___x_409_ = v___x_382_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
else
{
uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec(v_action_x3f_376_);
v___x_412_ = 0;
v___x_413_ = lean_box(v___x_412_);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction___boxed(lean_object* v_action_x3f_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
return v_res_419_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(uint8_t v___x_420_, lean_object* v_x_421_){
_start:
{
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed(lean_object* v___x_422_, lean_object* v_x_423_){
_start:
{
uint8_t v___x_777__boxed_424_; uint8_t v_res_425_; lean_object* v_r_426_; 
v___x_777__boxed_424_ = lean_unbox(v___x_422_);
v_res_425_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_777__boxed_424_, v_x_423_);
lean_dec_ref(v_x_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(uint8_t v___x_427_, uint8_t v___x_428_, lean_object* v_msg_429_){
_start:
{
uint8_t v___y_431_; uint8_t v___x_435_; 
v___x_435_ = l_Lean_Message_isTrace(v_msg_429_);
if (v___x_435_ == 0)
{
v___y_431_ = v___x_428_;
goto v___jp_430_;
}
else
{
v___y_431_ = v___x_427_;
goto v___jp_430_;
}
v___jp_430_:
{
if (v___y_431_ == 0)
{
return v___x_427_;
}
else
{
uint8_t v_severity_432_; uint8_t v___x_433_; uint8_t v___x_434_; 
v_severity_432_ = lean_ctor_get_uint8(v_msg_429_, sizeof(void*)*5 + 1);
v___x_433_ = 2;
v___x_434_ = l_Lean_instBEqMessageSeverity_beq(v_severity_432_, v___x_433_);
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object* v___x_436_, lean_object* v___x_437_, lean_object* v_msg_438_){
_start:
{
uint8_t v___x_783__boxed_439_; uint8_t v___x_784__boxed_440_; uint8_t v_res_441_; lean_object* v_r_442_; 
v___x_783__boxed_439_ = lean_unbox(v___x_436_);
v___x_784__boxed_440_ = lean_unbox(v___x_437_);
v_res_441_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_783__boxed_439_, v___x_784__boxed_440_, v_msg_438_);
lean_dec_ref(v_msg_438_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(uint8_t v___x_443_, uint8_t v___x_444_, lean_object* v_msg_445_){
_start:
{
uint8_t v___y_447_; uint8_t v___x_451_; 
v___x_451_ = l_Lean_Message_isTrace(v_msg_445_);
if (v___x_451_ == 0)
{
v___y_447_ = v___x_444_;
goto v___jp_446_;
}
else
{
v___y_447_ = v___x_443_;
goto v___jp_446_;
}
v___jp_446_:
{
if (v___y_447_ == 0)
{
return v___x_443_;
}
else
{
uint8_t v_severity_448_; uint8_t v___x_449_; uint8_t v___x_450_; 
v_severity_448_ = lean_ctor_get_uint8(v_msg_445_, sizeof(void*)*5 + 1);
v___x_449_ = 1;
v___x_450_ = l_Lean_instBEqMessageSeverity_beq(v_severity_448_, v___x_449_);
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object* v___x_452_, lean_object* v___x_453_, lean_object* v_msg_454_){
_start:
{
uint8_t v___x_799__boxed_455_; uint8_t v___x_800__boxed_456_; uint8_t v_res_457_; lean_object* v_r_458_; 
v___x_799__boxed_455_ = lean_unbox(v___x_452_);
v___x_800__boxed_456_ = lean_unbox(v___x_453_);
v_res_457_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_799__boxed_455_, v___x_800__boxed_456_, v_msg_454_);
lean_dec_ref(v_msg_454_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(uint8_t v___x_459_, uint8_t v___x_460_, lean_object* v_msg_461_){
_start:
{
uint8_t v___y_463_; uint8_t v___x_467_; 
v___x_467_ = l_Lean_Message_isTrace(v_msg_461_);
if (v___x_467_ == 0)
{
v___y_463_ = v___x_460_;
goto v___jp_462_;
}
else
{
v___y_463_ = v___x_459_;
goto v___jp_462_;
}
v___jp_462_:
{
if (v___y_463_ == 0)
{
return v___x_459_;
}
else
{
uint8_t v_severity_464_; uint8_t v___x_465_; uint8_t v___x_466_; 
v_severity_464_ = lean_ctor_get_uint8(v_msg_461_, sizeof(void*)*5 + 1);
v___x_465_ = 0;
v___x_466_ = l_Lean_instBEqMessageSeverity_beq(v_severity_464_, v___x_465_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object* v___x_468_, lean_object* v___x_469_, lean_object* v_msg_470_){
_start:
{
uint8_t v___x_815__boxed_471_; uint8_t v___x_816__boxed_472_; uint8_t v_res_473_; lean_object* v_r_474_; 
v___x_815__boxed_471_ = lean_unbox(v___x_468_);
v___x_816__boxed_472_ = lean_unbox(v___x_469_);
v_res_473_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_815__boxed_471_, v___x_816__boxed_472_, v_msg_470_);
lean_dec_ref(v_msg_470_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(lean_object* v_x_500_){
_start:
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1));
lean_inc(v_x_500_);
v___x_503_ = l_Lean_Syntax_isOfKind(v_x_500_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec(v_x_500_);
v___x_504_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_504_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = l_Lean_Syntax_getArg(v_x_500_, v___x_505_);
lean_dec(v_x_500_);
v___x_507_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3));
lean_inc(v___x_506_);
v___x_508_ = l_Lean_Syntax_isOfKind(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5));
lean_inc(v___x_506_);
v___x_510_ = l_Lean_Syntax_isOfKind(v___x_506_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7));
lean_inc(v___x_506_);
v___x_512_ = l_Lean_Syntax_isOfKind(v___x_506_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9));
lean_inc(v___x_506_);
v___x_514_ = l_Lean_Syntax_isOfKind(v___x_506_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11));
v___x_516_ = l_Lean_Syntax_isOfKind(v___x_506_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v___f_519_; lean_object* v___x_520_; 
v___x_518_ = lean_box(v___x_516_);
v___f_519_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_519_, 0, v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___f_519_);
return v___x_520_;
}
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___f_523_; lean_object* v___x_524_; 
lean_dec(v___x_506_);
v___x_521_ = lean_box(v___x_512_);
v___x_522_ = lean_box(v___x_514_);
v___f_523_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_523_, 0, v___x_521_);
lean_closure_set(v___f_523_, 1, v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___f_523_);
return v___x_524_;
}
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_528_; 
lean_dec(v___x_506_);
v___x_525_ = lean_box(v___x_510_);
v___x_526_ = lean_box(v___x_512_);
v___f_527_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_527_, 0, v___x_525_);
lean_closure_set(v___f_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___f_527_);
return v___x_528_;
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___f_531_; lean_object* v___x_532_; 
lean_dec(v___x_506_);
v___x_529_ = lean_box(v___x_508_);
v___x_530_ = lean_box(v___x_510_);
v___f_531_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_531_, 0, v___x_529_);
lean_closure_set(v___f_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___f_531_);
return v___x_532_;
}
}
else
{
lean_object* v___f_533_; lean_object* v___x_534_; 
lean_dec(v___x_506_);
v___f_533_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12));
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___f_533_);
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___boxed(lean_object* v_x_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(lean_object* v_x_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_538_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___boxed(lean_object* v_x_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(v_x_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
return v_res_547_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object* v_x_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = 0;
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object* v_x_550_){
_start:
{
uint8_t v_res_551_; lean_object* v_r_552_; 
v_res_551_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(v_x_550_);
lean_dec_ref(v_x_550_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(lean_object* v_snd_553_, lean_object* v___y_554_){
_start:
{
if (lean_obj_tag(v_snd_553_) == 0)
{
uint8_t v___x_555_; 
lean_dec_ref(v___y_554_);
v___x_555_ = 0;
return v___x_555_;
}
else
{
lean_object* v_val_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_val_556_ = lean_ctor_get(v_snd_553_, 0);
lean_inc(v_val_556_);
lean_dec_ref_known(v_snd_553_, 1);
v___x_557_ = lean_apply_1(v_val_556_, v___y_554_);
v___x_558_ = lean_unbox(v___x_557_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed(lean_object* v_snd_559_, lean_object* v___y_560_){
_start:
{
uint8_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(v_snd_559_, v___y_560_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(lean_object* v_a_563_, lean_object* v_snd_564_, uint8_t v_a_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_567_; uint8_t v___x_568_; 
lean_inc_ref(v___y_566_);
v___x_567_ = lean_apply_1(v_a_563_, v___y_566_);
v___x_568_ = lean_unbox(v___x_567_);
if (v___x_568_ == 0)
{
if (lean_obj_tag(v_snd_564_) == 0)
{
uint8_t v___x_569_; 
lean_dec_ref(v___y_566_);
v___x_569_ = 2;
return v___x_569_;
}
else
{
lean_object* v_val_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_val_570_ = lean_ctor_get(v_snd_564_, 0);
lean_inc(v_val_570_);
lean_dec_ref_known(v_snd_564_, 1);
v___x_571_ = lean_apply_1(v_val_570_, v___y_566_);
v___x_572_ = lean_unbox(v___x_571_);
return v___x_572_;
}
}
else
{
lean_dec_ref(v___y_566_);
lean_dec(v_snd_564_);
return v_a_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed(lean_object* v_a_573_, lean_object* v_snd_574_, lean_object* v_a_575_, lean_object* v___y_576_){
_start:
{
uint8_t v_a_6388__boxed_577_; uint8_t v_res_578_; lean_object* v_r_579_; 
v_a_6388__boxed_577_ = lean_unbox(v_a_575_);
v_res_578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_573_, v_snd_574_, v_a_6388__boxed_577_, v___y_576_);
v_r_579_ = lean_box(v_res_578_);
return v_r_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object* v_as_640_, size_t v_sz_641_, size_t v_i_642_, lean_object* v_b_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_a_648_; uint8_t v___x_652_; 
v___x_652_ = lean_usize_dec_lt(v_i_642_, v_sz_641_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v_b_643_);
return v___x_653_;
}
else
{
lean_object* v_snd_654_; lean_object* v_snd_655_; lean_object* v_snd_656_; lean_object* v_fst_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_964_; 
v_snd_654_ = lean_ctor_get(v_b_643_, 1);
lean_inc(v_snd_654_);
v_snd_655_ = lean_ctor_get(v_snd_654_, 1);
lean_inc(v_snd_655_);
v_snd_656_ = lean_ctor_get(v_snd_655_, 1);
lean_inc(v_snd_656_);
v_fst_657_ = lean_ctor_get(v_b_643_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_b_643_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v_b_643_, 1);
lean_dec(v_unused_965_);
v___x_659_ = v_b_643_;
v_isShared_660_ = v_isSharedCheck_964_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_fst_657_);
lean_dec(v_b_643_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_964_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_fst_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_962_; 
v_fst_661_ = lean_ctor_get(v_snd_654_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_snd_654_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_snd_654_, 1);
lean_dec(v_unused_963_);
v___x_663_ = v_snd_654_;
v_isShared_664_ = v_isSharedCheck_962_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_fst_661_);
lean_dec(v_snd_654_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_962_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_fst_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_960_; 
v_fst_665_ = lean_ctor_get(v_snd_655_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_snd_655_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v_snd_655_, 1);
lean_dec(v_unused_961_);
v___x_667_ = v_snd_655_;
v_isShared_668_ = v_isSharedCheck_960_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_fst_665_);
lean_dec(v_snd_655_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_960_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_fst_669_; lean_object* v_snd_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_959_; 
v_fst_669_ = lean_ctor_get(v_snd_656_, 0);
v_snd_670_ = lean_ctor_get(v_snd_656_, 1);
v_isSharedCheck_959_ = !lean_is_exclusive(v_snd_656_);
if (v_isSharedCheck_959_ == 0)
{
v___x_672_ = v_snd_656_;
v_isShared_673_ = v_isSharedCheck_959_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_snd_670_);
lean_inc(v_fst_669_);
lean_dec(v_snd_656_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_959_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_a_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_a_674_ = lean_array_uget_borrowed(v_as_640_, v_i_642_);
v___x_675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_a_674_);
v___x_676_ = l_Lean_Syntax_isOfKind(v_a_674_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v___x_679_; 
lean_dec_ref_known(v___x_677_, 1);
if (v_isShared_673_ == 0)
{
v___x_679_ = v___x_672_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_fst_669_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_snd_670_);
v___x_679_ = v_reuseFailAlloc_689_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_679_);
v___x_681_ = v___x_667_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_fst_665_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_688_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_681_);
v___x_683_ = v___x_663_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_fst_661_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_681_);
v___x_683_ = v_reuseFailAlloc_687_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_685_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_683_);
v___x_685_ = v___x_659_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_fst_657_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
v_a_648_ = v___x_685_;
goto v___jp_647_;
}
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_del_object(v___x_672_);
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_del_object(v___x_667_);
lean_dec(v_fst_665_);
lean_del_object(v___x_663_);
lean_dec(v_fst_661_);
lean_del_object(v___x_659_);
lean_dec(v_fst_657_);
v_a_690_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_677_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_677_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_action_x3f_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = l_Lean_Syntax_getArg(v_a_674_, v___x_698_);
v___x_740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3));
lean_inc(v___x_699_);
v___x_741_ = l_Lean_Syntax_isOfKind(v___x_699_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; uint8_t v___x_743_; 
lean_del_object(v___x_672_);
lean_del_object(v___x_667_);
lean_del_object(v___x_663_);
lean_del_object(v___x_659_);
v___x_742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5));
lean_inc(v___x_699_);
v___x_743_ = l_Lean_Syntax_isOfKind(v___x_699_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; uint8_t v_reportPositions_745_; 
v___x_744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7));
lean_inc(v___x_699_);
v_reportPositions_745_ = l_Lean_Syntax_isOfKind(v___x_699_, v___x_744_);
if (v_reportPositions_745_ == 0)
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9));
lean_inc(v___x_699_);
v___x_747_ = l_Lean_Syntax_isOfKind(v___x_699_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11));
lean_inc(v___x_699_);
v___x_749_ = l_Lean_Syntax_isOfKind(v___x_699_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
lean_dec(v___x_699_);
v___x_750_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref_known(v___x_750_, 1);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_fst_669_);
lean_ctor_set(v___x_751_, 1, v_snd_670_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_fst_665_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_fst_661_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_fst_657_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v_a_648_ = v___x_754_;
goto v___jp_647_;
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
lean_dec(v_fst_657_);
v_a_755_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_750_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_750_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_763_ = lean_unsigned_to_nat(2u);
v___x_764_ = l_Lean_Syntax_getArg(v___x_699_, v___x_763_);
lean_dec(v___x_699_);
v___x_765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_764_);
v___x_766_ = l_Lean_Syntax_isOfKind(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_768_ = l_Lean_Syntax_isOfKind(v___x_764_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref_known(v___x_769_, 1);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v_fst_669_);
lean_ctor_set(v___x_770_, 1, v_snd_670_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_fst_665_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_fst_661_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_fst_657_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v_a_648_ = v___x_773_;
goto v___jp_647_;
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
lean_dec(v_fst_657_);
v_a_774_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_769_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_769_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec(v_fst_669_);
v___x_782_ = lean_box(v_reportPositions_745_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_snd_670_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_fst_665_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_fst_661_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_fst_657_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v_a_648_ = v___x_786_;
goto v___jp_647_;
}
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec(v___x_764_);
lean_dec(v_fst_669_);
v___x_787_ = lean_box(v___x_676_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v_snd_670_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_fst_665_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_fst_661_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_fst_657_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v_a_648_ = v___x_791_;
goto v___jp_647_;
}
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_792_ = lean_unsigned_to_nat(2u);
v___x_793_ = l_Lean_Syntax_getArg(v___x_699_, v___x_792_);
lean_dec(v___x_699_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17));
lean_inc(v___x_793_);
v___x_795_ = l_Lean_Syntax_isOfKind(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
lean_dec(v___x_793_);
v___x_796_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref_known(v___x_796_, 1);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_fst_669_);
lean_ctor_set(v___x_797_, 1, v_snd_670_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v_fst_665_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_fst_661_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_fst_657_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v_a_648_ = v___x_800_;
goto v___jp_647_;
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
lean_dec(v_fst_657_);
v_a_801_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_796_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_796_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_809_ = l_Lean_Syntax_getArg(v___x_793_, v___x_698_);
lean_dec(v___x_793_);
v___x_810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_809_);
v___x_811_ = l_Lean_Syntax_isOfKind(v___x_809_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_813_ = l_Lean_Syntax_isOfKind(v___x_809_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec_ref_known(v___x_814_, 1);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_fst_669_);
lean_ctor_set(v___x_815_, 1, v_snd_670_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_fst_665_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_fst_661_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_fst_657_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v_a_648_ = v___x_818_;
goto v___jp_647_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
lean_dec(v_fst_657_);
v_a_819_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_814_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_814_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec(v_fst_665_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v_fst_669_);
lean_ctor_set(v___x_827_, 1, v_snd_670_);
v___x_828_ = lean_box(v_reportPositions_745_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_827_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_fst_661_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_fst_657_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v_a_648_ = v___x_831_;
goto v___jp_647_;
}
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v___x_809_);
lean_dec(v_fst_665_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_fst_669_);
lean_ctor_set(v___x_832_, 1, v_snd_670_);
v___x_833_ = lean_box(v___x_676_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___x_832_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_fst_661_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_fst_657_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v_a_648_ = v___x_836_;
goto v___jp_647_;
}
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_837_ = lean_unsigned_to_nat(2u);
v___x_838_ = l_Lean_Syntax_getArg(v___x_699_, v___x_837_);
lean_dec(v___x_699_);
v___x_839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19));
lean_inc(v___x_838_);
v___x_840_ = l_Lean_Syntax_isOfKind(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec(v___x_838_);
v___x_841_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref_known(v___x_841_, 1);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v_fst_669_);
lean_ctor_set(v___x_842_, 1, v_snd_670_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_fst_665_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_fst_661_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_fst_657_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v_a_648_ = v___x_845_;
goto v___jp_647_;
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
lean_dec(v_fst_657_);
v_a_846_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_841_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_841_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_854_ = l_Lean_Syntax_getArg(v___x_838_, v___x_698_);
lean_dec(v___x_838_);
v___x_855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_854_);
v___x_856_ = l_Lean_Syntax_isOfKind(v___x_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23));
v___x_858_ = l_Lean_Syntax_isOfKind(v___x_854_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref_known(v___x_859_, 1);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_fst_669_);
lean_ctor_set(v___x_860_, 1, v_snd_670_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_fst_665_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_fst_661_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_fst_657_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v_a_648_ = v___x_863_;
goto v___jp_647_;
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
lean_dec(v_fst_657_);
v_a_864_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_859_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_859_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_dec(v_fst_661_);
v___x_872_ = 1;
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_fst_669_);
lean_ctor_set(v___x_873_, 1, v_snd_670_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_fst_665_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_box(v___x_872_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_874_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_fst_657_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v_a_648_ = v___x_877_;
goto v___jp_647_;
}
}
else
{
uint8_t v_ordering_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec(v___x_854_);
lean_dec(v_fst_661_);
v_ordering_878_ = 0;
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_fst_669_);
lean_ctor_set(v___x_879_, 1, v_snd_670_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_fst_665_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_box(v_ordering_878_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_880_);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v_fst_657_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v_a_648_ = v___x_883_;
goto v___jp_647_;
}
}
}
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_884_ = lean_unsigned_to_nat(2u);
v___x_885_ = l_Lean_Syntax_getArg(v___x_699_, v___x_884_);
lean_dec(v___x_699_);
v___x_886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25));
lean_inc(v___x_885_);
v___x_887_ = l_Lean_Syntax_isOfKind(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec(v___x_885_);
v___x_888_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec_ref_known(v___x_888_, 1);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v_fst_669_);
lean_ctor_set(v___x_889_, 1, v_snd_670_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v_fst_665_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_fst_661_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v_fst_657_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v_a_648_ = v___x_892_;
goto v___jp_647_;
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
lean_dec(v_fst_657_);
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
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_901_ = l_Lean_Syntax_getArg(v___x_885_, v___x_698_);
lean_dec(v___x_885_);
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_901_);
v___x_903_ = l_Lean_Syntax_isOfKind(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27));
lean_inc(v___x_901_);
v___x_905_ = l_Lean_Syntax_isOfKind(v___x_901_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29));
v___x_907_ = l_Lean_Syntax_isOfKind(v___x_901_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec_ref_known(v___x_908_, 1);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_fst_669_);
lean_ctor_set(v___x_909_, 1, v_snd_670_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_fst_665_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_fst_661_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_fst_657_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v_a_648_ = v___x_912_;
goto v___jp_647_;
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
lean_dec(v_fst_657_);
v_a_913_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_908_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_908_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v_fst_657_);
v___x_921_ = 2;
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_fst_669_);
lean_ctor_set(v___x_922_, 1, v_snd_670_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_fst_665_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v_fst_661_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_box(v___x_921_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_924_);
v_a_648_ = v___x_926_;
goto v___jp_647_;
}
}
else
{
uint8_t v_whitespace_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v___x_901_);
lean_dec(v_fst_657_);
v_whitespace_927_ = 1;
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_fst_669_);
lean_ctor_set(v___x_928_, 1, v_snd_670_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_fst_665_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v_fst_661_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = lean_box(v_whitespace_927_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_930_);
v_a_648_ = v___x_932_;
goto v___jp_647_;
}
}
else
{
uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v___x_901_);
lean_dec(v_fst_657_);
v___x_933_ = 0;
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_fst_669_);
lean_ctor_set(v___x_934_, 1, v_snd_670_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v_fst_665_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_fst_661_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_box(v___x_933_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
v_a_648_ = v___x_938_;
goto v___jp_647_;
}
}
}
}
else
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = l_Lean_Syntax_getArg(v___x_699_, v___x_698_);
v___x_940_ = l_Lean_Syntax_isNone(v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_939_);
v___x_942_ = l_Lean_Syntax_matchesNull(v___x_939_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
lean_dec(v___x_939_);
lean_dec(v___x_699_);
lean_del_object(v___x_672_);
lean_del_object(v___x_667_);
lean_del_object(v___x_663_);
lean_del_object(v___x_659_);
v___x_943_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec_ref_known(v___x_943_, 1);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_fst_669_);
lean_ctor_set(v___x_944_, 1, v_snd_670_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_fst_665_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_fst_661_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v_fst_657_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v_a_648_ = v___x_947_;
goto v___jp_647_;
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_dec(v_fst_665_);
lean_dec(v_fst_661_);
lean_dec(v_fst_657_);
v_a_948_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_943_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_943_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = l_Lean_Syntax_getArg(v___x_939_, v___x_698_);
lean_dec(v___x_939_);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
v_action_x3f_701_ = v___x_957_;
v___y_702_ = v___y_644_;
v___y_703_ = v___y_645_;
goto v___jp_700_;
}
}
else
{
lean_object* v___x_958_; 
lean_dec(v___x_939_);
v___x_958_ = lean_box(0);
v_action_x3f_701_ = v___x_958_;
v___y_702_ = v___y_644_;
v___y_703_ = v___y_645_;
goto v___jp_700_;
}
}
v___jp_700_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = l_Lean_Syntax_getArg(v___x_699_, v___x_704_);
lean_dec(v___x_699_);
v___x_706_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v___x_705_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___f_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___f_710_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_710_, 0, v_a_709_);
lean_closure_set(v___f_710_, 1, v_snd_670_);
lean_closure_set(v___f_710_, 2, v_a_707_);
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v___f_710_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v___x_711_);
v___x_713_ = v___x_672_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_fst_669_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_723_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_713_);
v___x_715_ = v___x_667_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_fst_665_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_713_);
v___x_715_ = v_reuseFailAlloc_722_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_715_);
v___x_717_ = v___x_663_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_fst_661_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_717_);
v___x_719_ = v___x_659_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_fst_657_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
v_a_648_ = v___x_719_;
goto v___jp_647_;
}
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_a_707_);
lean_del_object(v___x_672_);
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_del_object(v___x_667_);
lean_dec(v_fst_665_);
lean_del_object(v___x_663_);
lean_dec(v_fst_661_);
lean_del_object(v___x_659_);
lean_dec(v_fst_657_);
v_a_724_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_708_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_708_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v___x_705_);
lean_del_object(v___x_672_);
lean_dec(v_snd_670_);
lean_dec(v_fst_669_);
lean_del_object(v___x_667_);
lean_dec(v_fst_665_);
lean_del_object(v___x_663_);
lean_dec(v_fst_661_);
lean_del_object(v___x_659_);
lean_dec(v_fst_657_);
v_a_732_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_706_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_706_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
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
v___jp_647_:
{
size_t v___x_649_; size_t v___x_650_; 
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_add(v_i_642_, v___x_649_);
v_i_642_ = v___x_650_;
v_b_643_ = v_a_648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object* v_as_966_, lean_object* v_sz_967_, lean_object* v_i_968_, lean_object* v_b_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
size_t v_sz_boxed_973_; size_t v_i_boxed_974_; lean_object* v_res_975_; 
v_sz_boxed_973_ = lean_unbox_usize(v_sz_967_);
lean_dec(v_sz_967_);
v_i_boxed_974_ = lean_unbox_usize(v_i_968_);
lean_dec(v_i_968_);
v_res_975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v_as_966_, v_sz_boxed_973_, v_i_boxed_974_, v_b_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v_as_966_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(size_t v_sz_976_, size_t v_i_977_, lean_object* v_bs_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_lt(v_i_977_, v_sz_976_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v_bs_978_);
return v___x_980_;
}
else
{
lean_object* v_v_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_v_981_ = lean_array_uget(v_bs_978_, v_i_977_);
v___x_982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_v_981_);
v___x_983_ = l_Lean_Syntax_isOfKind(v_v_981_, v___x_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
lean_dec(v_v_981_);
lean_dec_ref(v_bs_978_);
v___x_984_ = lean_box(0);
return v___x_984_;
}
else
{
lean_object* v___x_985_; lean_object* v_bs_x27_986_; size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
v___x_985_ = lean_unsigned_to_nat(0u);
v_bs_x27_986_ = lean_array_uset(v_bs_978_, v_i_977_, v___x_985_);
v___x_987_ = ((size_t)1ULL);
v___x_988_ = lean_usize_add(v_i_977_, v___x_987_);
v___x_989_ = lean_array_uset(v_bs_x27_986_, v_i_977_, v_v_981_);
v_i_977_ = v___x_988_;
v_bs_978_ = v___x_989_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1___boxed(lean_object* v_sz_991_, lean_object* v_i_992_, lean_object* v_bs_993_){
_start:
{
size_t v_sz_boxed_994_; size_t v_i_boxed_995_; lean_object* v_res_996_; 
v_sz_boxed_994_ = lean_unbox_usize(v_sz_991_);
lean_dec(v_sz_991_);
v_i_boxed_995_ = lean_unbox_usize(v_i_992_);
lean_dec(v_i_992_);
v_res_996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_boxed_994_, v_i_boxed_995_, v_bs_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(uint8_t v___x_997_, lean_object* v_as_998_, size_t v_i_999_, size_t v_stop_1000_, lean_object* v_b_1001_){
_start:
{
lean_object* v___y_1003_; uint8_t v___x_1007_; 
v___x_1007_ = lean_usize_dec_eq(v_i_999_, v_stop_1000_);
if (v___x_1007_ == 0)
{
lean_object* v_fst_1008_; uint8_t v___x_1009_; 
v_fst_1008_ = lean_ctor_get(v_b_1001_, 0);
v___x_1009_ = lean_unbox(v_fst_1008_);
if (v___x_1009_ == 0)
{
lean_object* v_snd_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1018_; 
v_snd_1010_ = lean_ctor_get(v_b_1001_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_b_1001_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v_b_1001_, 0);
lean_dec(v_unused_1019_);
v___x_1012_ = v_b_1001_;
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_snd_1010_);
lean_dec(v_b_1001_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1014_ = lean_box(v___x_997_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1014_);
v___x_1016_ = v___x_1012_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_snd_1010_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
v___y_1003_ = v___x_1016_;
goto v___jp_1002_;
}
}
}
else
{
lean_object* v_snd_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1030_; 
v_snd_1020_ = lean_ctor_get(v_b_1001_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_b_1001_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; 
v_unused_1031_ = lean_ctor_get(v_b_1001_, 0);
lean_dec(v_unused_1031_);
v___x_1022_ = v_b_1001_;
v_isShared_1023_ = v_isSharedCheck_1030_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_snd_1020_);
lean_dec(v_b_1001_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1030_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1024_ = lean_array_uget_borrowed(v_as_998_, v_i_999_);
lean_inc(v___x_1024_);
v___x_1025_ = lean_array_push(v_snd_1020_, v___x_1024_);
v___x_1026_ = lean_box(v___x_1007_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v___x_1025_);
lean_ctor_set(v___x_1022_, 0, v___x_1026_);
v___x_1028_ = v___x_1022_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v___x_1025_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
v___y_1003_ = v___x_1028_;
goto v___jp_1002_;
}
}
}
}
else
{
return v_b_1001_;
}
v___jp_1002_:
{
size_t v___x_1004_; size_t v___x_1005_; 
v___x_1004_ = ((size_t)1ULL);
v___x_1005_ = lean_usize_add(v_i_999_, v___x_1004_);
v_i_999_ = v___x_1005_;
v_b_1001_ = v___y_1003_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object* v___x_1032_, lean_object* v_as_1033_, lean_object* v_i_1034_, lean_object* v_stop_1035_, lean_object* v_b_1036_){
_start:
{
uint8_t v___x_7263__boxed_1037_; size_t v_i_boxed_1038_; size_t v_stop_boxed_1039_; lean_object* v_res_1040_; 
v___x_7263__boxed_1037_ = lean_unbox(v___x_1032_);
v_i_boxed_1038_ = lean_unbox_usize(v_i_1034_);
lean_dec(v_i_1034_);
v_stop_boxed_1039_ = lean_unbox_usize(v_stop_1035_);
lean_dec(v_stop_1035_);
v_res_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_7263__boxed_1037_, v_as_1033_, v_i_boxed_1038_, v_stop_boxed_1039_, v_b_1036_);
lean_dec_ref(v_as_1033_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object* v_spec_x3f_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_elts_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1113_; lean_object* v_cfg_1127_; 
v_cfg_1127_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5));
if (lean_obj_tag(v_spec_x3f_1069_) == 1)
{
lean_object* v_val_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v_val_1128_ = lean_ctor_get(v_spec_x3f_1069_, 0);
lean_inc_n(v_val_1128_, 2);
lean_dec_ref_known(v_spec_x3f_1069_, 1);
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7));
v___x_1130_ = l_Lean_Syntax_isOfKind(v_val_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_val_1128_);
v___x_1131_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1140_ = lean_unsigned_to_nat(1u);
v___x_1141_ = l_Lean_Syntax_getArg(v_val_1128_, v___x_1140_);
lean_dec(v_val_1128_);
v___x_1142_ = l_Lean_Syntax_getArgs(v___x_1141_);
lean_dec(v___x_1141_);
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8));
v___x_1145_ = lean_array_get_size(v___x_1142_);
v___x_1146_ = lean_nat_dec_lt(v___x_1143_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_dec_ref(v___x_1142_);
v___y_1113_ = v___x_1144_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; lean_object* v_snd_1152_; 
v___x_1147_ = lean_box(v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v___x_1144_);
v___x_1149_ = ((size_t)0ULL);
v___x_1150_ = lean_usize_of_nat(v___x_1145_);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1130_, v___x_1142_, v___x_1149_, v___x_1150_, v___x_1148_);
lean_dec_ref(v___x_1142_);
v_snd_1152_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_snd_1152_);
lean_dec_ref(v___x_1151_);
v___y_1113_ = v_snd_1152_;
goto v___jp_1112_;
}
}
}
else
{
lean_object* v___x_1153_; 
lean_dec(v_spec_x3f_1069_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_cfg_1127_);
return v___x_1153_;
}
v___jp_1073_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; size_t v_sz_1079_; size_t v___x_1080_; lean_object* v___x_1081_; 
v___x_1077_ = l_Array_reverse___redArg(v_elts_1074_);
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4));
v_sz_1079_ = lean_array_size(v___x_1077_);
v___x_1080_ = ((size_t)0ULL);
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v___x_1077_, v_sz_1079_, v___x_1080_, v___x_1078_, v___y_1075_, v___y_1076_);
lean_dec_ref(v___x_1077_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1103_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1103_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1103_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_snd_1086_; lean_object* v_snd_1087_; lean_object* v_snd_1088_; lean_object* v_fst_1089_; lean_object* v_fst_1090_; lean_object* v_fst_1091_; lean_object* v_fst_1092_; lean_object* v_snd_1093_; lean_object* v___y_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; uint8_t v___x_1097_; uint8_t v___x_1098_; uint8_t v___x_1099_; lean_object* v___x_1101_; 
v_snd_1086_ = lean_ctor_get(v_a_1082_, 1);
lean_inc(v_snd_1086_);
v_snd_1087_ = lean_ctor_get(v_snd_1086_, 1);
lean_inc(v_snd_1087_);
v_snd_1088_ = lean_ctor_get(v_snd_1087_, 1);
lean_inc(v_snd_1088_);
v_fst_1089_ = lean_ctor_get(v_a_1082_, 0);
lean_inc(v_fst_1089_);
lean_dec(v_a_1082_);
v_fst_1090_ = lean_ctor_get(v_snd_1086_, 0);
lean_inc(v_fst_1090_);
lean_dec(v_snd_1086_);
v_fst_1091_ = lean_ctor_get(v_snd_1087_, 0);
lean_inc(v_fst_1091_);
lean_dec(v_snd_1087_);
v_fst_1092_ = lean_ctor_get(v_snd_1088_, 0);
lean_inc(v_fst_1092_);
v_snd_1093_ = lean_ctor_get(v_snd_1088_, 1);
lean_inc(v_snd_1093_);
lean_dec(v_snd_1088_);
v___y_1094_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___y_1094_, 0, v_snd_1093_);
v___x_1095_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1095_, 0, v___y_1094_);
v___x_1096_ = lean_unbox(v_fst_1089_);
lean_dec(v_fst_1089_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1, v___x_1096_);
v___x_1097_ = lean_unbox(v_fst_1090_);
lean_dec(v_fst_1090_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1 + 1, v___x_1097_);
v___x_1098_ = lean_unbox(v_fst_1091_);
lean_dec(v_fst_1091_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1 + 2, v___x_1098_);
v___x_1099_ = lean_unbox(v_fst_1092_);
lean_dec(v_fst_1092_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1 + 3, v___x_1099_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1095_);
v___x_1101_ = v___x_1084_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1095_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1081_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1081_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
v___jp_1112_:
{
size_t v_sz_1114_; size_t v___x_1115_; lean_object* v___x_1116_; 
v_sz_1114_ = lean_array_size(v___y_1113_);
v___x_1115_ = ((size_t)0ULL);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_1114_, v___x_1115_, v___y_1113_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v___x_1117_; lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v___x_1117_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_val_1126_; 
v_val_1126_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_val_1126_);
lean_dec_ref_known(v___x_1116_, 1);
v_elts_1074_ = v_val_1126_;
v___y_1075_ = v_a_1070_;
v___y_1076_ = v_a_1071_;
goto v___jp_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object* v_spec_x3f_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v_spec_x3f_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(lean_object* v_s_1171_, lean_object* v_replacement_1172_, lean_object* v_a_1173_, lean_object* v_b_1174_){
_start:
{
lean_object* v_it_1176_; lean_object* v_startPos_1177_; lean_object* v_endPos_1178_; lean_object* v_it_1187_; 
switch(lean_obj_tag(v_a_1173_))
{
case 0:
{
lean_object* v_pos_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1205_; 
v_pos_1193_ = lean_ctor_get(v_a_1173_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_a_1173_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1195_ = v_a_1173_;
v_isShared_1196_ = v_isSharedCheck_1205_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_pos_1193_);
lean_dec(v_a_1173_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1205_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_startInclusive_1197_; lean_object* v_endExclusive_1198_; lean_object* v___x_1199_; uint8_t v_decide_1200_; 
v_startInclusive_1197_ = lean_ctor_get(v_s_1171_, 1);
v_endExclusive_1198_ = lean_ctor_get(v_s_1171_, 2);
v___x_1199_ = lean_nat_sub(v_endExclusive_1198_, v_startInclusive_1197_);
v_decide_1200_ = lean_nat_dec_eq(v_pos_1193_, v___x_1199_);
lean_dec(v___x_1199_);
if (v_decide_1200_ == 0)
{
lean_object* v___x_1202_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set_tag(v___x_1195_, 1);
v___x_1202_ = v___x_1195_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_pos_1193_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
v_it_1187_ = v___x_1202_;
goto v___jp_1186_;
}
}
else
{
lean_object* v___x_1204_; 
lean_del_object(v___x_1195_);
lean_dec(v_pos_1193_);
v___x_1204_ = lean_box(3);
v_it_1187_ = v___x_1204_;
goto v___jp_1186_;
}
}
}
case 1:
{
lean_object* v_pos_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1218_; 
v_pos_1206_ = lean_ctor_get(v_a_1173_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_a_1173_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1208_ = v_a_1173_;
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_pos_1206_);
lean_dec(v_a_1173_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v_str_1210_; lean_object* v_startInclusive_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v_str_1210_ = lean_ctor_get(v_s_1171_, 0);
v_startInclusive_1211_ = lean_ctor_get(v_s_1171_, 1);
v___x_1212_ = lean_nat_add(v_startInclusive_1211_, v_pos_1206_);
v___x_1213_ = lean_string_utf8_next_fast(v_str_1210_, v___x_1212_);
lean_dec(v___x_1212_);
v___x_1214_ = lean_nat_sub(v___x_1213_, v_startInclusive_1211_);
lean_inc(v___x_1214_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set_tag(v___x_1208_, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1214_);
v___x_1216_ = v___x_1208_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
v_it_1176_ = v___x_1216_;
v_startPos_1177_ = v_pos_1206_;
v_endPos_1178_ = v___x_1214_;
goto v___jp_1175_;
}
}
}
case 2:
{
lean_object* v_needle_1219_; lean_object* v_table_1220_; lean_object* v_stackPos_1221_; lean_object* v_needlePos_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1283_; 
v_needle_1219_ = lean_ctor_get(v_a_1173_, 0);
v_table_1220_ = lean_ctor_get(v_a_1173_, 1);
v_stackPos_1221_ = lean_ctor_get(v_a_1173_, 2);
v_needlePos_1222_ = lean_ctor_get(v_a_1173_, 3);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_a_1173_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1224_ = v_a_1173_;
v_isShared_1225_ = v_isSharedCheck_1283_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_needlePos_1222_);
lean_inc(v_stackPos_1221_);
lean_inc(v_table_1220_);
lean_inc(v_needle_1219_);
lean_dec(v_a_1173_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1283_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_str_1226_; lean_object* v_startInclusive_1227_; lean_object* v_endExclusive_1228_; lean_object* v_str_1229_; lean_object* v_startInclusive_1230_; lean_object* v_endExclusive_1231_; lean_object* v_basePos_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_str_1226_ = lean_ctor_get(v_needle_1219_, 0);
v_startInclusive_1227_ = lean_ctor_get(v_needle_1219_, 1);
v_endExclusive_1228_ = lean_ctor_get(v_needle_1219_, 2);
v_str_1229_ = lean_ctor_get(v_s_1171_, 0);
v_startInclusive_1230_ = lean_ctor_get(v_s_1171_, 1);
v_endExclusive_1231_ = lean_ctor_get(v_s_1171_, 2);
v_basePos_1232_ = lean_nat_sub(v_stackPos_1221_, v_needlePos_1222_);
v___x_1233_ = lean_nat_sub(v_endExclusive_1228_, v_startInclusive_1227_);
v___x_1234_ = lean_nat_add(v_basePos_1232_, v___x_1233_);
v___x_1235_ = lean_nat_sub(v_endExclusive_1231_, v_startInclusive_1230_);
v___x_1236_ = lean_nat_dec_le(v___x_1234_, v___x_1235_);
lean_dec(v___x_1234_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
lean_dec(v___x_1233_);
lean_del_object(v___x_1224_);
lean_dec(v_needlePos_1222_);
lean_dec(v_stackPos_1221_);
lean_dec_ref(v_table_1220_);
lean_dec_ref(v_needle_1219_);
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_nat_add(v_basePos_1232_, v___x_1237_);
v___x_1239_ = lean_nat_dec_le(v___x_1238_, v___x_1235_);
lean_dec(v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec(v___x_1235_);
lean_dec(v_basePos_1232_);
lean_dec_ref(v_s_1171_);
return v_b_1174_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = l_String_Slice_pos_x21(v_s_1171_, v_basePos_1232_);
lean_dec(v_basePos_1232_);
v___x_1241_ = lean_box(3);
v_it_1176_ = v___x_1241_;
v_startPos_1177_ = v___x_1240_;
v_endPos_1178_ = v___x_1235_;
goto v___jp_1175_;
}
}
else
{
lean_object* v___x_1242_; uint8_t v_stackByte_1243_; lean_object* v___x_1244_; uint8_t v_patByte_1245_; uint8_t v___x_1246_; 
lean_dec(v___x_1235_);
v___x_1242_ = lean_nat_add(v_startInclusive_1230_, v_stackPos_1221_);
v_stackByte_1243_ = lean_string_get_byte_fast(v_str_1229_, v___x_1242_);
v___x_1244_ = lean_nat_add(v_startInclusive_1227_, v_needlePos_1222_);
v_patByte_1245_ = lean_string_get_byte_fast(v_str_1226_, v___x_1244_);
v___x_1246_ = lean_uint8_dec_eq(v_stackByte_1243_, v_patByte_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; uint8_t v_decide_1248_; 
lean_dec(v___x_1233_);
v___x_1247_ = lean_unsigned_to_nat(0u);
v_decide_1248_ = lean_nat_dec_eq(v_needlePos_1222_, v___x_1247_);
if (v_decide_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v_newNeedlePos_1251_; uint8_t v___x_1252_; 
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = lean_nat_sub(v_needlePos_1222_, v___x_1249_);
lean_dec(v_needlePos_1222_);
v_newNeedlePos_1251_ = lean_array_fget_borrowed(v_table_1220_, v___x_1250_);
lean_dec(v___x_1250_);
v___x_1252_ = lean_nat_dec_eq(v_newNeedlePos_1251_, v___x_1247_);
if (v___x_1252_ == 0)
{
lean_object* v_oldBasePos_1253_; lean_object* v___x_1254_; lean_object* v_newBasePos_1255_; lean_object* v___x_1257_; 
lean_inc(v_newNeedlePos_1251_);
v_oldBasePos_1253_ = l_String_Slice_pos_x21(v_s_1171_, v_basePos_1232_);
lean_dec(v_basePos_1232_);
v___x_1254_ = lean_nat_sub(v_stackPos_1221_, v_newNeedlePos_1251_);
v_newBasePos_1255_ = l_String_Slice_pos_x21(v_s_1171_, v___x_1254_);
lean_dec(v___x_1254_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 3, v_newNeedlePos_1251_);
v___x_1257_ = v___x_1224_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_needle_1219_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_table_1220_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_stackPos_1221_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_newNeedlePos_1251_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
v_it_1176_ = v___x_1257_;
v_startPos_1177_ = v_oldBasePos_1253_;
v_endPos_1178_ = v_newBasePos_1255_;
goto v___jp_1175_;
}
}
else
{
lean_object* v_basePos_1259_; lean_object* v_nextStackPos_1260_; lean_object* v___x_1262_; 
v_basePos_1259_ = l_String_Slice_pos_x21(v_s_1171_, v_basePos_1232_);
lean_dec(v_basePos_1232_);
v_nextStackPos_1260_ = l_String_Slice_posGE___redArg(v_s_1171_, v_stackPos_1221_);
lean_inc(v_nextStackPos_1260_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 3, v___x_1247_);
lean_ctor_set(v___x_1224_, 2, v_nextStackPos_1260_);
v___x_1262_ = v___x_1224_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_needle_1219_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_table_1220_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_nextStackPos_1260_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v___x_1247_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
v_it_1176_ = v___x_1262_;
v_startPos_1177_ = v_basePos_1259_;
v_endPos_1178_ = v_nextStackPos_1260_;
goto v___jp_1175_;
}
}
}
else
{
lean_object* v_basePos_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_nextStackPos_1267_; lean_object* v___x_1269_; 
lean_dec(v_basePos_1232_);
lean_dec(v_needlePos_1222_);
v_basePos_1264_ = l_String_Slice_pos_x21(v_s_1171_, v_stackPos_1221_);
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_add(v_stackPos_1221_, v___x_1265_);
lean_dec(v_stackPos_1221_);
v_nextStackPos_1267_ = l_String_Slice_posGE___redArg(v_s_1171_, v___x_1266_);
lean_inc(v_nextStackPos_1267_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 3, v___x_1247_);
lean_ctor_set(v___x_1224_, 2, v_nextStackPos_1267_);
v___x_1269_ = v___x_1224_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_needle_1219_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_table_1220_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_nextStackPos_1267_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v___x_1247_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
v_it_1176_ = v___x_1269_;
v_startPos_1177_ = v_basePos_1264_;
v_endPos_1178_ = v_nextStackPos_1267_;
goto v___jp_1175_;
}
}
}
else
{
lean_object* v___x_1271_; lean_object* v_nextStackPos_1272_; lean_object* v_nextNeedlePos_1273_; uint8_t v_decide_1274_; 
lean_dec(v_basePos_1232_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1272_ = lean_nat_add(v_stackPos_1221_, v___x_1271_);
lean_dec(v_stackPos_1221_);
v_nextNeedlePos_1273_ = lean_nat_add(v_needlePos_1222_, v___x_1271_);
lean_dec(v_needlePos_1222_);
v_decide_1274_ = lean_nat_dec_eq(v_nextNeedlePos_1273_, v___x_1233_);
lean_dec(v___x_1233_);
if (v_decide_1274_ == 0)
{
lean_object* v___x_1276_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 3, v_nextNeedlePos_1273_);
lean_ctor_set(v___x_1224_, 2, v_nextStackPos_1272_);
v___x_1276_ = v___x_1224_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_needle_1219_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_table_1220_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_nextStackPos_1272_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_nextNeedlePos_1273_);
v___x_1276_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
v_a_1173_ = v___x_1276_;
goto _start;
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
lean_dec(v_nextNeedlePos_1273_);
v___x_1279_ = lean_unsigned_to_nat(0u);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 3, v___x_1279_);
lean_ctor_set(v___x_1224_, 2, v_nextStackPos_1272_);
v___x_1281_ = v___x_1224_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_needle_1219_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_table_1220_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_nextStackPos_1272_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
v_it_1187_ = v___x_1281_;
goto v___jp_1186_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1171_);
return v_b_1174_;
}
}
v___jp_1175_:
{
lean_object* v___x_1179_; lean_object* v_str_1180_; lean_object* v_startInclusive_1181_; lean_object* v_endExclusive_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_inc_ref(v_s_1171_);
v___x_1179_ = l_String_Slice_slice_x21(v_s_1171_, v_startPos_1177_, v_endPos_1178_);
lean_dec(v_endPos_1178_);
lean_dec(v_startPos_1177_);
v_str_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc_ref(v_str_1180_);
v_startInclusive_1181_ = lean_ctor_get(v___x_1179_, 1);
lean_inc(v_startInclusive_1181_);
v_endExclusive_1182_ = lean_ctor_get(v___x_1179_, 2);
lean_inc(v_endExclusive_1182_);
lean_dec_ref(v___x_1179_);
v___x_1183_ = lean_string_utf8_extract_fast(v_str_1180_, v_startInclusive_1181_, v_endExclusive_1182_);
lean_dec(v_endExclusive_1182_);
lean_dec(v_startInclusive_1181_);
lean_dec_ref(v_str_1180_);
v___x_1184_ = lean_string_append(v_b_1174_, v___x_1183_);
lean_dec_ref(v___x_1183_);
v_a_1173_ = v_it_1176_;
v_b_1174_ = v___x_1184_;
goto _start;
}
v___jp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = lean_string_utf8_byte_size(v_replacement_1172_);
v___x_1190_ = lean_string_utf8_extract_fast(v_replacement_1172_, v___x_1188_, v___x_1189_);
v___x_1191_ = lean_string_append(v_b_1174_, v___x_1190_);
lean_dec_ref(v___x_1190_);
v_a_1173_ = v_it_1187_;
v_b_1174_ = v___x_1191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg___boxed(lean_object* v_s_1284_, lean_object* v_replacement_1285_, lean_object* v_a_1286_, lean_object* v_b_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1284_, v_replacement_1285_, v_a_1286_, v_b_1287_);
lean_dec_ref(v_replacement_1285_);
return v_res_1288_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1));
v___x_1295_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2);
v___x_1298_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1));
v___x_1299_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1297_);
lean_ctor_set(v___x_1299_, 2, v___x_1296_);
lean_ctor_set(v___x_1299_, 3, v___x_1296_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object* v_s_1300_, lean_object* v_replacement_1301_){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1303_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1304_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1300_, v_replacement_1301_, v___x_1303_, v___x_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___boxed(lean_object* v_s_1305_, lean_object* v_replacement_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1305_, v_replacement_1306_);
lean_dec_ref(v_replacement_1306_);
return v_res_1307_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1));
v___x_1314_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1313_);
return v___x_1314_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2);
v___x_1317_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1));
v___x_1318_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v___x_1316_);
lean_ctor_set(v___x_1318_, 2, v___x_1315_);
lean_ctor_set(v___x_1318_, 3, v___x_1315_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object* v_s_1319_, lean_object* v_replacement_1320_){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1322_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1323_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1319_, v_replacement_1320_, v___x_1322_, v___x_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object* v_s_1324_, lean_object* v_replacement_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1324_, v_replacement_1325_);
lean_dec_ref(v_replacement_1325_);
return v_res_1326_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1));
v___x_1333_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2);
v___x_1336_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1));
v___x_1337_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___x_1335_);
lean_ctor_set(v___x_1337_, 2, v___x_1334_);
lean_ctor_set(v___x_1337_, 3, v___x_1334_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(lean_object* v_s_1338_, lean_object* v_replacement_1339_){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1341_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1342_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1338_, v_replacement_1339_, v___x_1341_, v___x_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___boxed(lean_object* v_s_1343_, lean_object* v_replacement_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1343_, v_replacement_1344_);
lean_dec_ref(v_replacement_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object* v_s_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1350_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0));
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = lean_string_utf8_byte_size(v_s_1349_);
v___x_1353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1353_, 0, v_s_1349_);
lean_ctor_set(v___x_1353_, 1, v___x_1351_);
lean_ctor_set(v___x_1353_, 2, v___x_1352_);
v___x_1354_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1353_, v___x_1350_);
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1));
v___x_1356_ = lean_string_utf8_byte_size(v___x_1354_);
v___x_1357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1354_);
lean_ctor_set(v___x_1357_, 1, v___x_1351_);
lean_ctor_set(v___x_1357_, 2, v___x_1356_);
v___x_1358_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v___x_1357_, v___x_1355_);
v___x_1359_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2));
v___x_1360_ = lean_string_utf8_byte_size(v___x_1358_);
v___x_1361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1358_);
lean_ctor_set(v___x_1361_, 1, v___x_1351_);
lean_ctor_set(v___x_1361_, 2, v___x_1360_);
v___x_1362_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v___x_1361_, v___x_1359_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(lean_object* v_s_1363_, lean_object* v_pattern_1364_, lean_object* v_replacement_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1363_, v_replacement_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___boxed(lean_object* v_s_1367_, lean_object* v_pattern_1368_, lean_object* v_replacement_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(v_s_1367_, v_pattern_1368_, v_replacement_1369_);
lean_dec_ref(v_replacement_1369_);
lean_dec_ref(v_pattern_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(lean_object* v_s_1371_, lean_object* v_pattern_1372_, lean_object* v_replacement_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1371_, v_replacement_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___boxed(lean_object* v_s_1375_, lean_object* v_pattern_1376_, lean_object* v_replacement_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(v_s_1375_, v_pattern_1376_, v_replacement_1377_);
lean_dec_ref(v_replacement_1377_);
lean_dec_ref(v_pattern_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(lean_object* v_s_1379_, lean_object* v_pattern_1380_, lean_object* v_replacement_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1379_, v_replacement_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___boxed(lean_object* v_s_1383_, lean_object* v_pattern_1384_, lean_object* v_replacement_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(v_s_1383_, v_pattern_1384_, v_replacement_1385_);
lean_dec_ref(v_replacement_1385_);
lean_dec_ref(v_pattern_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(lean_object* v_s_1387_, lean_object* v_replacement_1388_, lean_object* v_inst_1389_, lean_object* v_R_1390_, lean_object* v_a_1391_, lean_object* v_b_1392_, lean_object* v_c_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1387_, v_replacement_1388_, v_a_1391_, v_b_1392_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___boxed(lean_object* v_s_1395_, lean_object* v_replacement_1396_, lean_object* v_inst_1397_, lean_object* v_R_1398_, lean_object* v_a_1399_, lean_object* v_b_1400_, lean_object* v_c_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(v_s_1395_, v_replacement_1396_, v_inst_1397_, v_R_1398_, v_a_1399_, v_b_1400_, v_c_1401_);
lean_dec_ref(v_replacement_1396_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object* v_s_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1404_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_string_utf8_byte_size(v_s_1403_);
v___x_1407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1407_, 0, v_s_1403_);
lean_ctor_set(v___x_1407_, 1, v___x_1405_);
lean_ctor_set(v___x_1407_, 2, v___x_1406_);
v___x_1408_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1407_, v___x_1404_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg(){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___closed__0));
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___boxed(lean_object* v___dummy_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
return v_res_1414_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object* v_s_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object* v_s_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v_s_1418_);
lean_dec_ref(v_s_1418_);
return v_res_1419_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0));
v___x_1425_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1424_);
return v___x_1425_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1428_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0));
v___x_1429_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v___x_1427_);
lean_ctor_set(v___x_1429_, 2, v___x_1426_);
lean_ctor_set(v___x_1429_, 3, v___x_1426_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object* v_s_1430_, lean_object* v_replacement_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1433_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2);
v___x_1434_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1430_, v_replacement_1431_, v___x_1433_, v___x_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object* v_s_1435_, lean_object* v_replacement_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1435_, v_replacement_1436_);
lean_dec_ref(v_replacement_1436_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object* v_s_1438_, lean_object* v___x_1439_, lean_object* v___x_1440_, lean_object* v_a_1441_, lean_object* v_b_1442_){
_start:
{
lean_object* v_it_1444_; lean_object* v_startInclusive_1445_; lean_object* v_endExclusive_1446_; 
if (lean_obj_tag(v_a_1441_) == 0)
{
lean_object* v_currPos_1454_; lean_object* v_searcher_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1483_; 
v_currPos_1454_ = lean_ctor_get(v_a_1441_, 0);
v_searcher_1455_ = lean_ctor_get(v_a_1441_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_a_1441_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1457_ = v_a_1441_;
v_isShared_1458_ = v_isSharedCheck_1483_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_searcher_1455_);
lean_inc(v_currPos_1454_);
lean_dec(v_a_1441_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1483_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
uint8_t v_decide_1469_; 
v_decide_1469_ = lean_nat_dec_eq(v_searcher_1455_, v___x_1440_);
if (v_decide_1469_ == 0)
{
uint32_t v___x_1470_; uint32_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1470_ = lean_string_utf8_get_fast(v_s_1438_, v_searcher_1455_);
v___x_1471_ = 32;
v___x_1472_ = lean_uint32_dec_eq(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
uint32_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = 9;
v___x_1474_ = lean_uint32_dec_eq(v___x_1470_, v___x_1473_);
if (v___x_1474_ == 0)
{
uint32_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = 13;
v___x_1476_ = lean_uint32_dec_eq(v___x_1470_, v___x_1475_);
if (v___x_1476_ == 0)
{
uint32_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = 10;
v___x_1478_ = lean_uint32_dec_eq(v___x_1470_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_del_object(v___x_1457_);
v___x_1479_ = lean_string_utf8_next_fast(v_s_1438_, v_searcher_1455_);
lean_dec(v_searcher_1455_);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v_currPos_1454_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v_a_1441_ = v___x_1480_;
goto _start;
}
else
{
goto v___jp_1459_;
}
}
else
{
goto v___jp_1459_;
}
}
else
{
goto v___jp_1459_;
}
}
else
{
goto v___jp_1459_;
}
}
else
{
lean_object* v___x_1482_; 
lean_del_object(v___x_1457_);
lean_dec(v_searcher_1455_);
v___x_1482_ = lean_box(1);
lean_inc(v___x_1440_);
v_it_1444_ = v___x_1482_;
v_startInclusive_1445_ = v_currPos_1454_;
v_endExclusive_1446_ = v___x_1440_;
goto v___jp_1443_;
}
v___jp_1459_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_slice_1463_; lean_object* v_nextIt_1465_; 
v___x_1460_ = lean_string_utf8_next_fast(v_s_1438_, v_searcher_1455_);
v___x_1461_ = lean_nat_sub(v___x_1460_, v_searcher_1455_);
v___x_1462_ = lean_nat_add(v_searcher_1455_, v___x_1461_);
lean_dec(v___x_1461_);
v_slice_1463_ = l_String_Slice_subslice_x21(v___x_1439_, v_currPos_1454_, v_searcher_1455_);
lean_inc(v___x_1462_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 1, v___x_1462_);
lean_ctor_set(v___x_1457_, 0, v___x_1462_);
v_nextIt_1465_ = v___x_1457_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v___x_1462_);
v_nextIt_1465_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v_startInclusive_1466_; lean_object* v_endExclusive_1467_; 
v_startInclusive_1466_ = lean_ctor_get(v_slice_1463_, 0);
lean_inc(v_startInclusive_1466_);
v_endExclusive_1467_ = lean_ctor_get(v_slice_1463_, 1);
lean_inc(v_endExclusive_1467_);
lean_dec_ref(v_slice_1463_);
v_it_1444_ = v_nextIt_1465_;
v_startInclusive_1445_ = v_startInclusive_1466_;
v_endExclusive_1446_ = v_endExclusive_1467_;
goto v___jp_1443_;
}
}
}
}
else
{
lean_dec(v___x_1440_);
lean_dec_ref(v_s_1438_);
return v_b_1442_;
}
v___jp_1443_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1447_ = lean_nat_sub(v_endExclusive_1446_, v_startInclusive_1445_);
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = lean_nat_dec_eq(v___x_1447_, v___x_1448_);
lean_dec(v___x_1447_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_inc_ref(v_s_1438_);
v___x_1450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1450_, 0, v_s_1438_);
lean_ctor_set(v___x_1450_, 1, v_startInclusive_1445_);
lean_ctor_set(v___x_1450_, 2, v_endExclusive_1446_);
v___x_1451_ = lean_array_push(v_b_1442_, v___x_1450_);
v_a_1441_ = v_it_1444_;
v_b_1442_ = v___x_1451_;
goto _start;
}
else
{
lean_dec(v_endExclusive_1446_);
lean_dec(v_startInclusive_1445_);
v_a_1441_ = v_it_1444_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object* v_s_1484_, lean_object* v___x_1485_, lean_object* v___x_1486_, lean_object* v_a_1487_, lean_object* v_b_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1484_, v___x_1485_, v___x_1486_, v_a_1487_, v_b_1488_);
lean_dec_ref(v___x_1485_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t v_mode_1496_, lean_object* v_s_1497_){
_start:
{
switch(v_mode_1496_)
{
case 0:
{
return v_s_1497_;
}
case 1:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1498_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = lean_string_utf8_byte_size(v_s_1497_);
v___x_1501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1501_, 0, v_s_1497_);
lean_ctor_set(v___x_1501_, 1, v___x_1499_);
lean_ctor_set(v___x_1501_, 2, v___x_1500_);
v___x_1502_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v___x_1501_, v___x_1498_);
return v___x_1502_;
}
default: 
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0));
v___x_1505_ = lean_string_utf8_byte_size(v_s_1497_);
lean_inc_ref(v_s_1497_);
v___x_1506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1506_, 0, v_s_1497_);
lean_ctor_set(v___x_1506_, 1, v___x_1503_);
lean_ctor_set(v___x_1506_, 2, v___x_1505_);
v___x_1507_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0);
v___x_1508_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1));
v___x_1509_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1497_, v___x_1506_, v___x_1505_, v___x_1507_, v___x_1508_);
lean_dec_ref_known(v___x_1506_, 3);
v___x_1510_ = lean_array_to_list(v___x_1509_);
v___x_1511_ = l_String_Slice_intercalate(v___x_1504_, v___x_1510_);
lean_dec(v___x_1510_);
return v___x_1511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object* v_mode_1512_, lean_object* v_s_1513_){
_start:
{
uint8_t v_mode_boxed_1514_; lean_object* v_res_1515_; 
v_mode_boxed_1514_ = lean_unbox(v_mode_1512_);
v_res_1515_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v_mode_boxed_1514_, v_s_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object* v_s_1516_, lean_object* v_pattern_1517_, lean_object* v_replacement_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1516_, v_replacement_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object* v_s_1520_, lean_object* v_pattern_1521_, lean_object* v_replacement_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(v_s_1520_, v_pattern_1521_, v_replacement_1522_);
lean_dec_ref(v_replacement_1522_);
lean_dec_ref(v_pattern_1521_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object* v_s_1524_, lean_object* v___x_1525_, lean_object* v___x_1526_, lean_object* v_inst_1527_, lean_object* v_R_1528_, lean_object* v_a_1529_, lean_object* v_b_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1524_, v___x_1525_, v___x_1526_, v_a_1529_, v_b_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___boxed(lean_object* v_s_1532_, lean_object* v___x_1533_, lean_object* v___x_1534_, lean_object* v_inst_1535_, lean_object* v_R_1536_, lean_object* v_a_1537_, lean_object* v_b_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(v_s_1532_, v___x_1533_, v___x_1534_, v_inst_1535_, v_R_1536_, v_a_1537_, v_b_1538_);
lean_dec_ref(v___x_1533_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(lean_object* v_hi_1540_, lean_object* v_pivot_1541_, lean_object* v_as_1542_, lean_object* v_i_1543_, lean_object* v_k_1544_){
_start:
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_nat_dec_lt(v_k_1544_, v_hi_1540_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec(v_k_1544_);
v___x_1546_ = lean_array_fswap(v_as_1542_, v_i_1543_, v_hi_1540_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_i_1543_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1548_ = lean_array_fget_borrowed(v_as_1542_, v_k_1544_);
v___x_1549_ = lean_string_dec_lt(v___x_1548_, v_pivot_1541_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_add(v_k_1544_, v___x_1550_);
lean_dec(v_k_1544_);
v_k_1544_ = v___x_1551_;
goto _start;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1553_ = lean_array_fswap(v_as_1542_, v_i_1543_, v_k_1544_);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_nat_add(v_i_1543_, v___x_1554_);
lean_dec(v_i_1543_);
v___x_1556_ = lean_nat_add(v_k_1544_, v___x_1554_);
lean_dec(v_k_1544_);
v_as_1542_ = v___x_1553_;
v_i_1543_ = v___x_1555_;
v_k_1544_ = v___x_1556_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg___boxed(lean_object* v_hi_1558_, lean_object* v_pivot_1559_, lean_object* v_as_1560_, lean_object* v_i_1561_, lean_object* v_k_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1558_, v_pivot_1559_, v_as_1560_, v_i_1561_, v_k_1562_);
lean_dec_ref(v_pivot_1559_);
lean_dec(v_hi_1558_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object* v_n_1564_, lean_object* v_as_1565_, lean_object* v_lo_1566_, lean_object* v_hi_1567_){
_start:
{
lean_object* v___y_1569_; uint8_t v___x_1579_; 
v___x_1579_ = lean_nat_dec_lt(v_lo_1566_, v_hi_1567_);
if (v___x_1579_ == 0)
{
lean_dec(v_lo_1566_);
return v_as_1565_;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_mid_1582_; lean_object* v___y_1584_; lean_object* v___y_1590_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1580_ = lean_nat_add(v_lo_1566_, v_hi_1567_);
v___x_1581_ = lean_unsigned_to_nat(1u);
v_mid_1582_ = lean_nat_shiftr(v___x_1580_, v___x_1581_);
lean_dec(v___x_1580_);
v___x_1595_ = lean_array_fget_borrowed(v_as_1565_, v_mid_1582_);
v___x_1596_ = lean_array_fget_borrowed(v_as_1565_, v_lo_1566_);
v___x_1597_ = lean_string_dec_lt(v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
v___y_1590_ = v_as_1565_;
goto v___jp_1589_;
}
else
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_array_fswap(v_as_1565_, v_lo_1566_, v_mid_1582_);
v___y_1590_ = v___x_1598_;
goto v___jp_1589_;
}
v___jp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = lean_array_fget_borrowed(v___y_1584_, v_mid_1582_);
v___x_1586_ = lean_array_fget_borrowed(v___y_1584_, v_hi_1567_);
v___x_1587_ = lean_string_dec_lt(v___x_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_dec(v_mid_1582_);
v___y_1569_ = v___y_1584_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_array_fswap(v___y_1584_, v_mid_1582_, v_hi_1567_);
lean_dec(v_mid_1582_);
v___y_1569_ = v___x_1588_;
goto v___jp_1568_;
}
}
v___jp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1591_ = lean_array_fget_borrowed(v___y_1590_, v_hi_1567_);
v___x_1592_ = lean_array_fget_borrowed(v___y_1590_, v_lo_1566_);
v___x_1593_ = lean_string_dec_lt(v___x_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
v___y_1584_ = v___y_1590_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_array_fswap(v___y_1590_, v_lo_1566_, v_hi_1567_);
v___y_1584_ = v___x_1594_;
goto v___jp_1583_;
}
}
}
v___jp_1568_:
{
lean_object* v_pivot_1570_; lean_object* v___x_1571_; lean_object* v_fst_1572_; lean_object* v_snd_1573_; uint8_t v___x_1574_; 
v_pivot_1570_ = lean_array_fget(v___y_1569_, v_hi_1567_);
lean_inc_n(v_lo_1566_, 2);
v___x_1571_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1567_, v_pivot_1570_, v___y_1569_, v_lo_1566_, v_lo_1566_);
lean_dec(v_pivot_1570_);
v_fst_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_fst_1572_);
v_snd_1573_ = lean_ctor_get(v___x_1571_, 1);
lean_inc(v_snd_1573_);
lean_dec_ref(v___x_1571_);
v___x_1574_ = lean_nat_dec_le(v_hi_1567_, v_fst_1572_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1564_, v_snd_1573_, v_lo_1566_, v_fst_1572_);
v___x_1576_ = lean_unsigned_to_nat(1u);
v___x_1577_ = lean_nat_add(v_fst_1572_, v___x_1576_);
lean_dec(v_fst_1572_);
v_as_1565_ = v___x_1575_;
v_lo_1566_ = v___x_1577_;
goto _start;
}
else
{
lean_dec(v_fst_1572_);
lean_dec(v_lo_1566_);
return v_snd_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object* v_n_1599_, lean_object* v_as_1600_, lean_object* v_lo_1601_, lean_object* v_hi_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1599_, v_as_1600_, v_lo_1601_, v_hi_1602_);
lean_dec(v_hi_1602_);
lean_dec(v_n_1599_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t v_mode_1604_, lean_object* v_msgs_1605_){
_start:
{
if (v_mode_1604_ == 0)
{
return v_msgs_1605_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1606_ = lean_array_mk(v_msgs_1605_);
v___x_1607_ = lean_array_get_size(v___x_1606_);
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = lean_nat_dec_eq(v___x_1607_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___y_1618_; uint8_t v___x_1620_; 
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_nat_sub(v___x_1607_, v___x_1615_);
v___x_1620_ = lean_nat_dec_le(v___x_1613_, v___x_1616_);
if (v___x_1620_ == 0)
{
lean_inc(v___x_1616_);
v___y_1618_ = v___x_1616_;
goto v___jp_1617_;
}
else
{
v___y_1618_ = v___x_1613_;
goto v___jp_1617_;
}
v___jp_1617_:
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_nat_dec_le(v___y_1618_, v___x_1616_);
if (v___x_1619_ == 0)
{
lean_dec(v___x_1616_);
lean_inc(v___y_1618_);
v___y_1609_ = v___y_1618_;
v___y_1610_ = v___y_1618_;
goto v___jp_1608_;
}
else
{
v___y_1609_ = v___y_1618_;
v___y_1610_ = v___x_1616_;
goto v___jp_1608_;
}
}
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_array_to_list(v___x_1606_);
return v___x_1621_;
}
v___jp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v___x_1607_, v___x_1606_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
v___x_1612_ = lean_array_to_list(v___x_1611_);
return v___x_1612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* v_mode_1622_, lean_object* v_msgs_1623_){
_start:
{
uint8_t v_mode_boxed_1624_; lean_object* v_res_1625_; 
v_mode_boxed_1624_ = lean_unbox(v_mode_1622_);
v_res_1625_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_boxed_1624_, v_msgs_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object* v_n_1626_, lean_object* v_as_1627_, lean_object* v_lo_1628_, lean_object* v_hi_1629_, lean_object* v_w_1630_, lean_object* v_hlo_1631_, lean_object* v_hhi_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1626_, v_as_1627_, v_lo_1628_, v_hi_1629_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object* v_n_1634_, lean_object* v_as_1635_, lean_object* v_lo_1636_, lean_object* v_hi_1637_, lean_object* v_w_1638_, lean_object* v_hlo_1639_, lean_object* v_hhi_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(v_n_1634_, v_as_1635_, v_lo_1636_, v_hi_1637_, v_w_1638_, v_hlo_1639_, v_hhi_1640_);
lean_dec(v_hi_1637_);
lean_dec(v_n_1634_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(lean_object* v_n_1642_, lean_object* v_lo_1643_, lean_object* v_hi_1644_, lean_object* v_hhi_1645_, lean_object* v_pivot_1646_, lean_object* v_as_1647_, lean_object* v_i_1648_, lean_object* v_k_1649_, lean_object* v_ilo_1650_, lean_object* v_ik_1651_, lean_object* v_w_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1644_, v_pivot_1646_, v_as_1647_, v_i_1648_, v_k_1649_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___boxed(lean_object* v_n_1654_, lean_object* v_lo_1655_, lean_object* v_hi_1656_, lean_object* v_hhi_1657_, lean_object* v_pivot_1658_, lean_object* v_as_1659_, lean_object* v_i_1660_, lean_object* v_k_1661_, lean_object* v_ilo_1662_, lean_object* v_ik_1663_, lean_object* v_w_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(v_n_1654_, v_lo_1655_, v_hi_1656_, v_hhi_1657_, v_pivot_1658_, v_as_1659_, v_i_1660_, v_k_1661_, v_ilo_1662_, v_ik_1663_, v_w_1664_);
lean_dec_ref(v_pivot_1658_);
lean_dec(v_hi_1656_);
lean_dec(v_lo_1655_);
lean_dec(v_n_1654_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object* v_as_1666_, size_t v_i_1667_, size_t v_stop_1668_, lean_object* v_b_1669_){
_start:
{
uint8_t v___x_1670_; 
v___x_1670_ = lean_usize_dec_eq(v_i_1667_, v_stop_1668_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v_diagnostics_1672_; lean_object* v_msgLog_1673_; lean_object* v___x_1674_; size_t v___x_1675_; size_t v___x_1676_; 
v___x_1671_ = lean_array_uget_borrowed(v_as_1666_, v_i_1667_);
v_diagnostics_1672_ = lean_ctor_get(v___x_1671_, 1);
v_msgLog_1673_ = lean_ctor_get(v_diagnostics_1672_, 0);
lean_inc_ref(v_msgLog_1673_);
v___x_1674_ = l_Lean_MessageLog_append(v_b_1669_, v_msgLog_1673_);
v___x_1675_ = ((size_t)1ULL);
v___x_1676_ = lean_usize_add(v_i_1667_, v___x_1675_);
v_i_1667_ = v___x_1676_;
v_b_1669_ = v___x_1674_;
goto _start;
}
else
{
return v_b_1669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0___boxed(lean_object* v_as_1678_, lean_object* v_i_1679_, lean_object* v_stop_1680_, lean_object* v_b_1681_){
_start:
{
size_t v_i_boxed_1682_; size_t v_stop_boxed_1683_; lean_object* v_res_1684_; 
v_i_boxed_1682_ = lean_unbox_usize(v_i_1679_);
lean_dec(v_i_1679_);
v_stop_boxed_1683_ = lean_unbox_usize(v_stop_1680_);
lean_dec(v_stop_1680_);
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v_as_1678_, v_i_boxed_1682_, v_stop_boxed_1683_, v_b_1681_);
lean_dec_ref(v_as_1678_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object* v_as_1685_, size_t v_i_1686_, size_t v_stop_1687_, lean_object* v_b_1688_){
_start:
{
lean_object* v___y_1690_; uint8_t v___x_1694_; 
v___x_1694_ = lean_usize_dec_eq(v_i_1686_, v_stop_1687_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1695_ = lean_array_uget_borrowed(v_as_1685_, v_i_1686_);
v___x_1696_ = l_Lean_MessageLog_empty;
lean_inc(v___x_1695_);
v___x_1697_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1695_);
v___x_1698_ = l_Lean_Language_SnapshotTree_getAll(v___x_1697_);
v___x_1699_ = lean_unsigned_to_nat(0u);
v___x_1700_ = lean_array_get_size(v___x_1698_);
v___x_1701_ = lean_nat_dec_lt(v___x_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
lean_dec_ref(v___x_1698_);
v___x_1702_ = l_Lean_MessageLog_append(v_b_1688_, v___x_1696_);
v___y_1690_ = v___x_1702_;
goto v___jp_1689_;
}
else
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_nat_dec_le(v___x_1700_, v___x_1700_);
if (v___x_1703_ == 0)
{
if (v___x_1701_ == 0)
{
lean_object* v___x_1704_; 
lean_dec_ref(v___x_1698_);
v___x_1704_ = l_Lean_MessageLog_append(v_b_1688_, v___x_1696_);
v___y_1690_ = v___x_1704_;
goto v___jp_1689_;
}
else
{
size_t v___x_1705_; size_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = lean_usize_of_nat(v___x_1700_);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1698_, v___x_1705_, v___x_1706_, v___x_1696_);
lean_dec_ref(v___x_1698_);
v___x_1708_ = l_Lean_MessageLog_append(v_b_1688_, v___x_1707_);
v___y_1690_ = v___x_1708_;
goto v___jp_1689_;
}
}
else
{
size_t v___x_1709_; size_t v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1709_ = ((size_t)0ULL);
v___x_1710_ = lean_usize_of_nat(v___x_1700_);
v___x_1711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1698_, v___x_1709_, v___x_1710_, v___x_1696_);
lean_dec_ref(v___x_1698_);
v___x_1712_ = l_Lean_MessageLog_append(v_b_1688_, v___x_1711_);
v___y_1690_ = v___x_1712_;
goto v___jp_1689_;
}
}
}
else
{
return v_b_1688_;
}
v___jp_1689_:
{
size_t v___x_1691_; size_t v___x_1692_; 
v___x_1691_ = ((size_t)1ULL);
v___x_1692_ = lean_usize_add(v_i_1686_, v___x_1691_);
v_i_1686_ = v___x_1692_;
v_b_1688_ = v___y_1690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1___boxed(lean_object* v_as_1713_, lean_object* v_i_1714_, lean_object* v_stop_1715_, lean_object* v_b_1716_){
_start:
{
size_t v_i_boxed_1717_; size_t v_stop_boxed_1718_; lean_object* v_res_1719_; 
v_i_boxed_1717_ = lean_unbox_usize(v_i_1714_);
lean_dec(v_i_1714_);
v_stop_boxed_1718_ = lean_unbox_usize(v_stop_1715_);
lean_dec(v_stop_1715_);
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_as_1713_, v_i_boxed_1717_, v_stop_boxed_1718_, v_b_1716_);
lean_dec_ref(v_as_1713_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object* v_cmd_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_fileName_1726_; lean_object* v_fileMap_1727_; lean_object* v_currRecDepth_1728_; lean_object* v_cmdPos_1729_; lean_object* v_macroStack_1730_; lean_object* v_quotContext_x3f_1731_; lean_object* v_currMacroScope_1732_; lean_object* v_ref_1733_; lean_object* v_cancelTk_x3f_1734_; uint8_t v_suppressElabErrors_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v_fileName_1726_ = lean_ctor_get(v_a_1723_, 0);
v_fileMap_1727_ = lean_ctor_get(v_a_1723_, 1);
v_currRecDepth_1728_ = lean_ctor_get(v_a_1723_, 2);
v_cmdPos_1729_ = lean_ctor_get(v_a_1723_, 3);
v_macroStack_1730_ = lean_ctor_get(v_a_1723_, 4);
v_quotContext_x3f_1731_ = lean_ctor_get(v_a_1723_, 5);
v_currMacroScope_1732_ = lean_ctor_get(v_a_1723_, 6);
v_ref_1733_ = lean_ctor_get(v_a_1723_, 7);
v_cancelTk_x3f_1734_ = lean_ctor_get(v_a_1723_, 9);
v_suppressElabErrors_1735_ = lean_ctor_get_uint8(v_a_1723_, sizeof(void*)*10);
v___x_1736_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1734_);
lean_inc(v_ref_1733_);
lean_inc(v_currMacroScope_1732_);
lean_inc(v_quotContext_x3f_1731_);
lean_inc(v_macroStack_1730_);
lean_inc(v_cmdPos_1729_);
lean_inc(v_currRecDepth_1728_);
lean_inc_ref(v_fileMap_1727_);
lean_inc_ref(v_fileName_1726_);
v___x_1737_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1737_, 0, v_fileName_1726_);
lean_ctor_set(v___x_1737_, 1, v_fileMap_1727_);
lean_ctor_set(v___x_1737_, 2, v_currRecDepth_1728_);
lean_ctor_set(v___x_1737_, 3, v_cmdPos_1729_);
lean_ctor_set(v___x_1737_, 4, v_macroStack_1730_);
lean_ctor_set(v___x_1737_, 5, v_quotContext_x3f_1731_);
lean_ctor_set(v___x_1737_, 6, v_currMacroScope_1732_);
lean_ctor_set(v___x_1737_, 7, v_ref_1733_);
lean_ctor_set(v___x_1737_, 8, v___x_1736_);
lean_ctor_set(v___x_1737_, 9, v_cancelTk_x3f_1734_);
lean_ctor_set_uint8(v___x_1737_, sizeof(void*)*10, v_suppressElabErrors_1735_);
v___x_1738_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1722_, v___x_1737_, v_a_1724_);
lean_dec_ref_known(v___x_1737_, 10);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1786_; 
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v___x_1738_, 0);
lean_dec(v_unused_1787_);
v___x_1740_ = v___x_1738_;
v_isShared_1741_ = v_isSharedCheck_1786_;
goto v_resetjp_1739_;
}
else
{
lean_dec(v___x_1738_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1786_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v_messages_1744_; lean_object* v___y_1746_; lean_object* v_snapshotTasks_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1742_ = lean_st_ref_get(v_a_1724_);
v___x_1743_ = lean_st_ref_get(v_a_1724_);
v_messages_1744_ = lean_ctor_get(v___x_1742_, 1);
lean_inc_ref(v_messages_1744_);
lean_dec(v___x_1742_);
v_snapshotTasks_1774_ = lean_ctor_get(v___x_1743_, 10);
lean_inc_ref(v_snapshotTasks_1774_);
lean_dec(v___x_1743_);
v___x_1775_ = l_Lean_MessageLog_empty;
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = lean_array_get_size(v_snapshotTasks_1774_);
v___x_1778_ = lean_nat_dec_lt(v___x_1776_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_dec_ref(v_snapshotTasks_1774_);
v___y_1746_ = v___x_1775_;
goto v___jp_1745_;
}
else
{
uint8_t v___x_1779_; 
v___x_1779_ = lean_nat_dec_le(v___x_1777_, v___x_1777_);
if (v___x_1779_ == 0)
{
if (v___x_1778_ == 0)
{
lean_dec_ref(v_snapshotTasks_1774_);
v___y_1746_ = v___x_1775_;
goto v___jp_1745_;
}
else
{
size_t v___x_1780_; size_t v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = ((size_t)0ULL);
v___x_1781_ = lean_usize_of_nat(v___x_1777_);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1774_, v___x_1780_, v___x_1781_, v___x_1775_);
lean_dec_ref(v_snapshotTasks_1774_);
v___y_1746_ = v___x_1782_;
goto v___jp_1745_;
}
}
else
{
size_t v___x_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = ((size_t)0ULL);
v___x_1784_ = lean_usize_of_nat(v___x_1777_);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1774_, v___x_1783_, v___x_1784_, v___x_1775_);
lean_dec_ref(v_snapshotTasks_1774_);
v___y_1746_ = v___x_1785_;
goto v___jp_1745_;
}
}
v___jp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v_env_1749_; lean_object* v_messages_1750_; lean_object* v_scopes_1751_; lean_object* v_usedQuotCtxts_1752_; lean_object* v_nextMacroScope_1753_; lean_object* v_maxRecDepth_1754_; lean_object* v_ngen_1755_; lean_object* v_auxDeclNGen_1756_; lean_object* v_infoState_1757_; lean_object* v_traceState_1758_; lean_object* v_prevLinterStates_1759_; lean_object* v_codeQualityEntryTasks_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1772_; 
v___x_1747_ = l_Lean_MessageLog_append(v_messages_1744_, v___y_1746_);
v___x_1748_ = lean_st_ref_take(v_a_1724_);
v_env_1749_ = lean_ctor_get(v___x_1748_, 0);
v_messages_1750_ = lean_ctor_get(v___x_1748_, 1);
v_scopes_1751_ = lean_ctor_get(v___x_1748_, 2);
v_usedQuotCtxts_1752_ = lean_ctor_get(v___x_1748_, 3);
v_nextMacroScope_1753_ = lean_ctor_get(v___x_1748_, 4);
v_maxRecDepth_1754_ = lean_ctor_get(v___x_1748_, 5);
v_ngen_1755_ = lean_ctor_get(v___x_1748_, 6);
v_auxDeclNGen_1756_ = lean_ctor_get(v___x_1748_, 7);
v_infoState_1757_ = lean_ctor_get(v___x_1748_, 8);
v_traceState_1758_ = lean_ctor_get(v___x_1748_, 9);
v_prevLinterStates_1759_ = lean_ctor_get(v___x_1748_, 11);
v_codeQualityEntryTasks_1760_ = lean_ctor_get(v___x_1748_, 12);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v___x_1748_, 10);
lean_dec(v_unused_1773_);
v___x_1762_ = v___x_1748_;
v_isShared_1763_ = v_isSharedCheck_1772_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1760_);
lean_inc(v_prevLinterStates_1759_);
lean_inc(v_traceState_1758_);
lean_inc(v_infoState_1757_);
lean_inc(v_auxDeclNGen_1756_);
lean_inc(v_ngen_1755_);
lean_inc(v_maxRecDepth_1754_);
lean_inc(v_nextMacroScope_1753_);
lean_inc(v_usedQuotCtxts_1752_);
lean_inc(v_scopes_1751_);
lean_inc(v_messages_1750_);
lean_inc(v_env_1749_);
lean_dec(v___x_1748_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1772_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1764_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 10, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_env_1749_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_messages_1750_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_scopes_1751_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_usedQuotCtxts_1752_);
lean_ctor_set(v_reuseFailAlloc_1771_, 4, v_nextMacroScope_1753_);
lean_ctor_set(v_reuseFailAlloc_1771_, 5, v_maxRecDepth_1754_);
lean_ctor_set(v_reuseFailAlloc_1771_, 6, v_ngen_1755_);
lean_ctor_set(v_reuseFailAlloc_1771_, 7, v_auxDeclNGen_1756_);
lean_ctor_set(v_reuseFailAlloc_1771_, 8, v_infoState_1757_);
lean_ctor_set(v_reuseFailAlloc_1771_, 9, v_traceState_1758_);
lean_ctor_set(v_reuseFailAlloc_1771_, 10, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1771_, 11, v_prevLinterStates_1759_);
lean_ctor_set(v_reuseFailAlloc_1771_, 12, v_codeQualityEntryTasks_1760_);
v___x_1766_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = lean_st_ref_put(v_a_1724_, v___x_1766_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1747_);
v___x_1769_ = v___x_1740_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1747_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
v_a_1788_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1738_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1738_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
return v_res_1800_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1801_, lean_object* v_opt_1802_){
_start:
{
lean_object* v_name_1803_; lean_object* v_defValue_1804_; lean_object* v_map_1805_; lean_object* v___x_1806_; 
v_name_1803_ = lean_ctor_get(v_opt_1802_, 0);
v_defValue_1804_ = lean_ctor_get(v_opt_1802_, 1);
v_map_1805_ = lean_ctor_get(v_opts_1801_, 0);
v___x_1806_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1805_, v_name_1803_);
if (lean_obj_tag(v___x_1806_) == 0)
{
uint8_t v___x_1807_; 
v___x_1807_ = lean_unbox(v_defValue_1804_);
return v___x_1807_;
}
else
{
lean_object* v_val_1808_; 
v_val_1808_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_val_1808_);
lean_dec_ref_known(v___x_1806_, 1);
if (lean_obj_tag(v_val_1808_) == 1)
{
uint8_t v_v_1809_; 
v_v_1809_ = lean_ctor_get_uint8(v_val_1808_, 0);
lean_dec_ref_known(v_val_1808_, 0);
return v_v_1809_;
}
else
{
uint8_t v___x_1810_; 
lean_dec(v_val_1808_);
v___x_1810_ = lean_unbox(v_defValue_1804_);
return v___x_1810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1811_, lean_object* v_opt_1812_){
_start:
{
uint8_t v_res_1813_; lean_object* v_r_1814_; 
v_res_1813_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1811_, v_opt_1812_);
lean_dec_ref(v_opt_1812_);
lean_dec_ref(v_opts_1811_);
v_r_1814_ = lean_box(v_res_1813_);
return v_r_1814_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg(){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___closed__0));
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___boxed(lean_object* v___dummy_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v_res_1820_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1824_);
lean_dec_ref(v_s_1824_);
return v_res_1825_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_box(1);
v___x_1827_ = l_Lean_MessageData_ofFormat(v___x_1826_);
return v___x_1827_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1832_ = l_Lean_MessageData_ofFormat(v___x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1833_, lean_object* v_x_1834_){
_start:
{
if (lean_obj_tag(v_x_1834_) == 0)
{
return v_x_1833_;
}
else
{
lean_object* v_head_1835_; lean_object* v_tail_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1858_; 
v_head_1835_ = lean_ctor_get(v_x_1834_, 0);
v_tail_1836_ = lean_ctor_get(v_x_1834_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_x_1834_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1838_ = v_x_1834_;
v_isShared_1839_ = v_isSharedCheck_1858_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_tail_1836_);
lean_inc(v_head_1835_);
lean_dec(v_x_1834_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1858_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v_before_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1856_; 
v_before_1840_ = lean_ctor_get(v_head_1835_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_head_1835_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v_head_1835_, 1);
lean_dec(v_unused_1857_);
v___x_1842_ = v_head_1835_;
v_isShared_1843_ = v_isSharedCheck_1856_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_before_1840_);
lean_dec(v_head_1835_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1856_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1844_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1843_ == 0)
{
lean_ctor_set_tag(v___x_1842_, 7);
lean_ctor_set(v___x_1842_, 1, v___x_1844_);
lean_ctor_set(v___x_1842_, 0, v_x_1833_);
v___x_1846_ = v___x_1842_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_x_1833_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1839_ == 0)
{
lean_ctor_set_tag(v___x_1838_, 7);
lean_ctor_set(v___x_1838_, 1, v___x_1847_);
lean_ctor_set(v___x_1838_, 0, v___x_1846_);
v___x_1849_ = v___x_1838_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = l_Lean_MessageData_ofSyntax(v_before_1840_);
v___x_1851_ = l_Lean_indentD(v___x_1850_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1849_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v_x_1833_ = v___x_1852_;
v_x_1834_ = v_tail_1836_;
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
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1863_ = l_Lean_MessageData_ofFormat(v___x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1864_, lean_object* v_macroStack_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v_scopes_1870_; lean_object* v___x_1871_; lean_object* v_opts_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1868_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1869_ = lean_st_ref_get(v___y_1866_);
v_scopes_1870_ = lean_ctor_get(v___x_1869_, 2);
lean_inc(v_scopes_1870_);
lean_dec(v___x_1869_);
v___x_1871_ = l_List_head_x21___redArg(v___x_1868_, v_scopes_1870_);
lean_dec(v_scopes_1870_);
v_opts_1872_ = lean_ctor_get(v___x_1871_, 1);
lean_inc_ref(v_opts_1872_);
lean_dec(v___x_1871_);
v___x_1873_ = l_Lean_Elab_pp_macroStack;
v___x_1874_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1872_, v___x_1873_);
lean_dec_ref(v_opts_1872_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; 
lean_dec(v_macroStack_1865_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v_msgData_1864_);
return v___x_1875_;
}
else
{
if (lean_obj_tag(v_macroStack_1865_) == 0)
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_msgData_1864_);
return v___x_1876_;
}
else
{
lean_object* v_head_1877_; lean_object* v_after_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1893_; 
v_head_1877_ = lean_ctor_get(v_macroStack_1865_, 0);
lean_inc(v_head_1877_);
v_after_1878_ = lean_ctor_get(v_head_1877_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_head_1877_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v_head_1877_, 0);
lean_dec(v_unused_1894_);
v___x_1880_ = v_head_1877_;
v_isShared_1881_ = v_isSharedCheck_1893_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_after_1878_);
lean_dec(v_head_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1893_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1881_ == 0)
{
lean_ctor_set_tag(v___x_1880_, 7);
lean_ctor_set(v___x_1880_, 1, v___x_1882_);
lean_ctor_set(v___x_1880_, 0, v_msgData_1864_);
v___x_1884_ = v___x_1880_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_msgData_1864_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v_msgData_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1885_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = l_Lean_MessageData_ofSyntax(v_after_1878_);
v___x_1888_ = l_Lean_indentD(v___x_1887_);
v_msgData_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1889_, 0, v___x_1886_);
lean_ctor_set(v_msgData_1889_, 1, v___x_1888_);
v___x_1890_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1889_, v_macroStack_1865_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1895_, lean_object* v_macroStack_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1895_, v_macroStack_1896_, v___y_1897_);
lean_dec(v___y_1897_);
return v_res_1899_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1903_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1904_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
lean_ctor_set(v___x_1906_, 2, v___x_1905_);
lean_ctor_set(v___x_1906_, 3, v___x_1905_);
lean_ctor_set(v___x_1906_, 4, v___x_1904_);
lean_ctor_set(v___x_1906_, 5, v___x_1904_);
lean_ctor_set(v___x_1906_, 6, v___x_1904_);
lean_ctor_set(v___x_1906_, 7, v___x_1904_);
lean_ctor_set(v___x_1906_, 8, v___x_1904_);
lean_ctor_set(v___x_1906_, 9, v___x_1904_);
lean_ctor_set(v___x_1906_, 10, v___x_1904_);
lean_ctor_set(v___x_1906_, 11, v___x_1903_);
return v___x_1906_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = lean_unsigned_to_nat(32u);
v___x_1908_ = lean_mk_empty_array_with_capacity(v___x_1907_);
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1910_ = ((size_t)5ULL);
v___x_1911_ = lean_unsigned_to_nat(0u);
v___x_1912_ = lean_unsigned_to_nat(32u);
v___x_1913_ = lean_mk_empty_array_with_capacity(v___x_1912_);
v___x_1914_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1915_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v___x_1913_);
lean_ctor_set(v___x_1915_, 2, v___x_1911_);
lean_ctor_set(v___x_1915_, 3, v___x_1911_);
lean_ctor_set_usize(v___x_1915_, 4, v___x_1910_);
return v___x_1915_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1916_ = lean_box(1);
v___x_1917_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1918_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1917_);
lean_ctor_set(v___x_1919_, 2, v___x_1916_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; lean_object* v_env_1924_; uint8_t v___x_1925_; lean_object* v_env_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v_scopes_1929_; lean_object* v___x_1930_; lean_object* v_opts_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1923_ = lean_st_ref_get(v___y_1921_);
v_env_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc_ref(v_env_1924_);
lean_dec(v___x_1923_);
v___x_1925_ = 0;
v_env_1926_ = l_Lean_Environment_setRecordingDeps(v_env_1924_, v___x_1925_);
v___x_1927_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1928_ = lean_st_ref_get(v___y_1921_);
v_scopes_1929_ = lean_ctor_get(v___x_1928_, 2);
lean_inc(v_scopes_1929_);
lean_dec(v___x_1928_);
v___x_1930_ = l_List_head_x21___redArg(v___x_1927_, v_scopes_1929_);
lean_dec(v_scopes_1929_);
v_opts_1931_ = lean_ctor_get(v___x_1930_, 1);
lean_inc_ref(v_opts_1931_);
lean_dec(v___x_1930_);
v___x_1932_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1933_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1934_, 0, v_env_1926_);
lean_ctor_set(v___x_1934_, 1, v___x_1932_);
lean_ctor_set(v___x_1934_, 2, v___x_1933_);
lean_ctor_set(v___x_1934_, 3, v_opts_1931_);
v___x_1935_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v_msgData_1920_);
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1937_, v___y_1938_);
lean_dec(v___y_1938_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_Elab_Command_getRef___redArg(v___y_1942_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v_macroStack_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v_a_1950_; lean_object* v___x_1951_; lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1960_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1945_, 1);
v_macroStack_1947_ = lean_ctor_get(v___y_1942_, 4);
v___x_1948_ = l_Lean_Elab_getBetterRef(v_a_1946_, v_macroStack_1947_);
lean_dec(v_a_1946_);
v___x_1949_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1941_, v___y_1943_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
lean_inc(v_macroStack_1947_);
v___x_1951_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1950_, v_macroStack_1947_, v___y_1943_);
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1948_);
lean_ctor_set(v___x_1956_, 1, v_a_1952_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 1);
lean_ctor_set(v___x_1954_, 0, v___x_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_msg_1941_);
v_a_1961_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1945_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1945_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_1974_, lean_object* v_msg_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_Elab_Command_getRef___redArg(v___y_1976_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v_fileName_1981_; lean_object* v_fileMap_1982_; lean_object* v_currRecDepth_1983_; lean_object* v_cmdPos_1984_; lean_object* v_macroStack_1985_; lean_object* v_quotContext_x3f_1986_; lean_object* v_currMacroScope_1987_; lean_object* v_snap_x3f_1988_; lean_object* v_cancelTk_x3f_1989_; uint8_t v_suppressElabErrors_1990_; lean_object* v_ref_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v_fileName_1981_ = lean_ctor_get(v___y_1976_, 0);
v_fileMap_1982_ = lean_ctor_get(v___y_1976_, 1);
v_currRecDepth_1983_ = lean_ctor_get(v___y_1976_, 2);
v_cmdPos_1984_ = lean_ctor_get(v___y_1976_, 3);
v_macroStack_1985_ = lean_ctor_get(v___y_1976_, 4);
v_quotContext_x3f_1986_ = lean_ctor_get(v___y_1976_, 5);
v_currMacroScope_1987_ = lean_ctor_get(v___y_1976_, 6);
v_snap_x3f_1988_ = lean_ctor_get(v___y_1976_, 8);
v_cancelTk_x3f_1989_ = lean_ctor_get(v___y_1976_, 9);
v_suppressElabErrors_1990_ = lean_ctor_get_uint8(v___y_1976_, sizeof(void*)*10);
v_ref_1991_ = l_Lean_replaceRef(v_ref_1974_, v_a_1980_);
lean_dec(v_a_1980_);
lean_inc(v_cancelTk_x3f_1989_);
lean_inc(v_snap_x3f_1988_);
lean_inc(v_currMacroScope_1987_);
lean_inc(v_quotContext_x3f_1986_);
lean_inc(v_macroStack_1985_);
lean_inc(v_cmdPos_1984_);
lean_inc(v_currRecDepth_1983_);
lean_inc_ref(v_fileMap_1982_);
lean_inc_ref(v_fileName_1981_);
v___x_1992_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1992_, 0, v_fileName_1981_);
lean_ctor_set(v___x_1992_, 1, v_fileMap_1982_);
lean_ctor_set(v___x_1992_, 2, v_currRecDepth_1983_);
lean_ctor_set(v___x_1992_, 3, v_cmdPos_1984_);
lean_ctor_set(v___x_1992_, 4, v_macroStack_1985_);
lean_ctor_set(v___x_1992_, 5, v_quotContext_x3f_1986_);
lean_ctor_set(v___x_1992_, 6, v_currMacroScope_1987_);
lean_ctor_set(v___x_1992_, 7, v_ref_1991_);
lean_ctor_set(v___x_1992_, 8, v_snap_x3f_1988_);
lean_ctor_set(v___x_1992_, 9, v_cancelTk_x3f_1989_);
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*10, v_suppressElabErrors_1990_);
v___x_1993_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1975_, v___x_1992_, v___y_1977_);
lean_dec_ref_known(v___x_1992_, 10);
return v___x_1993_;
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_msg_1975_);
v_a_1994_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1979_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1979_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_2002_, lean_object* v_msg_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_2002_, v_msg_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v_ref_2002_);
return v_res_2007_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = l_Lean_Syntax_getArg(v_stx_2014_, v___x_2024_);
if (lean_obj_tag(v___x_2025_) == 1)
{
lean_object* v_kind_2026_; 
v_kind_2026_ = lean_ctor_get(v___x_2025_, 1);
lean_inc(v_kind_2026_);
if (lean_obj_tag(v_kind_2026_) == 1)
{
lean_object* v_pre_2027_; 
v_pre_2027_ = lean_ctor_get(v_kind_2026_, 0);
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
lean_inc(v_pre_2029_);
if (lean_obj_tag(v_pre_2029_) == 1)
{
lean_object* v_pre_2030_; 
v_pre_2030_ = lean_ctor_get(v_pre_2029_, 0);
if (lean_obj_tag(v_pre_2030_) == 0)
{
lean_object* v_args_2031_; lean_object* v_str_2032_; lean_object* v_str_2033_; lean_object* v_str_2034_; lean_object* v_str_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v_args_2031_ = lean_ctor_get(v___x_2025_, 2);
lean_inc_ref(v_args_2031_);
lean_dec_ref_known(v___x_2025_, 3);
v_str_2032_ = lean_ctor_get(v_kind_2026_, 1);
lean_inc_ref(v_str_2032_);
lean_dec_ref_known(v_kind_2026_, 2);
v_str_2033_ = lean_ctor_get(v_pre_2027_, 1);
lean_inc_ref(v_str_2033_);
lean_dec_ref_known(v_pre_2027_, 2);
v_str_2034_ = lean_ctor_get(v_pre_2028_, 1);
lean_inc_ref(v_str_2034_);
lean_dec_ref_known(v_pre_2028_, 2);
v_str_2035_ = lean_ctor_get(v_pre_2029_, 1);
lean_inc_ref(v_str_2035_);
lean_dec_ref_known(v_pre_2029_, 2);
v___x_2036_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_2037_ = lean_string_dec_eq(v_str_2035_, v___x_2036_);
lean_dec_ref(v_str_2035_);
if (v___x_2037_ == 0)
{
lean_dec_ref(v_str_2034_);
lean_dec_ref(v_str_2033_);
lean_dec_ref(v_str_2032_);
lean_dec_ref(v_args_2031_);
goto v___jp_2018_;
}
else
{
lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2039_ = lean_string_dec_eq(v_str_2034_, v___x_2038_);
lean_dec_ref(v_str_2034_);
if (v___x_2039_ == 0)
{
lean_dec_ref(v_str_2033_);
lean_dec_ref(v_str_2032_);
lean_dec_ref(v_args_2031_);
goto v___jp_2018_;
}
else
{
lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2041_ = lean_string_dec_eq(v_str_2033_, v___x_2040_);
lean_dec_ref(v_str_2033_);
if (v___x_2041_ == 0)
{
lean_dec_ref(v_str_2032_);
lean_dec_ref(v_args_2031_);
goto v___jp_2018_;
}
else
{
lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2042_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2043_ = lean_string_dec_eq(v_str_2032_, v___x_2042_);
lean_dec_ref(v_str_2032_);
if (v___x_2043_ == 0)
{
lean_dec_ref(v_args_2031_);
goto v___jp_2018_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2044_ = lean_array_get_size(v_args_2031_);
v___x_2045_ = lean_unsigned_to_nat(2u);
v___x_2046_ = lean_nat_dec_eq(v___x_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_dec_ref(v_args_2031_);
goto v___jp_2018_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_unsigned_to_nat(0u);
v___x_2048_ = lean_array_fget(v_args_2031_, v___x_2047_);
lean_dec_ref(v_args_2031_);
if (lean_obj_tag(v___x_2048_) == 2)
{
lean_object* v_val_2049_; lean_object* v___x_2050_; 
lean_dec(v_stx_2014_);
v_val_2049_ = lean_ctor_get(v___x_2048_, 1);
lean_inc_ref(v_val_2049_);
lean_dec_ref_known(v___x_2048_, 2);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_val_2049_);
return v___x_2050_;
}
else
{
lean_dec(v___x_2048_);
goto v___jp_2018_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2029_, 2);
lean_dec_ref_known(v_pre_2028_, 2);
lean_dec_ref_known(v_pre_2027_, 2);
lean_dec_ref_known(v_kind_2026_, 2);
lean_dec_ref_known(v___x_2025_, 3);
goto v___jp_2018_;
}
}
else
{
lean_dec_ref_known(v_pre_2028_, 2);
lean_dec(v_pre_2029_);
lean_dec_ref_known(v_pre_2027_, 2);
lean_dec_ref_known(v_kind_2026_, 2);
lean_dec_ref_known(v___x_2025_, 3);
goto v___jp_2018_;
}
}
else
{
lean_dec(v_pre_2028_);
lean_dec_ref_known(v_pre_2027_, 2);
lean_dec_ref_known(v_kind_2026_, 2);
lean_dec_ref_known(v___x_2025_, 3);
goto v___jp_2018_;
}
}
else
{
lean_dec(v_pre_2027_);
lean_dec_ref_known(v_kind_2026_, 2);
lean_dec_ref_known(v___x_2025_, 3);
goto v___jp_2018_;
}
}
else
{
lean_dec(v_kind_2026_);
lean_dec_ref_known(v___x_2025_, 3);
goto v___jp_2018_;
}
}
else
{
lean_dec(v___x_2025_);
goto v___jp_2018_;
}
v___jp_2018_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2019_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_2014_);
v___x_2020_ = l_Lean_MessageData_ofSyntax(v_stx_2014_);
v___x_2021_ = l_Lean_indentD(v___x_2020_);
v___x_2022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2019_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v___x_2023_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_2014_, v___x_2022_, v___y_2015_, v___y_2016_);
lean_dec(v_stx_2014_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2056_, size_t v_sz_2057_, size_t v_i_2058_, lean_object* v_b_2059_){
_start:
{
lean_object* v_a_2061_; uint8_t v___x_2065_; 
v___x_2065_ = lean_usize_dec_lt(v_i_2058_, v_sz_2057_);
if (v___x_2065_ == 0)
{
return v_b_2059_;
}
else
{
lean_object* v_a_2066_; lean_object* v_fst_2067_; lean_object* v_snd_2068_; lean_object* v_out_2069_; uint8_t v___x_2070_; 
v_a_2066_ = lean_array_uget_borrowed(v_as_2056_, v_i_2058_);
v_fst_2067_ = lean_ctor_get(v_a_2066_, 0);
v_snd_2068_ = lean_ctor_get(v_a_2066_, 1);
v_out_2069_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2070_ = lean_string_dec_eq(v_snd_2068_, v_out_2069_);
if (v___x_2070_ == 0)
{
uint8_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2071_ = lean_unbox(v_fst_2067_);
v___x_2072_ = l_Lean_Diff_Action_linePrefix(v___x_2071_);
v___x_2073_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2074_ = lean_string_append(v___x_2072_, v___x_2073_);
v___x_2075_ = lean_string_append(v___x_2074_, v_snd_2068_);
v___x_2076_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2077_ = lean_string_append(v___x_2075_, v___x_2076_);
v___x_2078_ = lean_string_append(v_b_2059_, v___x_2077_);
lean_dec_ref(v___x_2077_);
v_a_2061_ = v___x_2078_;
goto v___jp_2060_;
}
else
{
uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2079_ = lean_unbox(v_fst_2067_);
v___x_2080_ = l_Lean_Diff_Action_linePrefix(v___x_2079_);
v___x_2081_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2082_ = lean_string_append(v___x_2080_, v___x_2081_);
v___x_2083_ = lean_string_append(v_b_2059_, v___x_2082_);
lean_dec_ref(v___x_2082_);
v_a_2061_ = v___x_2083_;
goto v___jp_2060_;
}
}
v___jp_2060_:
{
size_t v___x_2062_; size_t v___x_2063_; 
v___x_2062_ = ((size_t)1ULL);
v___x_2063_ = lean_usize_add(v_i_2058_, v___x_2062_);
v_i_2058_ = v___x_2063_;
v_b_2059_ = v_a_2061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2084_, lean_object* v_sz_2085_, lean_object* v_i_2086_, lean_object* v_b_2087_){
_start:
{
size_t v_sz_boxed_2088_; size_t v_i_boxed_2089_; lean_object* v_res_2090_; 
v_sz_boxed_2088_ = lean_unbox_usize(v_sz_2085_);
lean_dec(v_sz_2085_);
v_i_boxed_2089_ = lean_unbox_usize(v_i_2086_);
lean_dec(v_i_2086_);
v_res_2090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2084_, v_sz_boxed_2088_, v_i_boxed_2089_, v_b_2087_);
lean_dec_ref(v_as_2084_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2091_){
_start:
{
lean_object* v_out_2092_; size_t v_sz_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v_out_2092_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v_sz_2093_ = lean_array_size(v_lines_2091_);
v___x_2094_ = ((size_t)0ULL);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2091_, v_sz_2093_, v___x_2094_, v_out_2092_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2096_);
lean_dec_ref(v_lines_2096_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2098_, lean_object* v_as_x27_2099_, lean_object* v_b_2100_){
_start:
{
if (lean_obj_tag(v_as_x27_2099_) == 0)
{
lean_object* v___x_2102_; 
lean_dec_ref(v_filterFn_2098_);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v_b_2100_);
return v___x_2102_;
}
else
{
lean_object* v_head_2103_; uint8_t v_isSilent_2104_; 
v_head_2103_ = lean_ctor_get(v_as_x27_2099_, 0);
v_isSilent_2104_ = lean_ctor_get_uint8(v_head_2103_, sizeof(void*)*5 + 2);
if (v_isSilent_2104_ == 0)
{
lean_object* v_tail_2105_; lean_object* v_fst_2106_; lean_object* v_snd_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2127_; 
v_tail_2105_ = lean_ctor_get(v_as_x27_2099_, 1);
v_fst_2106_ = lean_ctor_get(v_b_2100_, 0);
v_snd_2107_ = lean_ctor_get(v_b_2100_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_b_2100_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2109_ = v_b_2100_;
v_isShared_2110_ = v_isSharedCheck_2127_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_snd_2107_);
lean_inc(v_fst_2106_);
lean_dec(v_b_2100_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2127_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; uint8_t v___x_2112_; 
lean_inc_ref(v_filterFn_2098_);
lean_inc(v_head_2103_);
v___x_2111_ = lean_apply_1(v_filterFn_2098_, v_head_2103_);
v___x_2112_ = lean_unbox(v___x_2111_);
switch(v___x_2112_)
{
case 0:
{
lean_object* v___x_2113_; lean_object* v___x_2115_; 
lean_inc(v_head_2103_);
v___x_2113_ = l_Lean_MessageLog_add(v_head_2103_, v_fst_2106_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2113_);
v___x_2115_ = v___x_2109_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_snd_2107_);
v___x_2115_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
v_as_x27_2099_ = v_tail_2105_;
v_b_2100_ = v___x_2115_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2119_; 
if (v_isShared_2110_ == 0)
{
v___x_2119_ = v___x_2109_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_fst_2106_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_snd_2107_);
v___x_2119_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
v_as_x27_2099_ = v_tail_2105_;
v_b_2100_ = v___x_2119_;
goto _start;
}
}
default: 
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
lean_inc(v_head_2103_);
v___x_2122_ = l_Lean_MessageLog_add(v_head_2103_, v_snd_2107_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v___x_2122_);
v___x_2124_ = v___x_2109_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_fst_2106_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
v_as_x27_2099_ = v_tail_2105_;
v_b_2100_ = v___x_2124_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2128_; lean_object* v_fst_2129_; lean_object* v_snd_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2138_; 
v_tail_2128_ = lean_ctor_get(v_as_x27_2099_, 1);
v_fst_2129_ = lean_ctor_get(v_b_2100_, 0);
v_snd_2130_ = lean_ctor_get(v_b_2100_, 1);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_b_2100_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2132_ = v_b_2100_;
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_snd_2130_);
lean_inc(v_fst_2129_);
lean_dec(v_b_2100_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_fst_2129_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_snd_2130_);
v___x_2135_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
v_as_x27_2099_ = v_tail_2128_;
v_b_2100_ = v___x_2135_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2139_, lean_object* v_as_x27_2140_, lean_object* v_b_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2139_, v_as_x27_2140_, v_b_2141_);
lean_dec(v_as_x27_2140_);
return v_res_2143_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2144_, lean_object* v_a_2145_, uint8_t v_b_2146_){
_start:
{
uint8_t v___x_2147_; 
v___x_2147_ = 0;
switch(lean_obj_tag(v_a_2145_))
{
case 0:
{
lean_object* v_pos_2148_; lean_object* v_startInclusive_2149_; lean_object* v_endExclusive_2150_; lean_object* v___x_2151_; uint8_t v_decide_2152_; 
v_pos_2148_ = lean_ctor_get(v_a_2145_, 0);
lean_inc(v_pos_2148_);
lean_dec_ref_known(v_a_2145_, 1);
v_startInclusive_2149_ = lean_ctor_get(v_s_2144_, 1);
v_endExclusive_2150_ = lean_ctor_get(v_s_2144_, 2);
v___x_2151_ = lean_nat_sub(v_endExclusive_2150_, v_startInclusive_2149_);
v_decide_2152_ = lean_nat_dec_eq(v_pos_2148_, v___x_2151_);
lean_dec(v___x_2151_);
lean_dec(v_pos_2148_);
if (v_decide_2152_ == 0)
{
uint8_t v___x_2153_; 
v___x_2153_ = 1;
return v___x_2153_;
}
else
{
return v_decide_2152_;
}
}
case 1:
{
lean_object* v_pos_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2167_; 
v_pos_2154_ = lean_ctor_get(v_a_2145_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_a_2145_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2156_ = v_a_2145_;
v_isShared_2157_ = v_isSharedCheck_2167_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_pos_2154_);
lean_dec(v_a_2145_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2167_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v_str_2158_; lean_object* v_startInclusive_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; 
v_str_2158_ = lean_ctor_get(v_s_2144_, 0);
v_startInclusive_2159_ = lean_ctor_get(v_s_2144_, 1);
v___x_2160_ = lean_nat_add(v_startInclusive_2159_, v_pos_2154_);
lean_dec(v_pos_2154_);
v___x_2161_ = lean_string_utf8_next_fast(v_str_2158_, v___x_2160_);
lean_dec(v___x_2160_);
v___x_2162_ = lean_nat_sub(v___x_2161_, v_startInclusive_2159_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set_tag(v___x_2156_, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2162_);
v___x_2164_ = v___x_2156_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
v_a_2145_ = v___x_2164_;
v_b_2146_ = v___x_2147_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2168_; lean_object* v_table_2169_; lean_object* v_stackPos_2170_; lean_object* v_needlePos_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2226_; 
v_needle_2168_ = lean_ctor_get(v_a_2145_, 0);
v_table_2169_ = lean_ctor_get(v_a_2145_, 1);
v_stackPos_2170_ = lean_ctor_get(v_a_2145_, 2);
v_needlePos_2171_ = lean_ctor_get(v_a_2145_, 3);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_a_2145_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2173_ = v_a_2145_;
v_isShared_2174_ = v_isSharedCheck_2226_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_needlePos_2171_);
lean_inc(v_stackPos_2170_);
lean_inc(v_table_2169_);
lean_inc(v_needle_2168_);
lean_dec(v_a_2145_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2226_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_str_2175_; lean_object* v_startInclusive_2176_; lean_object* v_endExclusive_2177_; lean_object* v_str_2178_; lean_object* v_startInclusive_2179_; lean_object* v_endExclusive_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v_str_2175_ = lean_ctor_get(v_needle_2168_, 0);
v_startInclusive_2176_ = lean_ctor_get(v_needle_2168_, 1);
v_endExclusive_2177_ = lean_ctor_get(v_needle_2168_, 2);
v_str_2178_ = lean_ctor_get(v_s_2144_, 0);
v_startInclusive_2179_ = lean_ctor_get(v_s_2144_, 1);
v_endExclusive_2180_ = lean_ctor_get(v_s_2144_, 2);
v___x_2181_ = lean_nat_sub(v_stackPos_2170_, v_needlePos_2171_);
v___x_2182_ = lean_nat_sub(v_endExclusive_2177_, v_startInclusive_2176_);
v___x_2183_ = lean_nat_add(v___x_2181_, v___x_2182_);
v___x_2184_ = lean_nat_sub(v_endExclusive_2180_, v_startInclusive_2179_);
v___x_2185_ = lean_nat_dec_le(v___x_2183_, v___x_2184_);
lean_dec(v___x_2183_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
lean_dec(v___x_2182_);
lean_del_object(v___x_2173_);
lean_dec(v_needlePos_2171_);
lean_dec(v_stackPos_2170_);
lean_dec_ref(v_table_2169_);
lean_dec_ref(v_needle_2168_);
v___x_2186_ = lean_unsigned_to_nat(1u);
v___x_2187_ = lean_nat_add(v___x_2181_, v___x_2186_);
lean_dec(v___x_2181_);
v___x_2188_ = lean_nat_dec_le(v___x_2187_, v___x_2184_);
lean_dec(v___x_2184_);
lean_dec(v___x_2187_);
if (v___x_2188_ == 0)
{
return v_b_2146_;
}
else
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_box(3);
v_a_2145_ = v___x_2189_;
v_b_2146_ = v___x_2147_;
goto _start;
}
}
else
{
lean_object* v___x_2191_; uint8_t v_stackByte_2192_; lean_object* v___x_2193_; uint8_t v_patByte_2194_; uint8_t v___x_2195_; 
lean_dec(v___x_2184_);
lean_dec(v___x_2181_);
v___x_2191_ = lean_nat_add(v_startInclusive_2179_, v_stackPos_2170_);
v_stackByte_2192_ = lean_string_get_byte_fast(v_str_2178_, v___x_2191_);
v___x_2193_ = lean_nat_add(v_startInclusive_2176_, v_needlePos_2171_);
v_patByte_2194_ = lean_string_get_byte_fast(v_str_2175_, v___x_2193_);
v___x_2195_ = lean_uint8_dec_eq(v_stackByte_2192_, v_patByte_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; uint8_t v_decide_2197_; 
lean_dec(v___x_2182_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v_decide_2197_ = lean_nat_dec_eq(v_needlePos_2171_, v___x_2196_);
if (v_decide_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v_newNeedlePos_2200_; uint8_t v___x_2201_; 
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = lean_nat_sub(v_needlePos_2171_, v___x_2198_);
lean_dec(v_needlePos_2171_);
v_newNeedlePos_2200_ = lean_array_fget_borrowed(v_table_2169_, v___x_2199_);
lean_dec(v___x_2199_);
v___x_2201_ = lean_nat_dec_eq(v_newNeedlePos_2200_, v___x_2196_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2203_; 
lean_inc(v_newNeedlePos_2200_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 3, v_newNeedlePos_2200_);
v___x_2203_ = v___x_2173_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_needle_2168_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_table_2169_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_stackPos_2170_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_newNeedlePos_2200_);
v___x_2203_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
v_a_2145_ = v___x_2203_;
v_b_2146_ = v___x_2147_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2206_; lean_object* v___x_2208_; 
v_nextStackPos_2206_ = l_String_Slice_posGE___redArg(v_s_2144_, v_stackPos_2170_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 3, v___x_2196_);
lean_ctor_set(v___x_2173_, 2, v_nextStackPos_2206_);
v___x_2208_ = v___x_2173_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_needle_2168_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_table_2169_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_nextStackPos_2206_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v___x_2196_);
v___x_2208_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
v_a_2145_ = v___x_2208_;
v_b_2146_ = v___x_2147_;
goto _start;
}
}
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v_nextStackPos_2213_; lean_object* v___x_2215_; 
lean_dec(v_needlePos_2171_);
v___x_2211_ = lean_unsigned_to_nat(1u);
v___x_2212_ = lean_nat_add(v_stackPos_2170_, v___x_2211_);
lean_dec(v_stackPos_2170_);
v_nextStackPos_2213_ = l_String_Slice_posGE___redArg(v_s_2144_, v___x_2212_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 3, v___x_2196_);
lean_ctor_set(v___x_2173_, 2, v_nextStackPos_2213_);
v___x_2215_ = v___x_2173_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_needle_2168_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_table_2169_);
lean_ctor_set(v_reuseFailAlloc_2217_, 2, v_nextStackPos_2213_);
lean_ctor_set(v_reuseFailAlloc_2217_, 3, v___x_2196_);
v___x_2215_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
v_a_2145_ = v___x_2215_;
v_b_2146_ = v___x_2147_;
goto _start;
}
}
}
else
{
lean_object* v___x_2218_; lean_object* v_nextNeedlePos_2219_; uint8_t v_decide_2220_; 
v___x_2218_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2219_ = lean_nat_add(v_needlePos_2171_, v___x_2218_);
lean_dec(v_needlePos_2171_);
v_decide_2220_ = lean_nat_dec_eq(v_nextNeedlePos_2219_, v___x_2182_);
lean_dec(v___x_2182_);
if (v_decide_2220_ == 0)
{
lean_object* v_nextStackPos_2221_; lean_object* v___x_2223_; 
v_nextStackPos_2221_ = lean_nat_add(v_stackPos_2170_, v___x_2218_);
lean_dec(v_stackPos_2170_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 3, v_nextNeedlePos_2219_);
lean_ctor_set(v___x_2173_, 2, v_nextStackPos_2221_);
v___x_2223_ = v___x_2173_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_needle_2168_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_table_2169_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_nextStackPos_2221_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_nextNeedlePos_2219_);
v___x_2223_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
v_a_2145_ = v___x_2223_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2219_);
lean_del_object(v___x_2173_);
lean_dec(v_stackPos_2170_);
lean_dec_ref(v_table_2169_);
lean_dec_ref(v_needle_2168_);
return v_decide_2220_;
}
}
}
}
}
default: 
{
return v_b_2146_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2227_, lean_object* v_a_2228_, lean_object* v_b_2229_){
_start:
{
uint8_t v_b_boxed_2230_; uint8_t v_res_2231_; lean_object* v_r_2232_; 
v_b_boxed_2230_ = lean_unbox(v_b_2229_);
v_res_2231_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2227_, v_a_2228_, v_b_boxed_2230_);
lean_dec_ref(v_s_2227_);
v_r_2232_ = lean_box(v_res_2231_);
return v_r_2232_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2235_, lean_object* v_s_2236_){
_start:
{
lean_object* v___y_2238_; lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = lean_string_utf8_byte_size(v___x_2235_);
v___x_2243_ = lean_nat_dec_eq(v___x_2242_, v___x_2241_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2235_);
lean_ctor_set(v___x_2244_, 1, v___x_2241_);
lean_ctor_set(v___x_2244_, 2, v___x_2242_);
v___x_2245_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2244_);
v___x_2246_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2244_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
lean_ctor_set(v___x_2246_, 2, v___x_2241_);
lean_ctor_set(v___x_2246_, 3, v___x_2241_);
v___y_2238_ = v___x_2246_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2247_; 
lean_dec_ref(v___x_2235_);
v___x_2247_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___closed__0));
v___y_2238_ = v___x_2247_;
goto v___jp_2237_;
}
v___jp_2237_:
{
uint8_t v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = 0;
v___x_2240_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2236_, v___y_2238_, v___x_2239_);
return v___x_2240_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2248_, lean_object* v_s_2249_){
_start:
{
uint8_t v_res_2250_; lean_object* v_r_2251_; 
v_res_2250_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2248_, v_s_2249_);
lean_dec_ref(v_s_2249_);
v_r_2251_ = lean_box(v_res_2250_);
return v_r_2251_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v_suppressElabErrors_2252_, uint8_t v___y_2253_, lean_object* v_x_2254_){
_start:
{
if (lean_obj_tag(v_x_2254_) == 1)
{
lean_object* v_pre_2255_; 
v_pre_2255_ = lean_ctor_get(v_x_2254_, 0);
if (lean_obj_tag(v_pre_2255_) == 0)
{
lean_object* v_str_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v_str_2256_ = lean_ctor_get(v_x_2254_, 1);
v___x_2257_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2258_ = lean_string_dec_eq(v_str_2256_, v___x_2257_);
if (v___x_2258_ == 0)
{
return v___x_2258_;
}
else
{
return v_suppressElabErrors_2252_;
}
}
else
{
return v___y_2253_;
}
}
else
{
return v___y_2253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_2259_, lean_object* v___y_2260_, lean_object* v_x_2261_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2262_; uint8_t v___y_26108__boxed_2263_; uint8_t v_res_2264_; lean_object* v_r_2265_; 
v_suppressElabErrors_boxed_2262_ = lean_unbox(v_suppressElabErrors_2259_);
v___y_26108__boxed_2263_ = lean_unbox(v___y_2260_);
v_res_2264_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v_suppressElabErrors_boxed_2262_, v___y_26108__boxed_2263_, v_x_2261_);
lean_dec(v_x_2261_);
v_r_2265_ = lean_box(v_res_2264_);
return v_r_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2266_, lean_object* v_msgData_2267_, uint8_t v_severity_2268_, uint8_t v_isSilent_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; uint8_t v___y_2278_; uint8_t v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; uint8_t v___y_2339_; lean_object* v___y_2340_; uint8_t v___y_2341_; uint8_t v___y_2342_; lean_object* v___y_2343_; uint8_t v___y_2367_; uint8_t v___y_2368_; uint8_t v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; uint8_t v___y_2375_; uint8_t v___y_2376_; uint8_t v___y_2377_; uint8_t v___x_2392_; uint8_t v___y_2394_; uint8_t v___y_2395_; uint8_t v___y_2396_; uint8_t v___y_2398_; uint8_t v___x_2410_; 
v___x_2392_ = 2;
v___x_2410_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2268_, v___x_2392_);
if (v___x_2410_ == 0)
{
v___y_2398_ = v___x_2410_;
goto v___jp_2397_;
}
else
{
uint8_t v___x_2411_; 
lean_inc_ref(v_msgData_2267_);
v___x_2411_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2267_);
v___y_2398_ = v___x_2411_;
goto v___jp_2397_;
}
v___jp_2273_:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_Elab_Command_getScope___redArg(v___y_2281_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v_currNamespace_2284_; lean_object* v___x_2285_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v_currNamespace_2284_ = lean_ctor_get(v_a_2283_, 2);
lean_inc(v_currNamespace_2284_);
lean_dec(v_a_2283_);
v___x_2285_ = l_Lean_Elab_Command_getScope___redArg(v___y_2281_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2321_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2321_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2321_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v_openDecls_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v_env_2295_; lean_object* v_messages_2296_; lean_object* v_scopes_2297_; lean_object* v_usedQuotCtxts_2298_; lean_object* v_nextMacroScope_2299_; lean_object* v_maxRecDepth_2300_; lean_object* v_ngen_2301_; lean_object* v_auxDeclNGen_2302_; lean_object* v_infoState_2303_; lean_object* v_traceState_2304_; lean_object* v_snapshotTasks_2305_; lean_object* v_prevLinterStates_2306_; lean_object* v_codeQualityEntryTasks_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2320_; 
v_openDecls_2290_ = lean_ctor_get(v_a_2286_, 3);
lean_inc(v_openDecls_2290_);
lean_dec(v_a_2286_);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v_currNamespace_2284_);
lean_ctor_set(v___x_2291_, 1, v_openDecls_2290_);
v___x_2292_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v___y_2276_);
lean_inc_ref(v___y_2275_);
lean_inc_ref(v___y_2280_);
v___x_2293_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2293_, 0, v___y_2280_);
lean_ctor_set(v___x_2293_, 1, v___y_2274_);
lean_ctor_set(v___x_2293_, 2, v___y_2277_);
lean_ctor_set(v___x_2293_, 3, v___y_2275_);
lean_ctor_set(v___x_2293_, 4, v___x_2292_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*5, v___y_2278_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*5 + 1, v___y_2279_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*5 + 2, v_isSilent_2269_);
v___x_2294_ = lean_st_ref_take(v___y_2281_);
v_env_2295_ = lean_ctor_get(v___x_2294_, 0);
v_messages_2296_ = lean_ctor_get(v___x_2294_, 1);
v_scopes_2297_ = lean_ctor_get(v___x_2294_, 2);
v_usedQuotCtxts_2298_ = lean_ctor_get(v___x_2294_, 3);
v_nextMacroScope_2299_ = lean_ctor_get(v___x_2294_, 4);
v_maxRecDepth_2300_ = lean_ctor_get(v___x_2294_, 5);
v_ngen_2301_ = lean_ctor_get(v___x_2294_, 6);
v_auxDeclNGen_2302_ = lean_ctor_get(v___x_2294_, 7);
v_infoState_2303_ = lean_ctor_get(v___x_2294_, 8);
v_traceState_2304_ = lean_ctor_get(v___x_2294_, 9);
v_snapshotTasks_2305_ = lean_ctor_get(v___x_2294_, 10);
v_prevLinterStates_2306_ = lean_ctor_get(v___x_2294_, 11);
v_codeQualityEntryTasks_2307_ = lean_ctor_get(v___x_2294_, 12);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2309_ = v___x_2294_;
v_isShared_2310_ = v_isSharedCheck_2320_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2307_);
lean_inc(v_prevLinterStates_2306_);
lean_inc(v_snapshotTasks_2305_);
lean_inc(v_traceState_2304_);
lean_inc(v_infoState_2303_);
lean_inc(v_auxDeclNGen_2302_);
lean_inc(v_ngen_2301_);
lean_inc(v_maxRecDepth_2300_);
lean_inc(v_nextMacroScope_2299_);
lean_inc(v_usedQuotCtxts_2298_);
lean_inc(v_scopes_2297_);
lean_inc(v_messages_2296_);
lean_inc(v_env_2295_);
lean_dec(v___x_2294_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2320_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2311_ = lean_box(0);
v___x_2312_ = l_Lean_MessageLog_add(v___x_2293_, v_messages_2296_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v___x_2312_);
v___x_2314_ = v___x_2309_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_env_2295_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v_scopes_2297_);
lean_ctor_set(v_reuseFailAlloc_2319_, 3, v_usedQuotCtxts_2298_);
lean_ctor_set(v_reuseFailAlloc_2319_, 4, v_nextMacroScope_2299_);
lean_ctor_set(v_reuseFailAlloc_2319_, 5, v_maxRecDepth_2300_);
lean_ctor_set(v_reuseFailAlloc_2319_, 6, v_ngen_2301_);
lean_ctor_set(v_reuseFailAlloc_2319_, 7, v_auxDeclNGen_2302_);
lean_ctor_set(v_reuseFailAlloc_2319_, 8, v_infoState_2303_);
lean_ctor_set(v_reuseFailAlloc_2319_, 9, v_traceState_2304_);
lean_ctor_set(v_reuseFailAlloc_2319_, 10, v_snapshotTasks_2305_);
lean_ctor_set(v_reuseFailAlloc_2319_, 11, v_prevLinterStates_2306_);
lean_ctor_set(v_reuseFailAlloc_2319_, 12, v_codeQualityEntryTasks_2307_);
v___x_2314_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2315_ = lean_st_ref_put(v___y_2281_, v___x_2314_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2311_);
v___x_2317_ = v___x_2288_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2311_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_currNamespace_2284_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec_ref(v___y_2274_);
v_a_2322_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2285_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2285_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec_ref(v___y_2274_);
v_a_2330_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2282_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2282_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
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
v___jp_2338_:
{
lean_object* v_fileName_2344_; lean_object* v_fileMap_2345_; uint8_t v_suppressElabErrors_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___f_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2365_; 
v_fileName_2344_ = lean_ctor_get(v___y_2270_, 0);
v_fileMap_2345_ = lean_ctor_get(v___y_2270_, 1);
v_suppressElabErrors_2346_ = lean_ctor_get_uint8(v___y_2270_, sizeof(void*)*10);
v___x_2347_ = lean_box(v_suppressElabErrors_2346_);
v___x_2348_ = lean_box(v___y_2339_);
v___f_2349_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2349_, 0, v___x_2347_);
lean_closure_set(v___f_2349_, 1, v___x_2348_);
v___x_2350_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2267_);
v___x_2351_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2350_, v___y_2271_);
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2365_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2365_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_inc_ref_n(v_fileMap_2345_, 2);
v___x_2356_ = l_Lean_FileMap_toPosition(v_fileMap_2345_, v___y_2340_);
lean_dec(v___y_2340_);
v___x_2357_ = l_Lean_FileMap_toPosition(v_fileMap_2345_, v___y_2343_);
lean_dec(v___y_2343_);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
v___x_2359_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
if (v_suppressElabErrors_2346_ == 0)
{
lean_del_object(v___x_2354_);
lean_dec_ref(v___f_2349_);
v___y_2274_ = v___x_2356_;
v___y_2275_ = v___x_2359_;
v___y_2276_ = v_a_2352_;
v___y_2277_ = v___x_2358_;
v___y_2278_ = v___y_2341_;
v___y_2279_ = v___y_2342_;
v___y_2280_ = v_fileName_2344_;
v___y_2281_ = v___y_2271_;
goto v___jp_2273_;
}
else
{
uint8_t v___x_2360_; 
lean_inc(v_a_2352_);
v___x_2360_ = l_Lean_MessageData_hasTag(v___f_2349_, v_a_2352_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_dec_ref_known(v___x_2358_, 1);
lean_dec_ref(v___x_2356_);
lean_dec(v_a_2352_);
v___x_2361_ = lean_box(0);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2361_);
v___x_2363_ = v___x_2354_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
else
{
lean_del_object(v___x_2354_);
v___y_2274_ = v___x_2356_;
v___y_2275_ = v___x_2359_;
v___y_2276_ = v_a_2352_;
v___y_2277_ = v___x_2358_;
v___y_2278_ = v___y_2341_;
v___y_2279_ = v___y_2342_;
v___y_2280_ = v_fileName_2344_;
v___y_2281_ = v___y_2271_;
goto v___jp_2273_;
}
}
}
}
v___jp_2366_:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_Syntax_getTailPos_x3f(v___y_2370_, v___y_2368_);
lean_dec(v___y_2370_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_inc(v___y_2371_);
v___y_2339_ = v___y_2367_;
v___y_2340_ = v___y_2371_;
v___y_2341_ = v___y_2368_;
v___y_2342_ = v___y_2369_;
v___y_2343_ = v___y_2371_;
goto v___jp_2338_;
}
else
{
lean_object* v_val_2373_; 
v_val_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_val_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v___y_2339_ = v___y_2367_;
v___y_2340_ = v___y_2371_;
v___y_2341_ = v___y_2368_;
v___y_2342_ = v___y_2369_;
v___y_2343_ = v_val_2373_;
goto v___jp_2338_;
}
}
v___jp_2374_:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_Elab_Command_getRef___redArg(v___y_2270_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v_ref_2380_; lean_object* v___x_2381_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v_ref_2380_ = l_Lean_replaceRef(v_ref_2266_, v_a_2379_);
lean_dec(v_a_2379_);
v___x_2381_ = l_Lean_Syntax_getPos_x3f(v_ref_2380_, v___y_2376_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_unsigned_to_nat(0u);
v___y_2367_ = v___y_2375_;
v___y_2368_ = v___y_2376_;
v___y_2369_ = v___y_2377_;
v___y_2370_ = v_ref_2380_;
v___y_2371_ = v___x_2382_;
goto v___jp_2366_;
}
else
{
lean_object* v_val_2383_; 
v_val_2383_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_val_2383_);
lean_dec_ref_known(v___x_2381_, 1);
v___y_2367_ = v___y_2375_;
v___y_2368_ = v___y_2376_;
v___y_2369_ = v___y_2377_;
v___y_2370_ = v_ref_2380_;
v___y_2371_ = v_val_2383_;
goto v___jp_2366_;
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec_ref(v_msgData_2267_);
v_a_2384_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2378_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2378_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
v___jp_2393_:
{
if (v___y_2396_ == 0)
{
v___y_2375_ = v___y_2394_;
v___y_2376_ = v___y_2395_;
v___y_2377_ = v_severity_2268_;
goto v___jp_2374_;
}
else
{
v___y_2375_ = v___y_2394_;
v___y_2376_ = v___y_2395_;
v___y_2377_ = v___x_2392_;
goto v___jp_2374_;
}
}
v___jp_2397_:
{
if (v___y_2398_ == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v_scopes_2401_; lean_object* v___x_2402_; lean_object* v_opts_2403_; uint8_t v___x_2404_; uint8_t v___x_2405_; 
v___x_2399_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2400_ = lean_st_ref_get(v___y_2271_);
v_scopes_2401_ = lean_ctor_get(v___x_2400_, 2);
lean_inc(v_scopes_2401_);
lean_dec(v___x_2400_);
v___x_2402_ = l_List_head_x21___redArg(v___x_2399_, v_scopes_2401_);
lean_dec(v_scopes_2401_);
v_opts_2403_ = lean_ctor_get(v___x_2402_, 1);
lean_inc_ref(v_opts_2403_);
lean_dec(v___x_2402_);
v___x_2404_ = 1;
v___x_2405_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2268_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_dec_ref(v_opts_2403_);
v___y_2394_ = v___y_2398_;
v___y_2395_ = v___y_2398_;
v___y_2396_ = v___x_2405_;
goto v___jp_2393_;
}
else
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = l_Lean_warningAsError;
v___x_2407_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2403_, v___x_2406_);
lean_dec_ref(v_opts_2403_);
v___y_2394_ = v___y_2398_;
v___y_2395_ = v___y_2398_;
v___y_2396_ = v___x_2407_;
goto v___jp_2393_;
}
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_dec_ref(v_msgData_2267_);
v___x_2408_ = lean_box(0);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2412_, lean_object* v_msgData_2413_, lean_object* v_severity_2414_, lean_object* v_isSilent_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
uint8_t v_severity_boxed_2419_; uint8_t v_isSilent_boxed_2420_; lean_object* v_res_2421_; 
v_severity_boxed_2419_ = lean_unbox(v_severity_2414_);
v_isSilent_boxed_2420_ = lean_unbox(v_isSilent_2415_);
v_res_2421_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2412_, v_msgData_2413_, v_severity_boxed_2419_, v_isSilent_boxed_2420_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v_ref_2412_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2422_, lean_object* v_msgData_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = 2;
v___x_2428_ = 0;
v___x_2429_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2422_, v_msgData_2423_, v___x_2427_, v___x_2428_, v___y_2424_, v___y_2425_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2430_, lean_object* v_msgData_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2430_, v_msgData_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v_ref_2430_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2436_, lean_object* v___x_2437_, lean_object* v___x_2438_, lean_object* v_a_2439_, lean_object* v_b_2440_){
_start:
{
lean_object* v_it_2442_; lean_object* v_startInclusive_2443_; lean_object* v_endExclusive_2444_; 
if (lean_obj_tag(v_a_2439_) == 0)
{
lean_object* v_currPos_2449_; lean_object* v_searcher_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2479_; 
v_currPos_2449_ = lean_ctor_get(v_a_2439_, 0);
v_searcher_2450_ = lean_ctor_get(v_a_2439_, 1);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_a_2439_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2452_ = v_a_2439_;
v_isShared_2453_ = v_isSharedCheck_2479_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_searcher_2450_);
lean_inc(v_currPos_2449_);
lean_dec(v_a_2439_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2479_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v_str_2454_; lean_object* v_startInclusive_2455_; lean_object* v_endExclusive_2456_; lean_object* v___x_2457_; uint8_t v_decide_2458_; 
v_str_2454_ = lean_ctor_get(v___x_2437_, 0);
v_startInclusive_2455_ = lean_ctor_get(v___x_2437_, 1);
v_endExclusive_2456_ = lean_ctor_get(v___x_2437_, 2);
v___x_2457_ = lean_nat_sub(v_endExclusive_2456_, v_startInclusive_2455_);
v_decide_2458_ = lean_nat_dec_eq(v_searcher_2450_, v___x_2457_);
lean_dec(v___x_2457_);
if (v_decide_2458_ == 0)
{
uint32_t v___x_2459_; lean_object* v___x_2460_; uint32_t v___x_2461_; uint8_t v___x_2462_; 
v___x_2459_ = 10;
v___x_2460_ = lean_nat_add(v_startInclusive_2455_, v_searcher_2450_);
v___x_2461_ = lean_string_utf8_get_fast(v_str_2454_, v___x_2460_);
v___x_2462_ = lean_uint32_dec_eq(v___x_2461_, v___x_2459_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
lean_dec(v_searcher_2450_);
v___x_2463_ = lean_string_utf8_next_fast(v_str_2454_, v___x_2460_);
lean_dec(v___x_2460_);
v___x_2464_ = lean_nat_sub(v___x_2463_, v_startInclusive_2455_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2464_);
v___x_2466_ = v___x_2452_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_currPos_2449_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
v_a_2439_ = v___x_2466_;
goto _start;
}
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v_slice_2472_; lean_object* v_nextIt_2474_; 
v___x_2469_ = lean_string_utf8_next_fast(v_str_2454_, v___x_2460_);
v___x_2470_ = lean_nat_sub(v___x_2469_, v___x_2460_);
lean_dec(v___x_2460_);
v___x_2471_ = lean_nat_add(v_searcher_2450_, v___x_2470_);
lean_dec(v___x_2470_);
v_slice_2472_ = l_String_Slice_subslice_x21(v___x_2437_, v_currPos_2449_, v_searcher_2450_);
lean_inc(v___x_2471_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2471_);
lean_ctor_set(v___x_2452_, 0, v___x_2471_);
v_nextIt_2474_ = v___x_2452_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2471_);
v_nextIt_2474_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v_startInclusive_2475_; lean_object* v_endExclusive_2476_; 
v_startInclusive_2475_ = lean_ctor_get(v_slice_2472_, 0);
lean_inc(v_startInclusive_2475_);
v_endExclusive_2476_ = lean_ctor_get(v_slice_2472_, 1);
lean_inc(v_endExclusive_2476_);
lean_dec_ref(v_slice_2472_);
v_it_2442_ = v_nextIt_2474_;
v_startInclusive_2443_ = v_startInclusive_2475_;
v_endExclusive_2444_ = v_endExclusive_2476_;
goto v___jp_2441_;
}
}
}
else
{
lean_object* v___x_2478_; 
lean_del_object(v___x_2452_);
lean_dec(v_searcher_2450_);
v___x_2478_ = lean_box(1);
lean_inc(v___x_2438_);
v_it_2442_ = v___x_2478_;
v_startInclusive_2443_ = v_currPos_2449_;
v_endExclusive_2444_ = v___x_2438_;
goto v___jp_2441_;
}
}
}
else
{
lean_dec(v___x_2438_);
lean_dec_ref(v___x_2436_);
return v_b_2440_;
}
v___jp_2441_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_inc_ref(v___x_2436_);
v___x_2445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2436_);
lean_ctor_set(v___x_2445_, 1, v_startInclusive_2443_);
lean_ctor_set(v___x_2445_, 2, v_endExclusive_2444_);
v___x_2446_ = l_String_Slice_toString(v___x_2445_);
lean_dec_ref_known(v___x_2445_, 3);
v___x_2447_ = lean_array_push(v_b_2440_, v___x_2446_);
v_a_2439_ = v_it_2442_;
v_b_2440_ = v___x_2447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2480_, lean_object* v___x_2481_, lean_object* v___x_2482_, lean_object* v_a_2483_, lean_object* v_b_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2480_, v___x_2481_, v___x_2482_, v_a_2483_, v_b_2484_);
lean_dec_ref(v___x_2481_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2486_, lean_object* v___x_2487_, lean_object* v___x_2488_, lean_object* v_a_2489_, lean_object* v_b_2490_){
_start:
{
lean_object* v_it_2492_; lean_object* v_startInclusive_2493_; lean_object* v_endExclusive_2494_; 
if (lean_obj_tag(v_a_2489_) == 0)
{
lean_object* v_currPos_2499_; lean_object* v_searcher_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2529_; 
v_currPos_2499_ = lean_ctor_get(v_a_2489_, 0);
v_searcher_2500_ = lean_ctor_get(v_a_2489_, 1);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_a_2489_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2502_ = v_a_2489_;
v_isShared_2503_ = v_isSharedCheck_2529_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_searcher_2500_);
lean_inc(v_currPos_2499_);
lean_dec(v_a_2489_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2529_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_str_2504_; lean_object* v_startInclusive_2505_; lean_object* v_endExclusive_2506_; lean_object* v___x_2507_; uint8_t v_decide_2508_; 
v_str_2504_ = lean_ctor_get(v___x_2487_, 0);
v_startInclusive_2505_ = lean_ctor_get(v___x_2487_, 1);
v_endExclusive_2506_ = lean_ctor_get(v___x_2487_, 2);
v___x_2507_ = lean_nat_sub(v_endExclusive_2506_, v_startInclusive_2505_);
v_decide_2508_ = lean_nat_dec_eq(v_searcher_2500_, v___x_2507_);
lean_dec(v___x_2507_);
if (v_decide_2508_ == 0)
{
lean_object* v___x_2509_; uint32_t v___x_2510_; uint32_t v___x_2511_; uint8_t v___x_2512_; 
v___x_2509_ = lean_nat_add(v_startInclusive_2505_, v_searcher_2500_);
v___x_2510_ = lean_string_utf8_get_fast(v_str_2504_, v___x_2509_);
v___x_2511_ = 10;
v___x_2512_ = lean_uint32_dec_eq(v___x_2510_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
lean_dec(v_searcher_2500_);
v___x_2513_ = lean_string_utf8_next_fast(v_str_2504_, v___x_2509_);
lean_dec(v___x_2509_);
v___x_2514_ = lean_nat_sub(v___x_2513_, v_startInclusive_2505_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 1, v___x_2514_);
v___x_2516_ = v___x_2502_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_currPos_2499_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; 
v___x_2517_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2486_, v___x_2487_, v___x_2488_, v___x_2516_, v_b_2490_);
return v___x_2517_;
}
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v_slice_2522_; lean_object* v_nextIt_2524_; 
v___x_2519_ = lean_string_utf8_next_fast(v_str_2504_, v___x_2509_);
v___x_2520_ = lean_nat_sub(v___x_2519_, v___x_2509_);
lean_dec(v___x_2509_);
v___x_2521_ = lean_nat_add(v_searcher_2500_, v___x_2520_);
lean_dec(v___x_2520_);
v_slice_2522_ = l_String_Slice_subslice_x21(v___x_2487_, v_currPos_2499_, v_searcher_2500_);
lean_inc(v___x_2521_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 1, v___x_2521_);
lean_ctor_set(v___x_2502_, 0, v___x_2521_);
v_nextIt_2524_ = v___x_2502_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v___x_2521_);
v_nextIt_2524_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v_startInclusive_2525_; lean_object* v_endExclusive_2526_; 
v_startInclusive_2525_ = lean_ctor_get(v_slice_2522_, 0);
lean_inc(v_startInclusive_2525_);
v_endExclusive_2526_ = lean_ctor_get(v_slice_2522_, 1);
lean_inc(v_endExclusive_2526_);
lean_dec_ref(v_slice_2522_);
v_it_2492_ = v_nextIt_2524_;
v_startInclusive_2493_ = v_startInclusive_2525_;
v_endExclusive_2494_ = v_endExclusive_2526_;
goto v___jp_2491_;
}
}
}
else
{
lean_object* v___x_2528_; 
lean_del_object(v___x_2502_);
lean_dec(v_searcher_2500_);
v___x_2528_ = lean_box(1);
lean_inc(v___x_2488_);
v_it_2492_ = v___x_2528_;
v_startInclusive_2493_ = v_currPos_2499_;
v_endExclusive_2494_ = v___x_2488_;
goto v___jp_2491_;
}
}
}
else
{
lean_dec(v___x_2488_);
lean_dec_ref(v___x_2486_);
return v_b_2490_;
}
v___jp_2491_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_inc_ref(v___x_2486_);
v___x_2495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2486_);
lean_ctor_set(v___x_2495_, 1, v_startInclusive_2493_);
lean_ctor_set(v___x_2495_, 2, v_endExclusive_2494_);
v___x_2496_ = l_String_Slice_toString(v___x_2495_);
lean_dec_ref_known(v___x_2495_, 3);
v___x_2497_ = lean_array_push(v_b_2490_, v___x_2496_);
v___x_2498_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2486_, v___x_2487_, v___x_2488_, v_it_2492_, v___x_2497_);
return v___x_2498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2530_, lean_object* v___x_2531_, lean_object* v___x_2532_, lean_object* v_a_2533_, lean_object* v_b_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2530_, v___x_2531_, v___x_2532_, v_a_2533_, v_b_2534_);
lean_dec_ref(v___x_2531_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v___x_2539_; lean_object* v_infoState_2540_; uint8_t v_enabled_2541_; 
v___x_2539_ = lean_st_ref_get(v___y_2537_);
v_infoState_2540_ = lean_ctor_get(v___x_2539_, 8);
lean_inc_ref(v_infoState_2540_);
lean_dec(v___x_2539_);
v_enabled_2541_ = lean_ctor_get_uint8(v_infoState_2540_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2540_);
if (v_enabled_2541_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_dec_ref(v_t_2536_);
v___x_2542_ = lean_box(0);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; lean_object* v_infoState_2545_; lean_object* v_env_2546_; lean_object* v_messages_2547_; lean_object* v_scopes_2548_; lean_object* v_usedQuotCtxts_2549_; lean_object* v_nextMacroScope_2550_; lean_object* v_maxRecDepth_2551_; lean_object* v_ngen_2552_; lean_object* v_auxDeclNGen_2553_; lean_object* v_traceState_2554_; lean_object* v_snapshotTasks_2555_; lean_object* v_prevLinterStates_2556_; lean_object* v_codeQualityEntryTasks_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2579_; 
v___x_2544_ = lean_st_ref_take(v___y_2537_);
v_infoState_2545_ = lean_ctor_get(v___x_2544_, 8);
v_env_2546_ = lean_ctor_get(v___x_2544_, 0);
v_messages_2547_ = lean_ctor_get(v___x_2544_, 1);
v_scopes_2548_ = lean_ctor_get(v___x_2544_, 2);
v_usedQuotCtxts_2549_ = lean_ctor_get(v___x_2544_, 3);
v_nextMacroScope_2550_ = lean_ctor_get(v___x_2544_, 4);
v_maxRecDepth_2551_ = lean_ctor_get(v___x_2544_, 5);
v_ngen_2552_ = lean_ctor_get(v___x_2544_, 6);
v_auxDeclNGen_2553_ = lean_ctor_get(v___x_2544_, 7);
v_traceState_2554_ = lean_ctor_get(v___x_2544_, 9);
v_snapshotTasks_2555_ = lean_ctor_get(v___x_2544_, 10);
v_prevLinterStates_2556_ = lean_ctor_get(v___x_2544_, 11);
v_codeQualityEntryTasks_2557_ = lean_ctor_get(v___x_2544_, 12);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2559_ = v___x_2544_;
v_isShared_2560_ = v_isSharedCheck_2579_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2557_);
lean_inc(v_prevLinterStates_2556_);
lean_inc(v_snapshotTasks_2555_);
lean_inc(v_traceState_2554_);
lean_inc(v_infoState_2545_);
lean_inc(v_auxDeclNGen_2553_);
lean_inc(v_ngen_2552_);
lean_inc(v_maxRecDepth_2551_);
lean_inc(v_nextMacroScope_2550_);
lean_inc(v_usedQuotCtxts_2549_);
lean_inc(v_scopes_2548_);
lean_inc(v_messages_2547_);
lean_inc(v_env_2546_);
lean_dec(v___x_2544_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2579_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
uint8_t v_enabled_2561_; lean_object* v_assignment_2562_; lean_object* v_lazyAssignment_2563_; lean_object* v_trees_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2578_; 
v_enabled_2561_ = lean_ctor_get_uint8(v_infoState_2545_, sizeof(void*)*3);
v_assignment_2562_ = lean_ctor_get(v_infoState_2545_, 0);
v_lazyAssignment_2563_ = lean_ctor_get(v_infoState_2545_, 1);
v_trees_2564_ = lean_ctor_get(v_infoState_2545_, 2);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_infoState_2545_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2566_ = v_infoState_2545_;
v_isShared_2567_ = v_isSharedCheck_2578_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_trees_2564_);
lean_inc(v_lazyAssignment_2563_);
lean_inc(v_assignment_2562_);
lean_dec(v_infoState_2545_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2578_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2568_ = lean_box(0);
v___x_2569_ = l_Lean_PersistentArray_push___redArg(v_trees_2564_, v_t_2536_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 2, v___x_2569_);
v___x_2571_ = v___x_2566_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_assignment_2562_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_lazyAssignment_2563_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v___x_2569_);
lean_ctor_set_uint8(v_reuseFailAlloc_2577_, sizeof(void*)*3, v_enabled_2561_);
v___x_2571_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2573_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 8, v___x_2571_);
v___x_2573_ = v___x_2559_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_env_2546_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_messages_2547_);
lean_ctor_set(v_reuseFailAlloc_2576_, 2, v_scopes_2548_);
lean_ctor_set(v_reuseFailAlloc_2576_, 3, v_usedQuotCtxts_2549_);
lean_ctor_set(v_reuseFailAlloc_2576_, 4, v_nextMacroScope_2550_);
lean_ctor_set(v_reuseFailAlloc_2576_, 5, v_maxRecDepth_2551_);
lean_ctor_set(v_reuseFailAlloc_2576_, 6, v_ngen_2552_);
lean_ctor_set(v_reuseFailAlloc_2576_, 7, v_auxDeclNGen_2553_);
lean_ctor_set(v_reuseFailAlloc_2576_, 8, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2576_, 9, v_traceState_2554_);
lean_ctor_set(v_reuseFailAlloc_2576_, 10, v_snapshotTasks_2555_);
lean_ctor_set(v_reuseFailAlloc_2576_, 11, v_prevLinterStates_2556_);
lean_ctor_set(v_reuseFailAlloc_2576_, 12, v_codeQualityEntryTasks_2557_);
v___x_2573_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_st_ref_put(v___y_2537_, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2568_);
return v___x_2575_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2580_, v___y_2581_);
lean_dec(v___y_2581_);
return v_res_2583_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_unsigned_to_nat(32u);
v___x_2585_ = lean_mk_empty_array_with_capacity(v___x_2584_);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
return v___x_2586_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2587_ = ((size_t)5ULL);
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_unsigned_to_nat(32u);
v___x_2590_ = lean_mk_empty_array_with_capacity(v___x_2589_);
v___x_2591_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2592_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
lean_ctor_set(v___x_2592_, 1, v___x_2590_);
lean_ctor_set(v___x_2592_, 2, v___x_2588_);
lean_ctor_set(v___x_2592_, 3, v___x_2588_);
lean_ctor_set_usize(v___x_2592_, 4, v___x_2587_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v___x_2597_; lean_object* v_infoState_2598_; uint8_t v_enabled_2599_; 
v___x_2597_ = lean_st_ref_get(v___y_2595_);
v_infoState_2598_ = lean_ctor_get(v___x_2597_, 8);
lean_inc_ref(v_infoState_2598_);
lean_dec(v___x_2597_);
v_enabled_2599_ = lean_ctor_get_uint8(v_infoState_2598_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2598_);
if (v_enabled_2599_ == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v_t_2593_);
v___x_2600_ = lean_box(0);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2603_, 0, v_t_2593_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2603_, v___y_2595_);
return v___x_2604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v___x_2610_, lean_object* v_edited_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v_fst_2614_; lean_object* v_snd_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2639_; 
v_fst_2614_ = lean_ctor_get(v_a_2613_, 0);
v_snd_2615_ = lean_ctor_get(v_a_2613_, 1);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_a_2613_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2617_ = v_a_2613_;
v_isShared_2618_ = v_isSharedCheck_2639_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_snd_2615_);
lean_inc(v_fst_2614_);
lean_dec(v_a_2613_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2639_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
uint8_t v___x_2619_; 
v___x_2619_ = lean_nat_dec_lt(v_snd_2615_, v___x_2610_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2621_; 
if (v_isShared_2618_ == 0)
{
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_fst_2614_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_snd_2615_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2623_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2624_ = lean_array_get_borrowed(v___x_2623_, v_edited_2611_, v_snd_2615_);
v___x_2625_ = lean_string_dec_eq(v___x_2624_, v_a_2612_);
if (v___x_2625_ == 0)
{
uint8_t v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2626_ = 0;
v___x_2627_ = lean_box(v___x_2626_);
lean_inc(v___x_2624_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 1, v___x_2624_);
lean_ctor_set(v___x_2617_, 0, v___x_2627_);
v___x_2629_ = v___x_2617_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v___x_2624_);
v___x_2629_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2630_ = lean_array_push(v_fst_2614_, v___x_2629_);
v___x_2631_ = lean_unsigned_to_nat(1u);
v___x_2632_ = lean_nat_add(v_snd_2615_, v___x_2631_);
lean_dec(v_snd_2615_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2630_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v_a_2613_ = v___x_2633_;
goto _start;
}
}
else
{
lean_object* v___x_2637_; 
if (v_isShared_2618_ == 0)
{
v___x_2637_ = v___x_2617_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_fst_2614_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_snd_2615_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v___x_2640_, lean_object* v_edited_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2640_, v_edited_2641_, v_a_2642_, v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec_ref(v_edited_2641_);
lean_dec(v___x_2640_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(lean_object* v___x_2645_, lean_object* v_original_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_fst_2649_; lean_object* v_snd_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2674_; 
v_fst_2649_ = lean_ctor_get(v_a_2648_, 0);
v_snd_2650_ = lean_ctor_get(v_a_2648_, 1);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_a_2648_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2652_ = v_a_2648_;
v_isShared_2653_ = v_isSharedCheck_2674_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_snd_2650_);
lean_inc(v_fst_2649_);
lean_dec(v_a_2648_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2674_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
uint8_t v___x_2654_; 
v___x_2654_ = lean_nat_dec_lt(v_snd_2650_, v___x_2645_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2656_; 
if (v_isShared_2653_ == 0)
{
v___x_2656_ = v___x_2652_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_fst_2649_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_snd_2650_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2658_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2659_ = lean_array_get_borrowed(v___x_2658_, v_original_2646_, v_snd_2650_);
v___x_2660_ = lean_string_dec_eq(v___x_2659_, v_a_2647_);
if (v___x_2660_ == 0)
{
uint8_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2661_ = 1;
v___x_2662_ = lean_box(v___x_2661_);
lean_inc(v___x_2659_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 1, v___x_2659_);
lean_ctor_set(v___x_2652_, 0, v___x_2662_);
v___x_2664_ = v___x_2652_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v___x_2659_);
v___x_2664_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2665_ = lean_array_push(v_fst_2649_, v___x_2664_);
v___x_2666_ = lean_unsigned_to_nat(1u);
v___x_2667_ = lean_nat_add(v_snd_2650_, v___x_2666_);
lean_dec(v_snd_2650_);
v___x_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2665_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v_a_2648_ = v___x_2668_;
goto _start;
}
}
else
{
lean_object* v___x_2672_; 
if (v_isShared_2653_ == 0)
{
v___x_2672_ = v___x_2652_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_fst_2649_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_snd_2650_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg___boxed(lean_object* v___x_2675_, lean_object* v_original_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2675_, v_original_2676_, v_a_2677_, v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec_ref(v_original_2676_);
lean_dec(v___x_2675_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v___x_2680_, lean_object* v_original_2681_, lean_object* v___x_2682_, lean_object* v_edited_2683_, lean_object* v_as_2684_, size_t v_sz_2685_, size_t v_i_2686_, lean_object* v_b_2687_){
_start:
{
uint8_t v___x_2688_; 
v___x_2688_ = lean_usize_dec_lt(v_i_2686_, v_sz_2685_);
if (v___x_2688_ == 0)
{
return v_b_2687_;
}
else
{
lean_object* v_snd_2689_; lean_object* v_fst_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2737_; 
v_snd_2689_ = lean_ctor_get(v_b_2687_, 1);
v_fst_2690_ = lean_ctor_get(v_b_2687_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_b_2687_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2692_ = v_b_2687_;
v_isShared_2693_ = v_isSharedCheck_2737_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_snd_2689_);
lean_inc(v_fst_2690_);
lean_dec(v_b_2687_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2737_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_fst_2694_; lean_object* v_snd_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2736_; 
v_fst_2694_ = lean_ctor_get(v_snd_2689_, 0);
v_snd_2695_ = lean_ctor_get(v_snd_2689_, 1);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_snd_2689_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2697_ = v_snd_2689_;
v_isShared_2698_ = v_isSharedCheck_2736_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_snd_2695_);
lean_inc(v_fst_2694_);
lean_dec(v_snd_2689_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2736_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v_a_2699_; lean_object* v___x_2701_; 
v_a_2699_ = lean_array_uget_borrowed(v_as_2684_, v_i_2686_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v_fst_2694_);
lean_ctor_set(v___x_2697_, 0, v_fst_2690_);
v___x_2701_ = v___x_2697_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_fst_2690_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_fst_2694_);
v___x_2701_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; lean_object* v_fst_2703_; lean_object* v_snd_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2734_; 
v___x_2702_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2680_, v_original_2681_, v_a_2699_, v___x_2701_);
v_fst_2703_ = lean_ctor_get(v___x_2702_, 0);
v_snd_2704_ = lean_ctor_get(v___x_2702_, 1);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2706_ = v___x_2702_;
v_isShared_2707_ = v_isSharedCheck_2734_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_snd_2704_);
lean_inc(v_fst_2703_);
lean_dec(v___x_2702_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2734_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 1, v_snd_2695_);
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_fst_2703_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_snd_2695_);
v___x_2709_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; lean_object* v_fst_2711_; lean_object* v_snd_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2732_; 
v___x_2710_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2682_, v_edited_2683_, v_a_2699_, v___x_2709_);
v_fst_2711_ = lean_ctor_get(v___x_2710_, 0);
v_snd_2712_ = lean_ctor_get(v___x_2710_, 1);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2714_ = v___x_2710_;
v_isShared_2715_ = v_isSharedCheck_2732_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_snd_2712_);
lean_inc(v_fst_2711_);
lean_dec(v___x_2710_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2732_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2716_ = 2;
v___x_2717_ = lean_box(v___x_2716_);
lean_inc(v_a_2699_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 1, v_a_2699_);
lean_ctor_set(v___x_2714_, 0, v___x_2717_);
v___x_2719_ = v___x_2714_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2717_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_a_2699_);
v___x_2719_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2720_ = lean_array_push(v_fst_2711_, v___x_2719_);
v___x_2721_ = lean_unsigned_to_nat(1u);
v___x_2722_ = lean_nat_add(v_snd_2704_, v___x_2721_);
lean_dec(v_snd_2704_);
v___x_2723_ = lean_nat_add(v_snd_2712_, v___x_2721_);
lean_dec(v_snd_2712_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 1, v___x_2723_);
lean_ctor_set(v___x_2692_, 0, v___x_2722_);
v___x_2725_ = v___x_2692_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
lean_object* v___x_2726_; size_t v___x_2727_; size_t v___x_2728_; 
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2720_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = ((size_t)1ULL);
v___x_2728_ = lean_usize_add(v_i_2686_, v___x_2727_);
v_i_2686_ = v___x_2728_;
v_b_2687_ = v___x_2726_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v___x_2738_, lean_object* v_original_2739_, lean_object* v___x_2740_, lean_object* v_edited_2741_, lean_object* v_as_2742_, lean_object* v_sz_2743_, lean_object* v_i_2744_, lean_object* v_b_2745_){
_start:
{
size_t v_sz_boxed_2746_; size_t v_i_boxed_2747_; lean_object* v_res_2748_; 
v_sz_boxed_2746_ = lean_unbox_usize(v_sz_2743_);
lean_dec(v_sz_2743_);
v_i_boxed_2747_ = lean_unbox_usize(v_i_2744_);
lean_dec(v_i_2744_);
v_res_2748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2738_, v_original_2739_, v___x_2740_, v_edited_2741_, v_as_2742_, v_sz_boxed_2746_, v_i_boxed_2747_, v_b_2745_);
lean_dec_ref(v_as_2742_);
lean_dec_ref(v_edited_2741_);
lean_dec(v___x_2740_);
lean_dec_ref(v_original_2739_);
lean_dec(v___x_2738_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v___x_2749_, lean_object* v_edited_2750_, lean_object* v___x_2751_, lean_object* v_original_2752_, lean_object* v_as_2753_, size_t v_sz_2754_, size_t v_i_2755_, lean_object* v_b_2756_){
_start:
{
uint8_t v___x_2757_; 
v___x_2757_ = lean_usize_dec_lt(v_i_2755_, v_sz_2754_);
if (v___x_2757_ == 0)
{
return v_b_2756_;
}
else
{
lean_object* v_snd_2758_; lean_object* v_fst_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2806_; 
v_snd_2758_ = lean_ctor_get(v_b_2756_, 1);
v_fst_2759_ = lean_ctor_get(v_b_2756_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_b_2756_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2761_ = v_b_2756_;
v_isShared_2762_ = v_isSharedCheck_2806_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_snd_2758_);
lean_inc(v_fst_2759_);
lean_dec(v_b_2756_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2806_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v_fst_2763_; lean_object* v_snd_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2805_; 
v_fst_2763_ = lean_ctor_get(v_snd_2758_, 0);
v_snd_2764_ = lean_ctor_get(v_snd_2758_, 1);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_snd_2758_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2766_ = v_snd_2758_;
v_isShared_2767_ = v_isSharedCheck_2805_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_snd_2764_);
lean_inc(v_fst_2763_);
lean_dec(v_snd_2758_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2805_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v_a_2768_; lean_object* v___x_2770_; 
v_a_2768_ = lean_array_uget_borrowed(v_as_2753_, v_i_2755_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 1, v_fst_2763_);
lean_ctor_set(v___x_2766_, 0, v_fst_2759_);
v___x_2770_ = v___x_2766_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_fst_2759_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_fst_2763_);
v___x_2770_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; lean_object* v_fst_2772_; lean_object* v_snd_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2803_; 
v___x_2771_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2751_, v_original_2752_, v_a_2768_, v___x_2770_);
v_fst_2772_ = lean_ctor_get(v___x_2771_, 0);
v_snd_2773_ = lean_ctor_get(v___x_2771_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2775_ = v___x_2771_;
v_isShared_2776_ = v_isSharedCheck_2803_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_snd_2773_);
lean_inc(v_fst_2772_);
lean_dec(v___x_2771_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2803_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 1, v_snd_2764_);
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_fst_2772_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_snd_2764_);
v___x_2778_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; lean_object* v_fst_2780_; lean_object* v_snd_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2801_; 
v___x_2779_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2749_, v_edited_2750_, v_a_2768_, v___x_2778_);
v_fst_2780_ = lean_ctor_get(v___x_2779_, 0);
v_snd_2781_ = lean_ctor_get(v___x_2779_, 1);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2783_ = v___x_2779_;
v_isShared_2784_ = v_isSharedCheck_2801_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_snd_2781_);
lean_inc(v_fst_2780_);
lean_dec(v___x_2779_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2801_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
uint8_t v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2785_ = 2;
v___x_2786_ = lean_box(v___x_2785_);
lean_inc(v_a_2768_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v_a_2768_);
lean_ctor_set(v___x_2783_, 0, v___x_2786_);
v___x_2788_ = v___x_2783_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_a_2768_);
v___x_2788_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2789_ = lean_array_push(v_fst_2780_, v___x_2788_);
v___x_2790_ = lean_unsigned_to_nat(1u);
v___x_2791_ = lean_nat_add(v_snd_2773_, v___x_2790_);
lean_dec(v_snd_2773_);
v___x_2792_ = lean_nat_add(v_snd_2781_, v___x_2790_);
lean_dec(v_snd_2781_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v___x_2792_);
lean_ctor_set(v___x_2761_, 0, v___x_2791_);
v___x_2794_ = v___x_2761_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; size_t v___x_2796_; size_t v___x_2797_; lean_object* v___x_2798_; 
v___x_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2789_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = ((size_t)1ULL);
v___x_2797_ = lean_usize_add(v_i_2755_, v___x_2796_);
v___x_2798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2751_, v_original_2752_, v___x_2749_, v_edited_2750_, v_as_2753_, v_sz_2754_, v___x_2797_, v___x_2795_);
return v___x_2798_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v___x_2807_, lean_object* v_edited_2808_, lean_object* v___x_2809_, lean_object* v_original_2810_, lean_object* v_as_2811_, lean_object* v_sz_2812_, lean_object* v_i_2813_, lean_object* v_b_2814_){
_start:
{
size_t v_sz_boxed_2815_; size_t v_i_boxed_2816_; lean_object* v_res_2817_; 
v_sz_boxed_2815_ = lean_unbox_usize(v_sz_2812_);
lean_dec(v_sz_2812_);
v_i_boxed_2816_ = lean_unbox_usize(v_i_2813_);
lean_dec(v_i_2813_);
v_res_2817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_2807_, v_edited_2808_, v___x_2809_, v_original_2810_, v_as_2811_, v_sz_boxed_2815_, v_i_boxed_2816_, v_b_2814_);
lean_dec_ref(v_as_2811_);
lean_dec_ref(v_original_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v_edited_2808_);
lean_dec(v___x_2807_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_2818_, lean_object* v_original_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v_fst_2821_; lean_object* v_snd_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2841_; 
v_fst_2821_ = lean_ctor_get(v_a_2820_, 0);
v_snd_2822_ = lean_ctor_get(v_a_2820_, 1);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_a_2820_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2824_ = v_a_2820_;
v_isShared_2825_ = v_isSharedCheck_2841_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_snd_2822_);
lean_inc(v_fst_2821_);
lean_dec(v_a_2820_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2841_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
uint8_t v___x_2826_; 
v___x_2826_ = lean_nat_dec_lt(v_snd_2822_, v___x_2818_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2828_; 
if (v_isShared_2825_ == 0)
{
v___x_2828_ = v___x_2824_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_fst_2821_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_snd_2822_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
else
{
uint8_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2830_ = 1;
v___x_2831_ = lean_array_fget_borrowed(v_original_2819_, v_snd_2822_);
v___x_2832_ = lean_box(v___x_2830_);
lean_inc(v___x_2831_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 1, v___x_2831_);
lean_ctor_set(v___x_2824_, 0, v___x_2832_);
v___x_2834_ = v___x_2824_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v___x_2831_);
v___x_2834_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2835_ = lean_array_push(v_fst_2821_, v___x_2834_);
v___x_2836_ = lean_unsigned_to_nat(1u);
v___x_2837_ = lean_nat_add(v_snd_2822_, v___x_2836_);
lean_dec(v_snd_2822_);
v___x_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2835_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v_a_2820_ = v___x_2838_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_2842_, lean_object* v_original_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_2842_, v_original_2843_, v_a_2844_);
lean_dec_ref(v_original_2843_);
lean_dec(v___x_2842_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_2846_, size_t v_i_2847_, lean_object* v_bs_2848_){
_start:
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_usize_dec_lt(v_i_2847_, v_sz_2846_);
if (v___x_2849_ == 0)
{
return v_bs_2848_;
}
else
{
lean_object* v_v_2850_; lean_object* v___x_2851_; lean_object* v_bs_x27_2852_; uint8_t v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; size_t v___x_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
v_v_2850_ = lean_array_uget(v_bs_2848_, v_i_2847_);
v___x_2851_ = lean_unsigned_to_nat(0u);
v_bs_x27_2852_ = lean_array_uset(v_bs_2848_, v_i_2847_, v___x_2851_);
v___x_2853_ = 0;
v___x_2854_ = lean_box(v___x_2853_);
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v_v_2850_);
v___x_2856_ = ((size_t)1ULL);
v___x_2857_ = lean_usize_add(v_i_2847_, v___x_2856_);
v___x_2858_ = lean_array_uset(v_bs_x27_2852_, v_i_2847_, v___x_2855_);
v_i_2847_ = v___x_2857_;
v_bs_2848_ = v___x_2858_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_2860_, lean_object* v_i_2861_, lean_object* v_bs_2862_){
_start:
{
size_t v_sz_boxed_2863_; size_t v_i_boxed_2864_; lean_object* v_res_2865_; 
v_sz_boxed_2863_ = lean_unbox_usize(v_sz_2860_);
lean_dec(v_sz_2860_);
v_i_boxed_2864_ = lean_unbox_usize(v_i_2861_);
lean_dec(v_i_2861_);
v_res_2865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_2863_, v_i_boxed_2864_, v_bs_2862_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_2866_, lean_object* v_edited_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v_fst_2869_; lean_object* v_snd_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2889_; 
v_fst_2869_ = lean_ctor_get(v_a_2868_, 0);
v_snd_2870_ = lean_ctor_get(v_a_2868_, 1);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_a_2868_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2872_ = v_a_2868_;
v_isShared_2873_ = v_isSharedCheck_2889_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_snd_2870_);
lean_inc(v_fst_2869_);
lean_dec(v_a_2868_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2889_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
uint8_t v___x_2874_; 
v___x_2874_ = lean_nat_dec_lt(v_snd_2870_, v___x_2866_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2876_; 
if (v_isShared_2873_ == 0)
{
v___x_2876_ = v___x_2872_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_fst_2869_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_snd_2870_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
else
{
uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2878_ = 0;
v___x_2879_ = lean_array_fget_borrowed(v_edited_2867_, v_snd_2870_);
v___x_2880_ = lean_box(v___x_2878_);
lean_inc(v___x_2879_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 1, v___x_2879_);
lean_ctor_set(v___x_2872_, 0, v___x_2880_);
v___x_2882_ = v___x_2872_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2880_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v___x_2879_);
v___x_2882_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2883_ = lean_array_push(v_fst_2869_, v___x_2882_);
v___x_2884_ = lean_unsigned_to_nat(1u);
v___x_2885_ = lean_nat_add(v_snd_2870_, v___x_2884_);
lean_dec(v_snd_2870_);
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2883_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v_a_2868_ = v___x_2886_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_2890_, lean_object* v_edited_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_2890_, v_edited_2891_, v_a_2892_);
lean_dec_ref(v_edited_2891_);
lean_dec(v___x_2890_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(lean_object* v_x_2894_, lean_object* v_x_2895_){
_start:
{
if (lean_obj_tag(v_x_2895_) == 0)
{
lean_inc(v_x_2894_);
return v_x_2894_;
}
else
{
lean_object* v_key_2896_; lean_object* v_value_2897_; lean_object* v_tail_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_key_2896_ = lean_ctor_get(v_x_2895_, 0);
v_value_2897_ = lean_ctor_get(v_x_2895_, 1);
v_tail_2898_ = lean_ctor_get(v_x_2895_, 2);
v___x_2899_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2894_, v_tail_2898_);
lean_inc(v_value_2897_);
lean_inc(v_key_2896_);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v_key_2896_);
lean_ctor_set(v___x_2900_, 1, v_value_2897_);
v___x_2901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
lean_ctor_set(v___x_2901_, 1, v___x_2899_);
return v___x_2901_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17___boxed(lean_object* v_x_2902_, lean_object* v_x_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2902_, v_x_2903_);
lean_dec(v_x_2903_);
lean_dec(v_x_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(lean_object* v_as_2905_, size_t v_i_2906_, size_t v_stop_2907_, lean_object* v_b_2908_){
_start:
{
uint8_t v___x_2909_; 
v___x_2909_ = lean_usize_dec_eq(v_i_2906_, v_stop_2907_);
if (v___x_2909_ == 0)
{
size_t v___x_2910_; size_t v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2910_ = ((size_t)1ULL);
v___x_2911_ = lean_usize_sub(v_i_2906_, v___x_2910_);
v___x_2912_ = lean_array_uget_borrowed(v_as_2905_, v___x_2911_);
v___x_2913_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_b_2908_, v___x_2912_);
lean_dec(v_b_2908_);
v_i_2906_ = v___x_2911_;
v_b_2908_ = v___x_2913_;
goto _start;
}
else
{
return v_b_2908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18___boxed(lean_object* v_as_2915_, lean_object* v_i_2916_, lean_object* v_stop_2917_, lean_object* v_b_2918_){
_start:
{
size_t v_i_boxed_2919_; size_t v_stop_boxed_2920_; lean_object* v_res_2921_; 
v_i_boxed_2919_ = lean_unbox_usize(v_i_2916_);
lean_dec(v_i_2916_);
v_stop_boxed_2920_ = lean_unbox_usize(v_stop_2917_);
lean_dec(v_stop_2917_);
v_res_2921_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_as_2915_, v_i_boxed_2919_, v_stop_boxed_2920_, v_b_2918_);
lean_dec_ref(v_as_2915_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(lean_object* v_left_2922_, lean_object* v_right_2923_, lean_object* v_pref_2924_){
_start:
{
lean_object* v_start_2925_; lean_object* v_stop_2926_; lean_object* v_i_2927_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v_start_2925_ = lean_ctor_get(v_left_2922_, 1);
v_stop_2926_ = lean_ctor_get(v_left_2922_, 2);
v_i_2927_ = lean_array_get_size(v_pref_2924_);
v___x_2933_ = lean_nat_sub(v_stop_2926_, v_start_2925_);
v___x_2934_ = lean_nat_dec_lt(v_i_2927_, v___x_2933_);
lean_dec(v___x_2933_);
if (v___x_2934_ == 0)
{
goto v___jp_2928_;
}
else
{
lean_object* v_start_2935_; lean_object* v_stop_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v_start_2935_ = lean_ctor_get(v_right_2923_, 1);
v_stop_2936_ = lean_ctor_get(v_right_2923_, 2);
v___x_2937_ = lean_nat_sub(v_stop_2936_, v_start_2935_);
v___x_2938_ = lean_nat_dec_lt(v_i_2927_, v___x_2937_);
lean_dec(v___x_2937_);
if (v___x_2938_ == 0)
{
goto v___jp_2928_;
}
else
{
lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2939_ = l_Subarray_get___redArg(v_left_2922_, v_i_2927_);
v___x_2940_ = l_Subarray_get___redArg(v_right_2923_, v_i_2927_);
v___x_2941_ = lean_string_dec_eq(v___x_2939_, v___x_2940_);
lean_dec(v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_dec(v___x_2939_);
v___x_2942_ = l_Subarray_drop___redArg(v_left_2922_, v_i_2927_);
v___x_2943_ = l_Subarray_drop___redArg(v_right_2923_, v_i_2927_);
v___x_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v_pref_2924_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
return v___x_2945_;
}
else
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_array_push(v_pref_2924_, v___x_2939_);
v_pref_2924_ = v___x_2946_;
goto _start;
}
}
}
v___jp_2928_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2929_ = l_Subarray_drop___redArg(v_left_2922_, v_i_2927_);
v___x_2930_ = l_Subarray_drop___redArg(v_right_2923_, v_i_2927_);
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2929_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v_pref_2924_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
return v___x_2932_;
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
lean_object* v_start_3291_; lean_object* v_stop_3292_; lean_object* v___x_3293_; uint8_t v___x_3307_; 
v_start_3291_ = lean_ctor_get(v_left_3288_, 1);
v_stop_3292_ = lean_ctor_get(v_left_3288_, 2);
v___x_3293_ = lean_nat_sub(v_stop_3292_, v_start_3291_);
v___x_3307_ = lean_nat_dec_lt(v_i_3290_, v___x_3293_);
if (v___x_3307_ == 0)
{
goto v___jp_3294_;
}
else
{
lean_object* v_start_3308_; lean_object* v_stop_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v_start_3308_ = lean_ctor_get(v_right_3289_, 1);
v_stop_3309_ = lean_ctor_get(v_right_3289_, 2);
v___x_3310_ = lean_nat_sub(v_stop_3309_, v_start_3308_);
v___x_3311_ = lean_nat_dec_lt(v_i_3290_, v___x_3310_);
if (v___x_3311_ == 0)
{
lean_dec(v___x_3310_);
goto v___jp_3294_;
}
else
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; uint8_t v___x_3319_; 
v___x_3312_ = lean_nat_sub(v___x_3293_, v_i_3290_);
lean_dec(v___x_3293_);
v___x_3313_ = lean_unsigned_to_nat(1u);
v___x_3314_ = lean_nat_sub(v___x_3312_, v___x_3313_);
v___x_3315_ = l_Subarray_get___redArg(v_left_3288_, v___x_3314_);
lean_dec(v___x_3314_);
v___x_3316_ = lean_nat_sub(v___x_3310_, v_i_3290_);
lean_dec(v___x_3310_);
v___x_3317_ = lean_nat_sub(v___x_3316_, v___x_3313_);
v___x_3318_ = l_Subarray_get___redArg(v_right_3289_, v___x_3317_);
lean_dec(v___x_3317_);
v___x_3319_ = lean_string_dec_eq(v___x_3315_, v___x_3318_);
lean_dec(v___x_3318_);
lean_dec(v___x_3315_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_dec(v_i_3290_);
lean_inc_ref(v_left_3288_);
v___x_3320_ = l_Subarray_take___redArg(v_left_3288_, v___x_3312_);
v___x_3321_ = l_Subarray_take___redArg(v_right_3289_, v___x_3316_);
lean_dec(v___x_3316_);
v___x_3322_ = l_Subarray_drop___redArg(v_left_3288_, v___x_3312_);
lean_dec(v___x_3312_);
v___x_3323_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3324_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3322_, v___x_3323_);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3321_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3320_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
return v___x_3326_;
}
else
{
lean_object* v___x_3327_; 
lean_dec(v___x_3316_);
lean_dec(v___x_3312_);
v___x_3327_ = lean_nat_add(v_i_3290_, v___x_3313_);
lean_dec(v_i_3290_);
v_i_3290_ = v___x_3327_;
goto _start;
}
}
}
v___jp_3294_:
{
lean_object* v_start_3295_; lean_object* v_stop_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v_start_3295_ = lean_ctor_get(v_right_3289_, 1);
v_stop_3296_ = lean_ctor_get(v_right_3289_, 2);
v___x_3297_ = lean_nat_sub(v___x_3293_, v_i_3290_);
lean_dec(v___x_3293_);
lean_inc_ref(v_left_3288_);
v___x_3298_ = l_Subarray_take___redArg(v_left_3288_, v___x_3297_);
v___x_3299_ = lean_nat_sub(v_stop_3296_, v_start_3295_);
v___x_3300_ = lean_nat_sub(v___x_3299_, v_i_3290_);
lean_dec(v_i_3290_);
lean_dec(v___x_3299_);
v___x_3301_ = l_Subarray_take___redArg(v_right_3289_, v___x_3300_);
lean_dec(v___x_3300_);
v___x_3302_ = l_Subarray_drop___redArg(v_left_3288_, v___x_3297_);
lean_dec(v___x_3297_);
v___x_3303_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3304_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3302_, v___x_3303_);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3301_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3298_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
return v___x_3306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(lean_object* v_left_3329_, lean_object* v_right_3330_){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = lean_unsigned_to_nat(0u);
v___x_3332_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(v_left_3329_, v_right_3330_, v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = lean_box(0);
v___x_3334_ = lean_unsigned_to_nat(16u);
v___x_3335_ = lean_mk_array(v___x_3334_, v___x_3333_);
return v___x_3335_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v_hist_3338_; 
v___x_3336_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0);
v___x_3337_ = lean_unsigned_to_nat(0u);
v_hist_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3338_, 0, v___x_3337_);
lean_ctor_set(v_hist_3338_, 1, v___x_3336_);
return v_hist_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_left_3339_, lean_object* v_right_3340_){
_start:
{
lean_object* v___x_3341_; lean_object* v_snd_3342_; lean_object* v_fst_3343_; lean_object* v_fst_3344_; lean_object* v_snd_3345_; lean_object* v___x_3346_; lean_object* v_snd_3347_; lean_object* v_fst_3348_; lean_object* v_fst_3349_; lean_object* v_snd_3350_; lean_object* v_start_3351_; lean_object* v_stop_3352_; lean_object* v___x_3353_; lean_object* v_hist_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v_start_3357_; lean_object* v_stop_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v_buckets_3361_; lean_object* v___x_3362_; lean_object* v___y_3364_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3341_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(v_left_3339_, v_right_3340_);
v_snd_3342_ = lean_ctor_get(v___x_3341_, 1);
lean_inc(v_snd_3342_);
v_fst_3343_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_fst_3343_);
lean_dec_ref(v___x_3341_);
v_fst_3344_ = lean_ctor_get(v_snd_3342_, 0);
lean_inc(v_fst_3344_);
v_snd_3345_ = lean_ctor_get(v_snd_3342_, 1);
lean_inc(v_snd_3345_);
lean_dec(v_snd_3342_);
v___x_3346_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(v_fst_3344_, v_snd_3345_);
v_snd_3347_ = lean_ctor_get(v___x_3346_, 1);
lean_inc(v_snd_3347_);
v_fst_3348_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_fst_3348_);
lean_dec_ref(v___x_3346_);
v_fst_3349_ = lean_ctor_get(v_snd_3347_, 0);
lean_inc(v_fst_3349_);
v_snd_3350_ = lean_ctor_get(v_snd_3347_, 1);
lean_inc(v_snd_3350_);
lean_dec(v_snd_3347_);
v_start_3351_ = lean_ctor_get(v_fst_3348_, 1);
v_stop_3352_ = lean_ctor_get(v_fst_3348_, 2);
v___x_3353_ = lean_unsigned_to_nat(0u);
v_hist_3354_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1);
v___x_3355_ = lean_nat_sub(v_stop_3352_, v_start_3351_);
v___x_3356_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v___x_3355_, v_fst_3349_, v___x_3355_, v_fst_3348_, v___x_3353_, v_hist_3354_);
v_start_3357_ = lean_ctor_get(v_fst_3349_, 1);
v_stop_3358_ = lean_ctor_get(v_fst_3349_, 2);
v___x_3359_ = lean_nat_sub(v_stop_3358_, v_start_3357_);
v___x_3360_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v___x_3359_, v___x_3359_, v_fst_3349_, v___x_3355_, v___x_3353_, v___x_3356_);
lean_dec(v___x_3355_);
lean_dec(v___x_3359_);
v_buckets_3361_ = lean_ctor_get(v___x_3360_, 1);
lean_inc_ref(v_buckets_3361_);
lean_dec_ref(v___x_3360_);
v___x_3362_ = lean_box(0);
v___x_3390_ = lean_box(0);
v___x_3391_ = lean_array_get_size(v_buckets_3361_);
v___x_3392_ = lean_nat_dec_lt(v___x_3353_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_dec_ref(v_buckets_3361_);
v___y_3364_ = v___x_3390_;
goto v___jp_3363_;
}
else
{
size_t v___x_3393_; size_t v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = lean_usize_of_nat(v___x_3391_);
v___x_3394_ = ((size_t)0ULL);
v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_buckets_3361_, v___x_3393_, v___x_3394_, v___x_3390_);
lean_dec_ref(v_buckets_3361_);
v___y_3364_ = v___x_3395_;
goto v___jp_3363_;
}
v___jp_3363_:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v___y_3364_, v___x_3362_);
lean_dec(v___y_3364_);
if (lean_obj_tag(v___x_3365_) == 1)
{
lean_object* v_val_3366_; lean_object* v_snd_3367_; lean_object* v_snd_3368_; lean_object* v_fst_3369_; lean_object* v_fst_3370_; lean_object* v_snd_3371_; lean_object* v___x_3372_; lean_object* v_fst_3373_; lean_object* v_snd_3374_; lean_object* v___x_3375_; lean_object* v_fst_3376_; lean_object* v_snd_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_val_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_val_3366_);
lean_dec_ref_known(v___x_3365_, 1);
v_snd_3367_ = lean_ctor_get(v_val_3366_, 1);
lean_inc(v_snd_3367_);
lean_dec(v_val_3366_);
v_snd_3368_ = lean_ctor_get(v_snd_3367_, 1);
lean_inc(v_snd_3368_);
v_fst_3369_ = lean_ctor_get(v_snd_3367_, 0);
lean_inc(v_fst_3369_);
lean_dec(v_snd_3367_);
v_fst_3370_ = lean_ctor_get(v_snd_3368_, 0);
lean_inc(v_fst_3370_);
v_snd_3371_ = lean_ctor_get(v_snd_3368_, 1);
lean_inc(v_snd_3371_);
lean_dec(v_snd_3368_);
v___x_3372_ = l_Subarray_split___redArg(v_fst_3348_, v_fst_3370_);
lean_dec(v_fst_3370_);
v_fst_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_fst_3373_);
v_snd_3374_ = lean_ctor_get(v___x_3372_, 1);
lean_inc(v_snd_3374_);
lean_dec_ref(v___x_3372_);
v___x_3375_ = l_Subarray_split___redArg(v_fst_3349_, v_snd_3371_);
lean_dec(v_snd_3371_);
v_fst_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_fst_3376_);
v_snd_3377_ = lean_ctor_get(v___x_3375_, 1);
lean_inc(v_snd_3377_);
lean_dec_ref(v___x_3375_);
v___x_3378_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_fst_3373_, v_fst_3376_);
v___x_3379_ = l_Array_append___redArg(v_fst_3343_, v___x_3378_);
lean_dec_ref(v___x_3378_);
v___x_3380_ = lean_unsigned_to_nat(1u);
v___x_3381_ = lean_mk_empty_array_with_capacity(v___x_3380_);
v___x_3382_ = lean_array_push(v___x_3381_, v_fst_3369_);
v___x_3383_ = l_Array_append___redArg(v___x_3379_, v___x_3382_);
lean_dec_ref(v___x_3382_);
v___x_3384_ = l_Subarray_drop___redArg(v_snd_3374_, v___x_3380_);
v___x_3385_ = l_Subarray_drop___redArg(v_snd_3377_, v___x_3380_);
v___x_3386_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3384_, v___x_3385_);
v___x_3387_ = l_Array_append___redArg(v___x_3383_, v___x_3386_);
lean_dec_ref(v___x_3386_);
v___x_3388_ = l_Array_append___redArg(v___x_3387_, v_snd_3350_);
lean_dec(v_snd_3350_);
return v___x_3388_;
}
else
{
lean_object* v___x_3389_; 
lean_dec(v___x_3365_);
lean_dec(v_fst_3349_);
lean_dec(v_fst_3348_);
v___x_3389_ = l_Array_append___redArg(v_fst_3343_, v_snd_3350_);
lean_dec(v_snd_3350_);
return v___x_3389_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3396_, size_t v_i_3397_, lean_object* v_bs_3398_){
_start:
{
uint8_t v___x_3399_; 
v___x_3399_ = lean_usize_dec_lt(v_i_3397_, v_sz_3396_);
if (v___x_3399_ == 0)
{
return v_bs_3398_;
}
else
{
lean_object* v_v_3400_; lean_object* v___x_3401_; lean_object* v_bs_x27_3402_; uint8_t v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; size_t v___x_3406_; size_t v___x_3407_; lean_object* v___x_3408_; 
v_v_3400_ = lean_array_uget(v_bs_3398_, v_i_3397_);
v___x_3401_ = lean_unsigned_to_nat(0u);
v_bs_x27_3402_ = lean_array_uset(v_bs_3398_, v_i_3397_, v___x_3401_);
v___x_3403_ = 1;
v___x_3404_ = lean_box(v___x_3403_);
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v_v_3400_);
v___x_3406_ = ((size_t)1ULL);
v___x_3407_ = lean_usize_add(v_i_3397_, v___x_3406_);
v___x_3408_ = lean_array_uset(v_bs_x27_3402_, v_i_3397_, v___x_3405_);
v_i_3397_ = v___x_3407_;
v_bs_3398_ = v___x_3408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3410_, lean_object* v_i_3411_, lean_object* v_bs_3412_){
_start:
{
size_t v_sz_boxed_3413_; size_t v_i_boxed_3414_; lean_object* v_res_3415_; 
v_sz_boxed_3413_ = lean_unbox_usize(v_sz_3410_);
lean_dec(v_sz_3410_);
v_i_boxed_3414_ = lean_unbox_usize(v_i_3411_);
lean_dec(v_i_3411_);
v_res_3415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3413_, v_i_boxed_3414_, v_bs_3412_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3423_, lean_object* v_edited_3424_){
_start:
{
lean_object* v_i_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v_i_3425_ = lean_unsigned_to_nat(0u);
v___x_3426_ = lean_array_get_size(v_original_3423_);
v___x_3427_ = lean_nat_dec_lt(v_i_3425_, v___x_3426_);
if (v___x_3427_ == 0)
{
size_t v_sz_3428_; size_t v___x_3429_; lean_object* v___x_3430_; 
lean_dec_ref(v_original_3423_);
v_sz_3428_ = lean_array_size(v_edited_3424_);
v___x_3429_ = ((size_t)0ULL);
v___x_3430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3428_, v___x_3429_, v_edited_3424_);
return v___x_3430_;
}
else
{
lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3431_ = lean_array_get_size(v_edited_3424_);
v___x_3432_ = lean_nat_dec_lt(v_i_3425_, v___x_3431_);
if (v___x_3432_ == 0)
{
size_t v_sz_3433_; size_t v___x_3434_; lean_object* v___x_3435_; 
lean_dec_ref(v_edited_3424_);
v_sz_3433_ = lean_array_size(v_original_3423_);
v___x_3434_ = ((size_t)0ULL);
v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3433_, v___x_3434_, v_original_3423_);
return v___x_3435_;
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v_ds_3438_; lean_object* v___x_3439_; size_t v_sz_3440_; size_t v___x_3441_; lean_object* v___x_3442_; lean_object* v_snd_3443_; lean_object* v_fst_3444_; lean_object* v_fst_3445_; lean_object* v_snd_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3465_; 
lean_inc_ref(v_original_3423_);
v___x_3436_ = l_Array_toSubarray___redArg(v_original_3423_, v_i_3425_, v___x_3426_);
lean_inc_ref(v_edited_3424_);
v___x_3437_ = l_Array_toSubarray___redArg(v_edited_3424_, v_i_3425_, v___x_3431_);
v_ds_3438_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3436_, v___x_3437_);
v___x_3439_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3440_ = lean_array_size(v_ds_3438_);
v___x_3441_ = ((size_t)0ULL);
v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_3431_, v_edited_3424_, v___x_3426_, v_original_3423_, v_ds_3438_, v_sz_3440_, v___x_3441_, v___x_3439_);
lean_dec_ref(v_ds_3438_);
v_snd_3443_ = lean_ctor_get(v___x_3442_, 1);
lean_inc(v_snd_3443_);
v_fst_3444_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_fst_3444_);
lean_dec_ref(v___x_3442_);
v_fst_3445_ = lean_ctor_get(v_snd_3443_, 0);
v_snd_3446_ = lean_ctor_get(v_snd_3443_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_snd_3443_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3448_ = v_snd_3443_;
v_isShared_3449_ = v_isSharedCheck_3465_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_snd_3446_);
lean_inc(v_fst_3445_);
lean_dec(v_snd_3443_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3465_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 1, v_fst_3445_);
lean_ctor_set(v___x_3448_, 0, v_fst_3444_);
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_fst_3444_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_fst_3445_);
v___x_3451_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3452_; lean_object* v_fst_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3462_; 
v___x_3452_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3426_, v_original_3423_, v___x_3451_);
lean_dec_ref(v_original_3423_);
v_fst_3453_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3462_ == 0)
{
lean_object* v_unused_3463_; 
v_unused_3463_ = lean_ctor_get(v___x_3452_, 1);
lean_dec(v_unused_3463_);
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3462_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_fst_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3462_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 1, v_snd_3446_);
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_fst_3453_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_snd_3446_);
v___x_3458_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3459_; lean_object* v_fst_3460_; 
v___x_3459_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3431_, v_edited_3424_, v___x_3458_);
lean_dec_ref(v_edited_3424_);
v_fst_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_fst_3460_);
lean_dec_ref(v___x_3459_);
return v_fst_3460_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3466_, lean_object* v_x_3467_, lean_object* v_x_3468_){
_start:
{
if (lean_obj_tag(v_x_3467_) == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = l_List_reverse___redArg(v_x_3468_);
v___x_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
else
{
lean_object* v_head_3472_; lean_object* v_tail_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3482_; 
v_head_3472_ = lean_ctor_get(v_x_3467_, 0);
v_tail_3473_ = lean_ctor_get(v_x_3467_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_x_3467_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3475_ = v_x_3467_;
v_isShared_3476_ = v_isSharedCheck_3482_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_tail_3473_);
lean_inc(v_head_3472_);
lean_dec(v_x_3467_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3482_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3477_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3472_, v___y_3466_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 1, v_x_3468_);
lean_ctor_set(v___x_3475_, 0, v___x_3477_);
v___x_3479_ = v___x_3475_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_x_3468_);
v___x_3479_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
v_x_3467_ = v_tail_3473_;
v_x_3468_ = v___x_3479_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3483_, lean_object* v_x_3484_, lean_object* v_x_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3483_, v_x_3484_, v_x_3485_);
lean_dec(v___y_3483_);
return v_res_3487_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3494_ = l_Lean_stringToMessageData(v___x_3493_);
return v___x_3494_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = l_Lean_MessageLog_empty;
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v___x_3508_; uint8_t v___x_3509_; 
v___x_3508_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
lean_inc(v_x_3504_);
v___x_3509_ = l_Lean_Syntax_isOfKind(v_x_3504_, v___x_3508_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_dec(v_x_3504_);
v___x_3510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3552_; lean_object* v___y_3617_; uint8_t v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; uint8_t v___y_3626_; uint8_t v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v_dc_x3f_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___x_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v___x_3511_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3760_ = lean_unsigned_to_nat(0u);
v___x_3761_ = l_Lean_Syntax_getArg(v_x_3504_, v___x_3760_);
v___x_3762_ = l_Lean_Syntax_isNone(v___x_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; uint8_t v___x_3764_; 
v___x_3763_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3761_);
v___x_3764_ = l_Lean_Syntax_matchesNull(v___x_3761_, v___x_3763_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; 
lean_dec(v___x_3761_);
lean_dec(v_x_3504_);
v___x_3765_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3765_;
}
else
{
lean_object* v_dc_x3f_3766_; 
v_dc_x3f_3766_ = l_Lean_Syntax_getArg(v___x_3761_, v___x_3760_);
lean_dec(v___x_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3769_; uint8_t v___x_3770_; 
v___x_3769_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3766_);
v___x_3770_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3766_, v___x_3769_);
if (v___x_3770_ == 0)
{
lean_object* v___x_3771_; 
lean_dec(v_dc_x3f_3766_);
lean_dec(v_x_3504_);
v___x_3771_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3771_;
}
else
{
goto v___jp_3767_;
}
}
else
{
goto v___jp_3767_;
}
v___jp_3767_:
{
lean_object* v___x_3768_; 
v___x_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3768_, 0, v_dc_x3f_3766_);
v_dc_x3f_3741_ = v___x_3768_;
v___y_3742_ = v_a_3505_;
v___y_3743_ = v_a_3506_;
goto v___jp_3740_;
}
}
}
else
{
lean_object* v___x_3772_; 
lean_dec(v___x_3761_);
v___x_3772_ = lean_box(0);
v_dc_x3f_3741_ = v___x_3772_;
v___y_3742_ = v_a_3505_;
v___y_3743_ = v_a_3506_;
goto v___jp_3740_;
}
v___jp_3512_:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3518_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3519_ = l_Lean_stringToMessageData(v___y_3517_);
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3516_, v___x_3520_, v___y_3515_, v___y_3513_);
lean_dec(v___y_3516_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3541_; 
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3541_ == 0)
{
lean_object* v_unused_3542_; 
v_unused_3542_ = lean_ctor_get(v___x_3521_, 0);
lean_dec(v_unused_3542_);
v___x_3523_ = v___x_3521_;
v_isShared_3524_ = v_isSharedCheck_3541_;
goto v_resetjp_3522_;
}
else
{
lean_dec(v___x_3521_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3541_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_Elab_Command_getRef___redArg(v___y_3515_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3530_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref_known(v___x_3525_, 1);
v___x_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3511_);
lean_ctor_set(v___x_3527_, 1, v___y_3514_);
v___x_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3528_, 0, v_a_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set_tag(v___x_3523_, 10);
lean_ctor_set(v___x_3523_, 0, v___x_3528_);
v___x_3530_ = v___x_3523_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3530_, v___y_3515_, v___y_3513_);
return v___x_3531_;
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_del_object(v___x_3523_);
lean_dec_ref(v___y_3514_);
v_a_3533_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3525_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3525_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3514_);
return v___x_3521_;
}
}
v___jp_3543_:
{
if (v___y_3552_ == 0)
{
lean_object* v___x_3553_; lean_object* v_env_3554_; lean_object* v_scopes_3555_; lean_object* v_usedQuotCtxts_3556_; lean_object* v_nextMacroScope_3557_; lean_object* v_maxRecDepth_3558_; lean_object* v_ngen_3559_; lean_object* v_auxDeclNGen_3560_; lean_object* v_infoState_3561_; lean_object* v_traceState_3562_; lean_object* v_snapshotTasks_3563_; lean_object* v_prevLinterStates_3564_; lean_object* v_codeQualityEntryTasks_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v___y_3545_);
v___x_3553_ = lean_st_ref_take(v___y_3544_);
v_env_3554_ = lean_ctor_get(v___x_3553_, 0);
v_scopes_3555_ = lean_ctor_get(v___x_3553_, 2);
v_usedQuotCtxts_3556_ = lean_ctor_get(v___x_3553_, 3);
v_nextMacroScope_3557_ = lean_ctor_get(v___x_3553_, 4);
v_maxRecDepth_3558_ = lean_ctor_get(v___x_3553_, 5);
v_ngen_3559_ = lean_ctor_get(v___x_3553_, 6);
v_auxDeclNGen_3560_ = lean_ctor_get(v___x_3553_, 7);
v_infoState_3561_ = lean_ctor_get(v___x_3553_, 8);
v_traceState_3562_ = lean_ctor_get(v___x_3553_, 9);
v_snapshotTasks_3563_ = lean_ctor_get(v___x_3553_, 10);
v_prevLinterStates_3564_ = lean_ctor_get(v___x_3553_, 11);
v_codeQualityEntryTasks_3565_ = lean_ctor_get(v___x_3553_, 12);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3590_ == 0)
{
lean_object* v_unused_3591_; 
v_unused_3591_ = lean_ctor_get(v___x_3553_, 1);
lean_dec(v_unused_3591_);
v___x_3567_ = v___x_3553_;
v_isShared_3568_ = v_isSharedCheck_3590_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3565_);
lean_inc(v_prevLinterStates_3564_);
lean_inc(v_snapshotTasks_3563_);
lean_inc(v_traceState_3562_);
lean_inc(v_infoState_3561_);
lean_inc(v_auxDeclNGen_3560_);
lean_inc(v_ngen_3559_);
lean_inc(v_maxRecDepth_3558_);
lean_inc(v_nextMacroScope_3557_);
lean_inc(v_usedQuotCtxts_3556_);
lean_inc(v_scopes_3555_);
lean_inc(v_env_3554_);
lean_dec(v___x_3553_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3590_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 1, v___y_3549_);
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_env_3554_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v___y_3549_);
lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_scopes_3555_);
lean_ctor_set(v_reuseFailAlloc_3589_, 3, v_usedQuotCtxts_3556_);
lean_ctor_set(v_reuseFailAlloc_3589_, 4, v_nextMacroScope_3557_);
lean_ctor_set(v_reuseFailAlloc_3589_, 5, v_maxRecDepth_3558_);
lean_ctor_set(v_reuseFailAlloc_3589_, 6, v_ngen_3559_);
lean_ctor_set(v_reuseFailAlloc_3589_, 7, v_auxDeclNGen_3560_);
lean_ctor_set(v_reuseFailAlloc_3589_, 8, v_infoState_3561_);
lean_ctor_set(v_reuseFailAlloc_3589_, 9, v_traceState_3562_);
lean_ctor_set(v_reuseFailAlloc_3589_, 10, v_snapshotTasks_3563_);
lean_ctor_set(v_reuseFailAlloc_3589_, 11, v_prevLinterStates_3564_);
lean_ctor_set(v_reuseFailAlloc_3589_, 12, v_codeQualityEntryTasks_3565_);
v___x_3570_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v_scopes_3574_; lean_object* v___x_3575_; lean_object* v_opts_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3571_ = lean_st_ref_put(v___y_3544_, v___x_3570_);
v___x_3572_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3573_ = lean_st_ref_get(v___y_3544_);
v_scopes_3574_ = lean_ctor_get(v___x_3573_, 2);
lean_inc(v_scopes_3574_);
lean_dec(v___x_3573_);
v___x_3575_ = l_List_head_x21___redArg(v___x_3572_, v_scopes_3574_);
lean_dec(v_scopes_3574_);
v_opts_3576_ = lean_ctor_get(v___x_3575_, 1);
lean_inc_ref(v_opts_3576_);
lean_dec(v___x_3575_);
v___x_3577_ = l_Lean_guard__msgs_diff;
v___x_3578_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3576_, v___x_3577_);
lean_dec_ref(v_opts_3576_);
if (v___x_3578_ == 0)
{
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3546_);
lean_inc_ref(v___y_3547_);
v___y_3513_ = v___y_3544_;
v___y_3514_ = v___y_3547_;
v___y_3515_ = v___y_3548_;
v___y_3516_ = v___y_3550_;
v___y_3517_ = v___y_3547_;
goto v___jp_3512_;
}
else
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3579_ = lean_string_utf8_byte_size(v___y_3546_);
lean_inc(v___y_3551_);
lean_inc_ref(v___y_3546_);
v___x_3580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3580_, 0, v___y_3546_);
lean_ctor_set(v___x_3580_, 1, v___y_3551_);
lean_ctor_set(v___x_3580_, 2, v___x_3579_);
v___x_3581_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
v___x_3582_ = lean_mk_empty_array_with_capacity(v___y_3551_);
lean_inc_ref(v___x_3582_);
v___x_3583_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3546_, v___x_3580_, v___x_3579_, v___x_3581_, v___x_3582_);
lean_dec_ref_known(v___x_3580_, 3);
v___x_3584_ = lean_string_utf8_byte_size(v___y_3547_);
lean_inc_ref_n(v___y_3547_, 2);
v___x_3585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3585_, 0, v___y_3547_);
lean_ctor_set(v___x_3585_, 1, v___y_3551_);
lean_ctor_set(v___x_3585_, 2, v___x_3584_);
v___x_3586_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3547_, v___x_3585_, v___x_3584_, v___x_3581_, v___x_3582_);
lean_dec_ref_known(v___x_3585_, 3);
v___x_3587_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3583_, v___x_3586_);
v___x_3588_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3587_);
lean_dec_ref(v___x_3587_);
v___y_3513_ = v___y_3544_;
v___y_3514_ = v___y_3547_;
v___y_3515_ = v___y_3548_;
v___y_3516_ = v___y_3550_;
v___y_3517_ = v___x_3588_;
goto v___jp_3512_;
}
}
}
}
else
{
lean_object* v___x_3592_; lean_object* v_env_3593_; lean_object* v_scopes_3594_; lean_object* v_usedQuotCtxts_3595_; lean_object* v_nextMacroScope_3596_; lean_object* v_maxRecDepth_3597_; lean_object* v_ngen_3598_; lean_object* v_auxDeclNGen_3599_; lean_object* v_infoState_3600_; lean_object* v_traceState_3601_; lean_object* v_snapshotTasks_3602_; lean_object* v_prevLinterStates_3603_; lean_object* v_codeQualityEntryTasks_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3614_; 
lean_dec(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v___y_3546_);
v___x_3592_ = lean_st_ref_take(v___y_3544_);
v_env_3593_ = lean_ctor_get(v___x_3592_, 0);
v_scopes_3594_ = lean_ctor_get(v___x_3592_, 2);
v_usedQuotCtxts_3595_ = lean_ctor_get(v___x_3592_, 3);
v_nextMacroScope_3596_ = lean_ctor_get(v___x_3592_, 4);
v_maxRecDepth_3597_ = lean_ctor_get(v___x_3592_, 5);
v_ngen_3598_ = lean_ctor_get(v___x_3592_, 6);
v_auxDeclNGen_3599_ = lean_ctor_get(v___x_3592_, 7);
v_infoState_3600_ = lean_ctor_get(v___x_3592_, 8);
v_traceState_3601_ = lean_ctor_get(v___x_3592_, 9);
v_snapshotTasks_3602_ = lean_ctor_get(v___x_3592_, 10);
v_prevLinterStates_3603_ = lean_ctor_get(v___x_3592_, 11);
v_codeQualityEntryTasks_3604_ = lean_ctor_get(v___x_3592_, 12);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3614_ == 0)
{
lean_object* v_unused_3615_; 
v_unused_3615_ = lean_ctor_get(v___x_3592_, 1);
lean_dec(v_unused_3615_);
v___x_3606_ = v___x_3592_;
v_isShared_3607_ = v_isSharedCheck_3614_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3604_);
lean_inc(v_prevLinterStates_3603_);
lean_inc(v_snapshotTasks_3602_);
lean_inc(v_traceState_3601_);
lean_inc(v_infoState_3600_);
lean_inc(v_auxDeclNGen_3599_);
lean_inc(v_ngen_3598_);
lean_inc(v_maxRecDepth_3597_);
lean_inc(v_nextMacroScope_3596_);
lean_inc(v_usedQuotCtxts_3595_);
lean_inc(v_scopes_3594_);
lean_inc(v_env_3593_);
lean_dec(v___x_3592_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3614_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3608_ = lean_box(0);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 1, v___y_3545_);
v___x_3610_ = v___x_3606_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_env_3593_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v___y_3545_);
lean_ctor_set(v_reuseFailAlloc_3613_, 2, v_scopes_3594_);
lean_ctor_set(v_reuseFailAlloc_3613_, 3, v_usedQuotCtxts_3595_);
lean_ctor_set(v_reuseFailAlloc_3613_, 4, v_nextMacroScope_3596_);
lean_ctor_set(v_reuseFailAlloc_3613_, 5, v_maxRecDepth_3597_);
lean_ctor_set(v_reuseFailAlloc_3613_, 6, v_ngen_3598_);
lean_ctor_set(v_reuseFailAlloc_3613_, 7, v_auxDeclNGen_3599_);
lean_ctor_set(v_reuseFailAlloc_3613_, 8, v_infoState_3600_);
lean_ctor_set(v_reuseFailAlloc_3613_, 9, v_traceState_3601_);
lean_ctor_set(v_reuseFailAlloc_3613_, 10, v_snapshotTasks_3602_);
lean_ctor_set(v_reuseFailAlloc_3613_, 11, v_prevLinterStates_3603_);
lean_ctor_set(v_reuseFailAlloc_3613_, 12, v_codeQualityEntryTasks_3604_);
v___x_3610_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = lean_st_ref_put(v___y_3544_, v___x_3610_);
v___x_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3608_);
return v___x_3612_;
}
}
}
}
v___jp_3616_:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v_a_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v_str_3639_; lean_object* v_startInclusive_3640_; lean_object* v_endExclusive_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3656_; 
v___x_3629_ = l_Lean_MessageLog_toList(v___y_3623_);
lean_dec(v___y_3623_);
v___x_3630_ = lean_box(0);
v___x_3631_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3628_, v___x_3629_, v___x_3630_);
lean_dec(v___y_3628_);
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_a_3632_);
lean_dec_ref(v___x_3631_);
v___x_3633_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3627_, v_a_3632_);
v___x_3634_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4));
v___x_3635_ = l_String_intercalate(v___x_3634_, v___x_3633_);
v___x_3636_ = lean_string_utf8_byte_size(v___x_3635_);
lean_inc(v___y_3625_);
v___x_3637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3635_);
lean_ctor_set(v___x_3637_, 1, v___y_3625_);
lean_ctor_set(v___x_3637_, 2, v___x_3636_);
v___x_3638_ = l_String_Slice_trimAscii(v___x_3637_);
v_str_3639_ = lean_ctor_get(v___x_3638_, 0);
v_startInclusive_3640_ = lean_ctor_get(v___x_3638_, 1);
v_endExclusive_3641_ = lean_ctor_get(v___x_3638_, 2);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3643_ = v___x_3638_;
v_isShared_3644_ = v_isSharedCheck_3656_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_endExclusive_3641_);
lean_inc(v_startInclusive_3640_);
lean_inc(v_str_3639_);
lean_dec(v___x_3638_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3656_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; 
v___x_3645_ = lean_string_utf8_extract_fast(v_str_3639_, v_startInclusive_3640_, v_endExclusive_3641_);
lean_dec(v_endExclusive_3641_);
lean_dec(v_startInclusive_3640_);
lean_dec_ref(v_str_3639_);
if (v___y_3626_ == 0)
{
lean_object* v___x_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
lean_del_object(v___x_3643_);
lean_inc_ref(v___y_3620_);
v___x_3646_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3618_, v___y_3620_);
lean_inc_ref(v___x_3645_);
v___x_3647_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3618_, v___x_3645_);
v___x_3648_ = lean_string_dec_eq(v___x_3646_, v___x_3647_);
lean_dec_ref(v___x_3647_);
lean_dec_ref(v___x_3646_);
v___y_3544_ = v___y_3617_;
v___y_3545_ = v___y_3619_;
v___y_3546_ = v___y_3620_;
v___y_3547_ = v___x_3645_;
v___y_3548_ = v___y_3622_;
v___y_3549_ = v___y_3621_;
v___y_3550_ = v___y_3624_;
v___y_3551_ = v___y_3625_;
v___y_3552_ = v___x_3648_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3653_; 
lean_inc_ref(v___x_3645_);
v___x_3649_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3618_, v___x_3645_);
lean_inc_ref(v___y_3620_);
v___x_3650_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3618_, v___y_3620_);
v___x_3651_ = lean_string_utf8_byte_size(v___x_3649_);
lean_inc(v___y_3625_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 2, v___x_3651_);
lean_ctor_set(v___x_3643_, 1, v___y_3625_);
lean_ctor_set(v___x_3643_, 0, v___x_3649_);
v___x_3653_ = v___x_3643_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3649_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v___y_3625_);
lean_ctor_set(v_reuseFailAlloc_3655_, 2, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
uint8_t v___x_3654_; 
v___x_3654_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3650_, v___x_3653_);
lean_dec_ref(v___x_3653_);
v___y_3544_ = v___y_3617_;
v___y_3545_ = v___y_3619_;
v___y_3546_ = v___y_3620_;
v___y_3547_ = v___x_3645_;
v___y_3548_ = v___y_3622_;
v___y_3549_ = v___y_3621_;
v___y_3550_ = v___y_3624_;
v___y_3551_ = v___y_3625_;
v___y_3552_ = v___x_3654_;
goto v___jp_3543_;
}
}
}
}
v___jp_3657_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v_str_3668_; lean_object* v_startInclusive_3669_; lean_object* v_endExclusive_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3664_ = lean_unsigned_to_nat(0u);
v___x_3665_ = lean_string_utf8_byte_size(v___y_3663_);
v___x_3666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3666_, 0, v___y_3663_);
lean_ctor_set(v___x_3666_, 1, v___x_3664_);
lean_ctor_set(v___x_3666_, 2, v___x_3665_);
v___x_3667_ = l_String_Slice_trimAscii(v___x_3666_);
v_str_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc_ref(v_str_3668_);
v_startInclusive_3669_ = lean_ctor_get(v___x_3667_, 1);
lean_inc(v_startInclusive_3669_);
v_endExclusive_3670_ = lean_ctor_get(v___x_3667_, 2);
lean_inc(v_endExclusive_3670_);
lean_dec_ref(v___x_3667_);
v___x_3671_ = lean_string_utf8_extract_fast(v_str_3668_, v_startInclusive_3669_, v_endExclusive_3670_);
lean_dec(v_endExclusive_3670_);
lean_dec(v_startInclusive_3669_);
lean_dec_ref(v_str_3668_);
v___x_3672_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3671_);
v___x_3673_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3662_, v___y_3659_, v___y_3658_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v_filterFn_3675_; uint8_t v_whitespace_3676_; uint8_t v_ordering_3677_; uint8_t v_reportPositions_3678_; uint8_t v_substring_3679_; lean_object* v___x_3680_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref_known(v___x_3673_, 1);
v_filterFn_3675_ = lean_ctor_get(v_a_3674_, 0);
lean_inc_ref(v_filterFn_3675_);
v_whitespace_3676_ = lean_ctor_get_uint8(v_a_3674_, sizeof(void*)*1);
v_ordering_3677_ = lean_ctor_get_uint8(v_a_3674_, sizeof(void*)*1 + 1);
v_reportPositions_3678_ = lean_ctor_get_uint8(v_a_3674_, sizeof(void*)*1 + 2);
v_substring_3679_ = lean_ctor_get_uint8(v_a_3674_, sizeof(void*)*1 + 3);
lean_dec(v_a_3674_);
v___x_3680_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3661_, v___y_3659_, v___y_3658_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v_a_3685_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_a_3681_);
lean_dec_ref_known(v___x_3680_, 1);
v___x_3682_ = l_Lean_MessageLog_toList(v_a_3681_);
v___x_3683_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5);
v___x_3684_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3675_, v___x_3682_, v___x_3683_);
lean_dec(v___x_3682_);
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
lean_dec_ref(v___x_3684_);
if (v_reportPositions_3678_ == 0)
{
lean_object* v_fst_3686_; lean_object* v_snd_3687_; lean_object* v___x_3688_; 
v_fst_3686_ = lean_ctor_get(v_a_3685_, 0);
lean_inc(v_fst_3686_);
v_snd_3687_ = lean_ctor_get(v_a_3685_, 1);
lean_inc(v_snd_3687_);
lean_dec(v_a_3685_);
v___x_3688_ = lean_box(0);
v___y_3617_ = v___y_3658_;
v___y_3618_ = v_whitespace_3676_;
v___y_3619_ = v_snd_3687_;
v___y_3620_ = v___x_3672_;
v___y_3621_ = v_a_3681_;
v___y_3622_ = v___y_3659_;
v___y_3623_ = v_fst_3686_;
v___y_3624_ = v___y_3660_;
v___y_3625_ = v___x_3664_;
v___y_3626_ = v_substring_3679_;
v___y_3627_ = v_ordering_3677_;
v___y_3628_ = v___x_3688_;
goto v___jp_3616_;
}
else
{
lean_object* v_fst_3689_; lean_object* v_snd_3690_; uint8_t v___x_3691_; lean_object* v___x_3692_; 
v_fst_3689_ = lean_ctor_get(v_a_3685_, 0);
lean_inc(v_fst_3689_);
v_snd_3690_ = lean_ctor_get(v_a_3685_, 1);
lean_inc(v_snd_3690_);
lean_dec(v_a_3685_);
v___x_3691_ = 0;
v___x_3692_ = l_Lean_Syntax_getPos_x3f(v___y_3660_, v___x_3691_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v___x_3693_; 
v___x_3693_ = lean_box(0);
v___y_3617_ = v___y_3658_;
v___y_3618_ = v_whitespace_3676_;
v___y_3619_ = v_snd_3690_;
v___y_3620_ = v___x_3672_;
v___y_3621_ = v_a_3681_;
v___y_3622_ = v___y_3659_;
v___y_3623_ = v_fst_3689_;
v___y_3624_ = v___y_3660_;
v___y_3625_ = v___x_3664_;
v___y_3626_ = v_substring_3679_;
v___y_3627_ = v_ordering_3677_;
v___y_3628_ = v___x_3693_;
goto v___jp_3616_;
}
else
{
lean_object* v_val_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3704_; 
v_val_3694_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3696_ = v___x_3692_;
v_isShared_3697_ = v_isSharedCheck_3704_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_val_3694_);
lean_dec(v___x_3692_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3704_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v_fileMap_3698_; lean_object* v___x_3699_; lean_object* v_line_3700_; lean_object* v___x_3702_; 
v_fileMap_3698_ = lean_ctor_get(v___y_3659_, 1);
lean_inc_ref(v_fileMap_3698_);
v___x_3699_ = l_Lean_FileMap_toPosition(v_fileMap_3698_, v_val_3694_);
lean_dec(v_val_3694_);
v_line_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_line_3700_);
lean_dec_ref(v___x_3699_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v_line_3700_);
v___x_3702_ = v___x_3696_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_line_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
v___y_3617_ = v___y_3658_;
v___y_3618_ = v_whitespace_3676_;
v___y_3619_ = v_snd_3690_;
v___y_3620_ = v___x_3672_;
v___y_3621_ = v_a_3681_;
v___y_3622_ = v___y_3659_;
v___y_3623_ = v_fst_3689_;
v___y_3624_ = v___y_3660_;
v___y_3625_ = v___x_3664_;
v___y_3626_ = v_substring_3679_;
v___y_3627_ = v_ordering_3677_;
v___y_3628_ = v___x_3702_;
goto v___jp_3616_;
}
}
}
}
}
else
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
lean_dec_ref(v_filterFn_3675_);
lean_dec_ref(v___x_3672_);
lean_dec(v___y_3660_);
v_a_3705_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3680_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3680_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec_ref(v___x_3672_);
lean_dec(v___y_3661_);
lean_dec(v___y_3660_);
v_a_3713_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3673_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3673_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
v___jp_3721_:
{
if (lean_obj_tag(v___y_3724_) == 0)
{
lean_object* v___x_3728_; 
v___x_3728_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_3658_ = v___y_3722_;
v___y_3659_ = v___y_3723_;
v___y_3660_ = v___y_3725_;
v___y_3661_ = v___y_3726_;
v___y_3662_ = v___y_3727_;
v___y_3663_ = v___x_3728_;
goto v___jp_3657_;
}
else
{
lean_object* v_val_3729_; lean_object* v___x_3730_; 
v_val_3729_ = lean_ctor_get(v___y_3724_, 0);
lean_inc(v_val_3729_);
lean_dec_ref_known(v___y_3724_, 1);
v___x_3730_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3729_, v___y_3723_, v___y_3722_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref_known(v___x_3730_, 1);
v___y_3658_ = v___y_3722_;
v___y_3659_ = v___y_3723_;
v___y_3660_ = v___y_3725_;
v___y_3661_ = v___y_3726_;
v___y_3662_ = v___y_3727_;
v___y_3663_ = v_a_3731_;
goto v___jp_3657_;
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec(v___y_3725_);
v_a_3732_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3730_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3730_);
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
}
v___jp_3740_:
{
lean_object* v___x_3744_; lean_object* v_tk_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3744_ = lean_unsigned_to_nat(1u);
v_tk_3745_ = l_Lean_Syntax_getArg(v_x_3504_, v___x_3744_);
v___x_3746_ = lean_unsigned_to_nat(2u);
v___x_3747_ = l_Lean_Syntax_getArg(v_x_3504_, v___x_3746_);
v___x_3748_ = lean_unsigned_to_nat(4u);
v___x_3749_ = l_Lean_Syntax_getArg(v_x_3504_, v___x_3748_);
lean_dec(v_x_3504_);
v___x_3750_ = l_Lean_Syntax_getOptional_x3f(v___x_3747_);
lean_dec(v___x_3747_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v___x_3751_; 
v___x_3751_ = lean_box(0);
v___y_3722_ = v___y_3743_;
v___y_3723_ = v___y_3742_;
v___y_3724_ = v_dc_x3f_3741_;
v___y_3725_ = v_tk_3745_;
v___y_3726_ = v___x_3749_;
v___y_3727_ = v___x_3751_;
goto v___jp_3721_;
}
else
{
lean_object* v_val_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
v_val_3752_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3750_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_val_3752_);
lean_dec(v___x_3750_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_val_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
v___y_3722_ = v___y_3743_;
v___y_3723_ = v___y_3742_;
v___y_3724_ = v_dc_x3f_3741_;
v___y_3725_ = v_tk_3745_;
v___y_3726_ = v___x_3749_;
v___y_3727_ = v___x_3757_;
goto v___jp_3721_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3773_, v_a_3774_, v_a_3775_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3778_, lean_object* v_as_3779_, lean_object* v_as_x27_3780_, lean_object* v_b_3781_, lean_object* v_a_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3778_, v_as_x27_3780_, v_b_3781_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3787_, lean_object* v_as_3788_, lean_object* v_as_x27_3789_, lean_object* v_b_3790_, lean_object* v_a_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3787_, v_as_3788_, v_as_x27_3789_, v_b_3790_, v_a_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v_as_x27_3789_);
lean_dec(v_as_3788_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3796_, lean_object* v_x_3797_, lean_object* v_x_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3796_, v_x_3797_, v_x_3798_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3803_, lean_object* v_x_3804_, lean_object* v_x_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3803_, v_x_3804_, v_x_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3803_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3810_, v___y_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3815_, v___y_3816_, v___y_3817_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3820_, lean_object* v___x_3821_, lean_object* v___x_3822_, lean_object* v_inst_3823_, lean_object* v_R_3824_, lean_object* v_a_3825_, lean_object* v_b_3826_){
_start:
{
lean_object* v___x_3827_; 
v___x_3827_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3820_, v___x_3821_, v___x_3822_, v_a_3825_, v_b_3826_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3828_, lean_object* v___x_3829_, lean_object* v___x_3830_, lean_object* v_inst_3831_, lean_object* v_R_3832_, lean_object* v_a_3833_, lean_object* v_b_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3828_, v___x_3829_, v___x_3830_, v_inst_3831_, v_R_3832_, v_a_3833_, v_b_3834_);
lean_dec_ref(v___x_3829_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3836_, v___y_3838_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3841_, v___y_3842_, v___y_3843_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3846_, lean_object* v___x_3847_, lean_object* v___x_3848_, lean_object* v_inst_3849_, lean_object* v_R_3850_, lean_object* v_a_3851_, lean_object* v_b_3852_){
_start:
{
lean_object* v___x_3853_; 
v___x_3853_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3846_, v___x_3847_, v___x_3848_, v_a_3851_, v_b_3852_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3854_, lean_object* v___x_3855_, lean_object* v___x_3856_, lean_object* v_inst_3857_, lean_object* v_R_3858_, lean_object* v_a_3859_, lean_object* v_b_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3854_, v___x_3855_, v___x_3856_, v_inst_3857_, v_R_3858_, v_a_3859_, v_b_3860_);
lean_dec_ref(v___x_3855_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v___x_3862_, lean_object* v_original_3863_, lean_object* v_a_3864_, lean_object* v_inst_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_3862_, v_original_3863_, v_a_3864_, v_a_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___boxed(lean_object* v___x_3868_, lean_object* v_original_3869_, lean_object* v_a_3870_, lean_object* v_inst_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3868_, v_original_3869_, v_a_3870_, v_inst_3871_, v_a_3872_);
lean_dec_ref(v_a_3870_);
lean_dec_ref(v_original_3869_);
lean_dec(v___x_3868_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v___x_3874_, lean_object* v_edited_3875_, lean_object* v_a_3876_, lean_object* v_inst_3877_, lean_object* v_a_3878_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_3874_, v_edited_3875_, v_a_3876_, v_a_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v___x_3880_, lean_object* v_edited_3881_, lean_object* v_a_3882_, lean_object* v_inst_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v___x_3880_, v_edited_3881_, v_a_3882_, v_inst_3883_, v_a_3884_);
lean_dec_ref(v_a_3882_);
lean_dec_ref(v_edited_3881_);
lean_dec(v___x_3880_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3886_, lean_object* v_original_3887_, lean_object* v_inst_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3886_, v_original_3887_, v_a_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3891_, lean_object* v_original_3892_, lean_object* v_inst_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3891_, v_original_3892_, v_inst_3893_, v_a_3894_);
lean_dec_ref(v_original_3892_);
lean_dec(v___x_3891_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3896_, lean_object* v_edited_3897_, lean_object* v_inst_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3896_, v_edited_3897_, v_a_3899_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3901_, lean_object* v_edited_3902_, lean_object* v_inst_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3901_, v_edited_3902_, v_inst_3903_, v_a_3904_);
lean_dec_ref(v_edited_3902_);
lean_dec(v___x_3901_);
return v_res_3905_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3906_, lean_object* v_inst_3907_, lean_object* v_R_3908_, lean_object* v_a_3909_, uint8_t v_b_3910_, lean_object* v_c_3911_){
_start:
{
uint8_t v___x_3912_; 
v___x_3912_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3906_, v_a_3909_, v_b_3910_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3913_, lean_object* v_inst_3914_, lean_object* v_R_3915_, lean_object* v_a_3916_, lean_object* v_b_3917_, lean_object* v_c_3918_){
_start:
{
uint8_t v_b_boxed_3919_; uint8_t v_res_3920_; lean_object* v_r_3921_; 
v_b_boxed_3919_ = lean_unbox(v_b_3917_);
v_res_3920_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3913_, v_inst_3914_, v_R_3915_, v_a_3916_, v_b_boxed_3919_, v_c_3918_);
lean_dec_ref(v_s_3913_);
v_r_3921_ = lean_box(v_res_3920_);
return v_r_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3922_, lean_object* v_ref_3923_, lean_object* v_msg_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v___x_3928_; 
v___x_3928_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3923_, v_msg_3924_, v___y_3925_, v___y_3926_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3929_, lean_object* v_ref_3930_, lean_object* v_msg_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3929_, v_ref_3930_, v_msg_3931_, v___y_3932_, v___y_3933_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v_ref_3930_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(lean_object* v_as_3936_, lean_object* v_as_x27_3937_, lean_object* v_b_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3937_, v_b_3938_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___boxed(lean_object* v_as_3941_, lean_object* v_as_x27_3942_, lean_object* v_b_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(v_as_3941_, v_as_x27_3942_, v_b_3943_, v_a_3944_);
lean_dec(v_as_x27_3942_);
lean_dec(v_as_3941_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(lean_object* v_lsize_3946_, lean_object* v_rsize_3947_, lean_object* v_histogram_3948_, lean_object* v_index_3949_, lean_object* v_val_3950_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_histogram_3948_, v_index_3949_, v_val_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___boxed(lean_object* v_lsize_3952_, lean_object* v_rsize_3953_, lean_object* v_histogram_3954_, lean_object* v_index_3955_, lean_object* v_val_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(v_lsize_3952_, v_rsize_3953_, v_histogram_3954_, v_index_3955_, v_val_3956_);
lean_dec(v_rsize_3953_);
lean_dec(v_lsize_3952_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(lean_object* v_upperBound_3958_, lean_object* v___x_3959_, lean_object* v_fst_3960_, lean_object* v___x_3961_, lean_object* v_inst_3962_, lean_object* v_R_3963_, lean_object* v_a_3964_, lean_object* v_b_3965_, lean_object* v_c_3966_){
_start:
{
lean_object* v___x_3967_; 
v___x_3967_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3958_, v___x_3959_, v_fst_3960_, v___x_3961_, v_a_3964_, v_b_3965_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___boxed(lean_object* v_upperBound_3968_, lean_object* v___x_3969_, lean_object* v_fst_3970_, lean_object* v___x_3971_, lean_object* v_inst_3972_, lean_object* v_R_3973_, lean_object* v_a_3974_, lean_object* v_b_3975_, lean_object* v_c_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(v_upperBound_3968_, v___x_3969_, v_fst_3970_, v___x_3971_, v_inst_3972_, v_R_3973_, v_a_3974_, v_b_3975_, v_c_3976_);
lean_dec(v___x_3971_);
lean_dec_ref(v_fst_3970_);
lean_dec(v___x_3969_);
lean_dec(v_upperBound_3968_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(lean_object* v_lsize_3978_, lean_object* v_rsize_3979_, lean_object* v_histogram_3980_, lean_object* v_index_3981_, lean_object* v_val_3982_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_histogram_3980_, v_index_3981_, v_val_3982_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___boxed(lean_object* v_lsize_3984_, lean_object* v_rsize_3985_, lean_object* v_histogram_3986_, lean_object* v_index_3987_, lean_object* v_val_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(v_lsize_3984_, v_rsize_3985_, v_histogram_3986_, v_index_3987_, v_val_3988_);
lean_dec(v_rsize_3985_);
lean_dec(v_lsize_3984_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(lean_object* v_upperBound_3990_, lean_object* v_fst_3991_, lean_object* v___x_3992_, lean_object* v_fst_3993_, lean_object* v_inst_3994_, lean_object* v_R_3995_, lean_object* v_a_3996_, lean_object* v_b_3997_, lean_object* v_c_3998_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3990_, v_fst_3991_, v___x_3992_, v_fst_3993_, v_a_3996_, v_b_3997_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___boxed(lean_object* v_upperBound_4000_, lean_object* v_fst_4001_, lean_object* v___x_4002_, lean_object* v_fst_4003_, lean_object* v_inst_4004_, lean_object* v_R_4005_, lean_object* v_a_4006_, lean_object* v_b_4007_, lean_object* v_c_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(v_upperBound_4000_, v_fst_4001_, v___x_4002_, v_fst_4003_, v_inst_4004_, v_R_4005_, v_a_4006_, v_b_4007_, v_c_4008_);
lean_dec_ref(v_fst_4003_);
lean_dec(v___x_4002_);
lean_dec_ref(v_fst_4001_);
lean_dec(v_upperBound_4000_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_4010_, lean_object* v_msg_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_4011_, v___y_4012_, v___y_4013_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_4016_, lean_object* v_msg_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_4016_, v_msg_4017_, v___y_4018_, v___y_4019_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(lean_object* v_00_u03b2_4022_, lean_object* v_m_4023_, lean_object* v_a_4024_){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_4023_, v_a_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___boxed(lean_object* v_00_u03b2_4026_, lean_object* v_m_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(v_00_u03b2_4026_, v_m_4027_, v_a_4028_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_m_4027_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26(lean_object* v_00_u03b2_4030_, lean_object* v_m_4031_, lean_object* v_a_4032_, lean_object* v_b_4033_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_m_4031_, v_a_4032_, v_b_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_4035_, lean_object* v_macroStack_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___x_4040_; 
v___x_4040_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_4035_, v_macroStack_4036_, v___y_4038_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4041_, lean_object* v_macroStack_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4041_, v_macroStack_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29(lean_object* v_inst_4047_, lean_object* v_R_4048_, lean_object* v_a_4049_, lean_object* v_b_4050_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v_a_4049_, v_b_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(lean_object* v_00_u03b2_4052_, lean_object* v_a_4053_, lean_object* v_x_4054_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_4053_, v_x_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___boxed(lean_object* v_00_u03b2_4056_, lean_object* v_a_4057_, lean_object* v_x_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(v_00_u03b2_4056_, v_a_4057_, v_x_4058_);
lean_dec(v_x_4058_);
lean_dec_ref(v_a_4057_);
return v_res_4059_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(lean_object* v_00_u03b2_4060_, lean_object* v_a_4061_, lean_object* v_x_4062_){
_start:
{
uint8_t v___x_4063_; 
v___x_4063_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_4061_, v_x_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___boxed(lean_object* v_00_u03b2_4064_, lean_object* v_a_4065_, lean_object* v_x_4066_){
_start:
{
uint8_t v_res_4067_; lean_object* v_r_4068_; 
v_res_4067_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(v_00_u03b2_4064_, v_a_4065_, v_x_4066_);
lean_dec(v_x_4066_);
lean_dec_ref(v_a_4065_);
v_r_4068_ = lean_box(v_res_4067_);
return v_r_4068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38(lean_object* v_00_u03b2_4069_, lean_object* v_data_4070_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_data_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39(lean_object* v_00_u03b2_4072_, lean_object* v_a_4073_, lean_object* v_b_4074_, lean_object* v_x_4075_){
_start:
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_4073_, v_b_4074_, v_x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44(lean_object* v_00_u03b2_4077_, lean_object* v_i_4078_, lean_object* v_source_4079_, lean_object* v_target_4080_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v_i_4078_, v_source_4079_, v_target_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4082_, lean_object* v_x_4083_, lean_object* v_x_4084_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_x_4083_, v_x_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4094_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4095_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
v___x_4096_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4097_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4098_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4094_, v___x_4095_, v___x_4096_, v___x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4127_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4128_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4129_ = l_Lean_addBuiltinDeclarationRanges(v___x_4127_, v___x_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4132_){
_start:
{
lean_object* v_doc_4134_; lean_object* v___x_4135_; 
v_doc_4134_ = lean_ctor_get(v___y_4132_, 1);
lean_inc_ref(v_doc_4134_);
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v_doc_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4136_);
lean_dec_ref(v___y_4136_);
return v_res_4138_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4139_, lean_object* v_a_4140_, uint8_t v_b_4141_){
_start:
{
lean_object* v_str_4142_; lean_object* v_startInclusive_4143_; lean_object* v_endExclusive_4144_; lean_object* v___x_4145_; uint8_t v_decide_4146_; 
v_str_4142_ = lean_ctor_get(v_s_4139_, 0);
v_startInclusive_4143_ = lean_ctor_get(v_s_4139_, 1);
v_endExclusive_4144_ = lean_ctor_get(v_s_4139_, 2);
v___x_4145_ = lean_nat_sub(v_endExclusive_4144_, v_startInclusive_4143_);
v_decide_4146_ = lean_nat_dec_eq(v_a_4140_, v___x_4145_);
lean_dec(v___x_4145_);
if (v_decide_4146_ == 0)
{
lean_object* v___x_4147_; uint32_t v___x_4148_; uint32_t v___x_4149_; uint8_t v___x_4150_; 
v___x_4147_ = lean_nat_add(v_startInclusive_4143_, v_a_4140_);
lean_dec(v_a_4140_);
v___x_4148_ = lean_string_utf8_get_fast(v_str_4142_, v___x_4147_);
v___x_4149_ = 10;
v___x_4150_ = lean_uint32_dec_eq(v___x_4148_, v___x_4149_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4151_ = lean_string_utf8_next_fast(v_str_4142_, v___x_4147_);
lean_dec(v___x_4147_);
v___x_4152_ = lean_nat_sub(v___x_4151_, v_startInclusive_4143_);
v_a_4140_ = v___x_4152_;
v_b_4141_ = v___x_4150_;
goto _start;
}
else
{
lean_dec(v___x_4147_);
return v___x_4150_;
}
}
else
{
lean_dec(v_a_4140_);
return v_b_4141_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4154_, lean_object* v_a_4155_, lean_object* v_b_4156_){
_start:
{
uint8_t v_b_boxed_4157_; uint8_t v_res_4158_; lean_object* v_r_4159_; 
v_b_boxed_4157_ = lean_unbox(v_b_4156_);
v_res_4158_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4154_, v_a_4155_, v_b_boxed_4157_);
lean_dec_ref(v_s_4154_);
v_r_4159_ = lean_box(v_res_4158_);
return v_r_4159_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4160_){
_start:
{
lean_object* v_searcher_4161_; uint8_t v___x_4162_; uint8_t v___x_4163_; 
v_searcher_4161_ = lean_unsigned_to_nat(0u);
v___x_4162_ = 0;
v___x_4163_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4160_, v_searcher_4161_, v___x_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4164_){
_start:
{
uint8_t v_res_4165_; lean_object* v_r_4166_; 
v_res_4165_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4164_);
lean_dec_ref(v_s_4164_);
v_r_4166_ = lean_box(v_res_4165_);
return v_r_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4178_, lean_object* v_fst_4179_, uint8_t v___x_4180_, lean_object* v_a_4181_, lean_object* v___x_4182_, lean_object* v___x_4183_, lean_object* v___x_4184_, lean_object* v___x_4185_, lean_object* v___x_4186_, lean_object* v___x_4187_, lean_object* v___x_4188_, lean_object* v___x_4189_, lean_object* v_snd_4190_, lean_object* v___x_4191_){
_start:
{
if (lean_obj_tag(v___x_4178_) == 1)
{
lean_object* v_val_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4254_; 
v_val_4193_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4195_ = v___x_4178_;
v_isShared_4196_ = v_isSharedCheck_4254_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_val_4193_);
lean_dec(v___x_4178_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4254_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4197_ = lean_unsigned_to_nat(0u);
v___x_4198_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4199_ = l_Lean_Syntax_setArg(v_fst_4179_, v___x_4197_, v___x_4198_);
v___x_4200_ = l_Lean_Syntax_getPos_x3f(v___x_4199_, v___x_4180_);
lean_dec(v___x_4199_);
if (lean_obj_tag(v___x_4200_) == 1)
{
lean_object* v_val_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v___x_4191_);
v_val_4201_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4203_ = v___x_4200_;
v_isShared_4204_ = v_isSharedCheck_4250_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_val_4201_);
lean_dec(v___x_4200_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4250_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___y_4206_; lean_object* v___x_4232_; lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4232_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4190_);
v___x_4238_ = lean_string_utf8_byte_size(v___x_4232_);
v___x_4239_ = lean_nat_dec_eq(v___x_4238_, v___x_4197_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; lean_object* v___x_4241_; uint8_t v___x_4242_; 
v___x_4240_ = lean_string_length(v___x_4232_);
v___x_4241_ = lean_unsigned_to_nat(93u);
v___x_4242_ = lean_nat_dec_le(v___x_4240_, v___x_4241_);
if (v___x_4242_ == 0)
{
goto v___jp_4233_;
}
else
{
lean_object* v___x_4243_; uint8_t v___x_4244_; 
lean_inc_ref(v___x_4232_);
v___x_4243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4232_);
lean_ctor_set(v___x_4243_, 1, v___x_4197_);
lean_ctor_set(v___x_4243_, 2, v___x_4238_);
v___x_4244_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4243_);
lean_dec_ref_known(v___x_4243_, 3);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4245_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4246_ = lean_string_append(v___x_4245_, v___x_4232_);
lean_dec_ref(v___x_4232_);
v___x_4247_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4248_ = lean_string_append(v___x_4246_, v___x_4247_);
v___y_4206_ = v___x_4248_;
goto v___jp_4205_;
}
else
{
goto v___jp_4233_;
}
}
}
else
{
lean_object* v___x_4249_; 
lean_dec_ref(v___x_4232_);
v___x_4249_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_4206_ = v___x_4249_;
goto v___jp_4205_;
}
v___jp_4205_:
{
lean_object* v_toEditableDocumentCore_4207_; lean_object* v_meta_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4228_; 
v_toEditableDocumentCore_4207_ = lean_ctor_get(v_a_4181_, 0);
lean_inc_ref(v_toEditableDocumentCore_4207_);
v_meta_4208_ = lean_ctor_get(v_toEditableDocumentCore_4207_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v_toEditableDocumentCore_4207_);
if (v_isSharedCheck_4228_ == 0)
{
lean_object* v_unused_4229_; lean_object* v_unused_4230_; lean_object* v_unused_4231_; 
v_unused_4229_ = lean_ctor_get(v_toEditableDocumentCore_4207_, 3);
lean_dec(v_unused_4229_);
v_unused_4230_ = lean_ctor_get(v_toEditableDocumentCore_4207_, 2);
lean_dec(v_unused_4230_);
v_unused_4231_ = lean_ctor_get(v_toEditableDocumentCore_4207_, 1);
lean_dec(v_unused_4231_);
v___x_4210_ = v_toEditableDocumentCore_4207_;
v_isShared_4211_ = v_isSharedCheck_4228_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_meta_4208_);
lean_dec(v_toEditableDocumentCore_4207_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4228_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v_text_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4218_; 
v_text_4212_ = lean_ctor_get(v_meta_4208_, 3);
lean_inc_ref(v_text_4212_);
lean_dec_ref(v_meta_4208_);
v___x_4213_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4181_);
v___x_4214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4214_, 0, v_val_4193_);
lean_ctor_set(v___x_4214_, 1, v_val_4201_);
v___x_4215_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4212_, v___x_4214_);
v___x_4216_ = lean_box(0);
lean_inc(v___x_4182_);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 3, v___x_4182_);
lean_ctor_set(v___x_4210_, 2, v___x_4216_);
lean_ctor_set(v___x_4210_, 1, v___y_4206_);
lean_ctor_set(v___x_4210_, 0, v___x_4215_);
v___x_4218_ = v___x_4210_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4215_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v___y_4206_);
lean_ctor_set(v_reuseFailAlloc_4227_, 2, v___x_4216_);
lean_ctor_set(v_reuseFailAlloc_4227_, 3, v___x_4182_);
v___x_4218_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
lean_object* v___x_4219_; lean_object* v___x_4221_; 
v___x_4219_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4213_, v___x_4218_);
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 0, v___x_4219_);
v___x_4221_ = v___x_4203_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
lean_object* v___x_4222_; lean_object* v___x_4224_; 
lean_inc(v___x_4182_);
v___x_4222_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4182_);
lean_ctor_set(v___x_4222_, 1, v___x_4182_);
lean_ctor_set(v___x_4222_, 2, v___x_4183_);
lean_ctor_set(v___x_4222_, 3, v___x_4184_);
lean_ctor_set(v___x_4222_, 4, v___x_4185_);
lean_ctor_set(v___x_4222_, 5, v___x_4186_);
lean_ctor_set(v___x_4222_, 6, v___x_4187_);
lean_ctor_set(v___x_4222_, 7, v___x_4221_);
lean_ctor_set(v___x_4222_, 8, v___x_4188_);
lean_ctor_set(v___x_4222_, 9, v___x_4189_);
if (v_isShared_4196_ == 0)
{
lean_ctor_set_tag(v___x_4195_, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4222_);
v___x_4224_ = v___x_4195_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4222_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
}
v___jp_4233_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4234_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4235_ = lean_string_append(v___x_4234_, v___x_4232_);
lean_dec_ref(v___x_4232_);
v___x_4236_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4237_ = lean_string_append(v___x_4235_, v___x_4236_);
v___y_4206_ = v___x_4237_;
goto v___jp_4205_;
}
}
}
else
{
lean_object* v___x_4252_; 
lean_dec(v___x_4200_);
lean_dec(v_val_4193_);
lean_dec_ref(v_snd_4190_);
lean_dec(v___x_4189_);
lean_dec(v___x_4188_);
lean_dec(v___x_4187_);
lean_dec(v___x_4186_);
lean_dec(v___x_4185_);
lean_dec(v___x_4184_);
lean_dec_ref(v___x_4183_);
lean_dec(v___x_4182_);
lean_dec_ref(v_a_4181_);
if (v_isShared_4196_ == 0)
{
lean_ctor_set_tag(v___x_4195_, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4191_);
v___x_4252_ = v___x_4195_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4191_);
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
else
{
lean_object* v___x_4255_; 
lean_dec_ref(v_snd_4190_);
lean_dec(v___x_4189_);
lean_dec(v___x_4188_);
lean_dec(v___x_4187_);
lean_dec(v___x_4186_);
lean_dec(v___x_4185_);
lean_dec(v___x_4184_);
lean_dec_ref(v___x_4183_);
lean_dec(v___x_4182_);
lean_dec_ref(v_a_4181_);
lean_dec(v_fst_4179_);
lean_dec(v___x_4178_);
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4191_);
return v___x_4255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4256_, lean_object* v_fst_4257_, lean_object* v___x_4258_, lean_object* v_a_4259_, lean_object* v___x_4260_, lean_object* v___x_4261_, lean_object* v___x_4262_, lean_object* v___x_4263_, lean_object* v___x_4264_, lean_object* v___x_4265_, lean_object* v___x_4266_, lean_object* v___x_4267_, lean_object* v_snd_4268_, lean_object* v___x_4269_, lean_object* v___y_4270_){
_start:
{
uint8_t v___x_4482__boxed_4271_; lean_object* v_res_4272_; 
v___x_4482__boxed_4271_ = lean_unbox(v___x_4258_);
v_res_4272_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4256_, v_fst_4257_, v___x_4482__boxed_4271_, v_a_4259_, v___x_4260_, v___x_4261_, v___x_4262_, v___x_4263_, v___x_4264_, v___x_4265_, v___x_4266_, v___x_4267_, v_snd_4268_, v___x_4269_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4276_, size_t v_sz_4277_, size_t v_i_4278_, lean_object* v_b_4279_){
_start:
{
lean_object* v_a_4281_; uint8_t v___x_4285_; 
v___x_4285_ = lean_usize_dec_lt(v_i_4278_, v_sz_4277_);
if (v___x_4285_ == 0)
{
lean_inc_ref(v_b_4279_);
return v_b_4279_;
}
else
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v_a_4288_; 
v___x_4286_ = lean_box(0);
v___x_4287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4288_ = lean_array_uget(v_as_4276_, v_i_4278_);
if (lean_obj_tag(v_a_4288_) == 1)
{
lean_object* v_i_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4323_; 
v_i_4289_ = lean_ctor_get(v_a_4288_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v_a_4288_);
if (v_isSharedCheck_4323_ == 0)
{
lean_object* v_unused_4324_; 
v_unused_4324_ = lean_ctor_get(v_a_4288_, 1);
lean_dec(v_unused_4324_);
v___x_4291_ = v_a_4288_;
v_isShared_4292_ = v_isSharedCheck_4323_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_i_4289_);
lean_dec(v_a_4288_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4323_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
if (lean_obj_tag(v_i_4289_) == 10)
{
lean_object* v_i_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4322_; 
v_i_4293_ = lean_ctor_get(v_i_4289_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v_i_4289_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4295_ = v_i_4289_;
v_isShared_4296_ = v_isSharedCheck_4322_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_i_4293_);
lean_dec(v_i_4289_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4322_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v_stx_4297_; lean_object* v_value_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4321_; 
v_stx_4297_ = lean_ctor_get(v_i_4293_, 0);
v_value_4298_ = lean_ctor_get(v_i_4293_, 1);
v_isSharedCheck_4321_ = !lean_is_exclusive(v_i_4293_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4300_ = v_i_4293_;
v_isShared_4301_ = v_isSharedCheck_4321_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_value_4298_);
lean_inc(v_stx_4297_);
lean_dec(v_i_4293_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4321_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4302_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4303_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4298_, v___x_4302_);
lean_dec(v_value_4298_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_del_object(v___x_4300_);
lean_dec(v_stx_4297_);
lean_del_object(v___x_4295_);
lean_del_object(v___x_4291_);
v_a_4281_ = v___x_4287_;
goto v___jp_4280_;
}
else
{
lean_object* v_val_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4320_; 
v_val_4304_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4306_ = v___x_4303_;
v_isShared_4307_ = v_isSharedCheck_4320_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_val_4304_);
lean_dec(v___x_4303_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4320_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 1, v_val_4304_);
v___x_4309_ = v___x_4300_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_stx_4297_);
lean_ctor_set(v_reuseFailAlloc_4319_, 1, v_val_4304_);
v___x_4309_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
lean_object* v___x_4311_; 
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 0, v___x_4309_);
v___x_4311_ = v___x_4306_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4309_);
v___x_4311_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
lean_object* v___x_4313_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set_tag(v___x_4295_, 1);
lean_ctor_set(v___x_4295_, 0, v___x_4311_);
v___x_4313_ = v___x_4295_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4311_);
v___x_4313_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
lean_object* v___x_4315_; 
if (v_isShared_4292_ == 0)
{
lean_ctor_set_tag(v___x_4291_, 0);
lean_ctor_set(v___x_4291_, 1, v___x_4286_);
lean_ctor_set(v___x_4291_, 0, v___x_4313_);
v___x_4315_ = v___x_4291_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4313_);
lean_ctor_set(v_reuseFailAlloc_4316_, 1, v___x_4286_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
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
lean_del_object(v___x_4291_);
lean_dec_ref(v_i_4289_);
v_a_4281_ = v___x_4287_;
goto v___jp_4280_;
}
}
}
else
{
lean_dec(v_a_4288_);
v_a_4281_ = v___x_4287_;
goto v___jp_4280_;
}
}
v___jp_4280_:
{
size_t v___x_4282_; size_t v___x_4283_; 
v___x_4282_ = ((size_t)1ULL);
v___x_4283_ = lean_usize_add(v_i_4278_, v___x_4282_);
v_i_4278_ = v___x_4283_;
v_b_4279_ = v_a_4281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4325_, lean_object* v_sz_4326_, lean_object* v_i_4327_, lean_object* v_b_4328_){
_start:
{
size_t v_sz_boxed_4329_; size_t v_i_boxed_4330_; lean_object* v_res_4331_; 
v_sz_boxed_4329_ = lean_unbox_usize(v_sz_4326_);
lean_dec(v_sz_4326_);
v_i_boxed_4330_ = lean_unbox_usize(v_i_4327_);
lean_dec(v_i_4327_);
v_res_4331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4325_, v_sz_boxed_4329_, v_i_boxed_4330_, v_b_4328_);
lean_dec_ref(v_b_4328_);
lean_dec_ref(v_as_4325_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4332_, size_t v_sz_4333_, size_t v_i_4334_, lean_object* v_b_4335_){
_start:
{
lean_object* v_a_4337_; uint8_t v___x_4341_; 
v___x_4341_ = lean_usize_dec_lt(v_i_4334_, v_sz_4333_);
if (v___x_4341_ == 0)
{
lean_inc_ref(v_b_4335_);
return v_b_4335_;
}
else
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v_a_4344_; 
v___x_4342_ = lean_box(0);
v___x_4343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4344_ = lean_array_uget(v_as_4332_, v_i_4334_);
if (lean_obj_tag(v_a_4344_) == 1)
{
lean_object* v_i_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4379_; 
v_i_4345_ = lean_ctor_get(v_a_4344_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v_a_4344_);
if (v_isSharedCheck_4379_ == 0)
{
lean_object* v_unused_4380_; 
v_unused_4380_ = lean_ctor_get(v_a_4344_, 1);
lean_dec(v_unused_4380_);
v___x_4347_ = v_a_4344_;
v_isShared_4348_ = v_isSharedCheck_4379_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_i_4345_);
lean_dec(v_a_4344_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4379_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
if (lean_obj_tag(v_i_4345_) == 10)
{
lean_object* v_i_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4378_; 
v_i_4349_ = lean_ctor_get(v_i_4345_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v_i_4345_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4351_ = v_i_4345_;
v_isShared_4352_ = v_isSharedCheck_4378_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_i_4349_);
lean_dec(v_i_4345_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4378_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v_stx_4353_; lean_object* v_value_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4377_; 
v_stx_4353_ = lean_ctor_get(v_i_4349_, 0);
v_value_4354_ = lean_ctor_get(v_i_4349_, 1);
v_isSharedCheck_4377_ = !lean_is_exclusive(v_i_4349_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4356_ = v_i_4349_;
v_isShared_4357_ = v_isSharedCheck_4377_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_value_4354_);
lean_inc(v_stx_4353_);
lean_dec(v_i_4349_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4377_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4358_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4359_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4354_, v___x_4358_);
lean_dec(v_value_4354_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_del_object(v___x_4356_);
lean_dec(v_stx_4353_);
lean_del_object(v___x_4351_);
lean_del_object(v___x_4347_);
v_a_4337_ = v___x_4343_;
goto v___jp_4336_;
}
else
{
lean_object* v_val_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4376_; 
v_val_4360_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4362_ = v___x_4359_;
v_isShared_4363_ = v_isSharedCheck_4376_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_val_4360_);
lean_dec(v___x_4359_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4376_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 1, v_val_4360_);
v___x_4365_ = v___x_4356_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_stx_4353_);
lean_ctor_set(v_reuseFailAlloc_4375_, 1, v_val_4360_);
v___x_4365_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
lean_object* v___x_4367_; 
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 0, v___x_4365_);
v___x_4367_ = v___x_4362_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4365_);
v___x_4367_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
lean_object* v___x_4369_; 
if (v_isShared_4352_ == 0)
{
lean_ctor_set_tag(v___x_4351_, 1);
lean_ctor_set(v___x_4351_, 0, v___x_4367_);
v___x_4369_ = v___x_4351_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4367_);
v___x_4369_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
lean_object* v___x_4371_; 
if (v_isShared_4348_ == 0)
{
lean_ctor_set_tag(v___x_4347_, 0);
lean_ctor_set(v___x_4347_, 1, v___x_4342_);
lean_ctor_set(v___x_4347_, 0, v___x_4369_);
v___x_4371_ = v___x_4347_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4369_);
lean_ctor_set(v_reuseFailAlloc_4372_, 1, v___x_4342_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
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
lean_del_object(v___x_4347_);
lean_dec_ref(v_i_4345_);
v_a_4337_ = v___x_4343_;
goto v___jp_4336_;
}
}
}
else
{
lean_dec(v_a_4344_);
v_a_4337_ = v___x_4343_;
goto v___jp_4336_;
}
}
v___jp_4336_:
{
size_t v___x_4338_; size_t v___x_4339_; lean_object* v___x_4340_; 
v___x_4338_ = ((size_t)1ULL);
v___x_4339_ = lean_usize_add(v_i_4334_, v___x_4338_);
v___x_4340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4332_, v_sz_4333_, v___x_4339_, v_a_4337_);
return v___x_4340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4381_, lean_object* v_sz_4382_, lean_object* v_i_4383_, lean_object* v_b_4384_){
_start:
{
size_t v_sz_boxed_4385_; size_t v_i_boxed_4386_; lean_object* v_res_4387_; 
v_sz_boxed_4385_ = lean_unbox_usize(v_sz_4382_);
lean_dec(v_sz_4382_);
v_i_boxed_4386_ = lean_unbox_usize(v_i_4383_);
lean_dec(v_i_4383_);
v_res_4387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4381_, v_sz_boxed_4385_, v_i_boxed_4386_, v_b_4384_);
lean_dec_ref(v_b_4384_);
lean_dec_ref(v_as_4381_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4388_){
_start:
{
if (lean_obj_tag(v_x_4388_) == 0)
{
lean_object* v_cs_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; size_t v_sz_4392_; size_t v___x_4393_; lean_object* v___x_4394_; lean_object* v_fst_4395_; 
v_cs_4389_ = lean_ctor_get(v_x_4388_, 0);
v___x_4390_ = lean_box(0);
v___x_4391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4392_ = lean_array_size(v_cs_4389_);
v___x_4393_ = ((size_t)0ULL);
v___x_4394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4389_, v_sz_4392_, v___x_4393_, v___x_4391_);
v_fst_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_fst_4395_);
lean_dec_ref(v___x_4394_);
if (lean_obj_tag(v_fst_4395_) == 0)
{
return v___x_4390_;
}
else
{
lean_object* v_val_4396_; 
v_val_4396_ = lean_ctor_get(v_fst_4395_, 0);
lean_inc(v_val_4396_);
lean_dec_ref_known(v_fst_4395_, 1);
return v_val_4396_;
}
}
else
{
lean_object* v_vs_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; size_t v_sz_4400_; size_t v___x_4401_; lean_object* v___x_4402_; lean_object* v_fst_4403_; 
v_vs_4397_ = lean_ctor_get(v_x_4388_, 0);
v___x_4398_ = lean_box(0);
v___x_4399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4400_ = lean_array_size(v_vs_4397_);
v___x_4401_ = ((size_t)0ULL);
v___x_4402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4397_, v_sz_4400_, v___x_4401_, v___x_4399_);
v_fst_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_fst_4403_);
lean_dec_ref(v___x_4402_);
if (lean_obj_tag(v_fst_4403_) == 0)
{
return v___x_4398_;
}
else
{
lean_object* v_val_4404_; 
v_val_4404_ = lean_ctor_get(v_fst_4403_, 0);
lean_inc(v_val_4404_);
lean_dec_ref_known(v_fst_4403_, 1);
return v_val_4404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4405_, size_t v_sz_4406_, size_t v_i_4407_, lean_object* v_b_4408_){
_start:
{
uint8_t v___x_4409_; 
v___x_4409_ = lean_usize_dec_lt(v_i_4407_, v_sz_4406_);
if (v___x_4409_ == 0)
{
lean_inc_ref(v_b_4408_);
return v_b_4408_;
}
else
{
lean_object* v___x_4410_; lean_object* v_a_4411_; lean_object* v___x_4412_; 
v___x_4410_ = lean_box(0);
v_a_4411_ = lean_array_uget_borrowed(v_as_4405_, v_i_4407_);
v___x_4412_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4411_);
if (lean_obj_tag(v___x_4412_) == 1)
{
lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4412_);
v___x_4414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4413_);
lean_ctor_set(v___x_4414_, 1, v___x_4410_);
return v___x_4414_;
}
else
{
lean_object* v___x_4415_; size_t v___x_4416_; size_t v___x_4417_; 
lean_dec(v___x_4412_);
v___x_4415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4416_ = ((size_t)1ULL);
v___x_4417_ = lean_usize_add(v_i_4407_, v___x_4416_);
v_i_4407_ = v___x_4417_;
v_b_4408_ = v___x_4415_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4419_, lean_object* v_sz_4420_, lean_object* v_i_4421_, lean_object* v_b_4422_){
_start:
{
size_t v_sz_boxed_4423_; size_t v_i_boxed_4424_; lean_object* v_res_4425_; 
v_sz_boxed_4423_ = lean_unbox_usize(v_sz_4420_);
lean_dec(v_sz_4420_);
v_i_boxed_4424_ = lean_unbox_usize(v_i_4421_);
lean_dec(v_i_4421_);
v_res_4425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4419_, v_sz_boxed_4423_, v_i_boxed_4424_, v_b_4422_);
lean_dec_ref(v_b_4422_);
lean_dec_ref(v_as_4419_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4426_);
lean_dec_ref(v_x_4426_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4428_){
_start:
{
lean_object* v_root_4429_; lean_object* v_tail_4430_; lean_object* v___x_4431_; 
v_root_4429_ = lean_ctor_get(v_t_4428_, 0);
v_tail_4430_ = lean_ctor_get(v_t_4428_, 1);
v___x_4431_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4429_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v___x_4432_; size_t v_sz_4433_; size_t v___x_4434_; lean_object* v___x_4435_; lean_object* v_fst_4436_; 
v___x_4432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4433_ = lean_array_size(v_tail_4430_);
v___x_4434_ = ((size_t)0ULL);
v___x_4435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4430_, v_sz_4433_, v___x_4434_, v___x_4432_);
v_fst_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_fst_4436_);
lean_dec_ref(v___x_4435_);
if (lean_obj_tag(v_fst_4436_) == 0)
{
return v___x_4431_;
}
else
{
lean_object* v_val_4437_; 
v_val_4437_ = lean_ctor_get(v_fst_4436_, 0);
lean_inc(v_val_4437_);
lean_dec_ref_known(v_fst_4436_, 1);
return v_val_4437_;
}
}
else
{
return v___x_4431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4438_);
lean_dec_ref(v_t_4438_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4454_, lean_object* v_a_4455_){
_start:
{
if (lean_obj_tag(v_node_4454_) == 1)
{
lean_object* v_children_4457_; lean_object* v_res_4458_; 
v_children_4457_ = lean_ctor_get(v_node_4454_, 1);
v_res_4458_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4457_);
if (lean_obj_tag(v_res_4458_) == 1)
{
lean_object* v_val_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4496_; 
v_val_4459_ = lean_ctor_get(v_res_4458_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v_res_4458_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4461_ = v_res_4458_;
v_isShared_4462_ = v_isSharedCheck_4496_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_val_4459_);
lean_dec(v_res_4458_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4496_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v_fst_4463_; lean_object* v_snd_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4495_; 
v_fst_4463_ = lean_ctor_get(v_val_4459_, 0);
v_snd_4464_ = lean_ctor_get(v_val_4459_, 1);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_val_4459_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4466_ = v_val_4459_;
v_isShared_4467_ = v_isSharedCheck_4495_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_snd_4464_);
lean_inc(v_fst_4463_);
lean_dec(v_val_4459_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4495_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4468_; lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4494_; 
v___x_4468_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4455_);
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4471_ = v___x_4468_;
v_isShared_4472_ = v_isSharedCheck_4494_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4468_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4494_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; uint8_t v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___y_4481_; lean_object* v___x_4483_; 
v___x_4473_ = lean_box(0);
v___x_4474_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4475_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4476_ = 1;
v___x_4477_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4478_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4479_ = l_Lean_Syntax_getPos_x3f(v_fst_4463_, v___x_4476_);
v___x_4480_ = lean_box(v___x_4476_);
v___y_4481_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4481_, 0, v___x_4479_);
lean_closure_set(v___y_4481_, 1, v_fst_4463_);
lean_closure_set(v___y_4481_, 2, v___x_4480_);
lean_closure_set(v___y_4481_, 3, v_a_4469_);
lean_closure_set(v___y_4481_, 4, v___x_4473_);
lean_closure_set(v___y_4481_, 5, v___x_4474_);
lean_closure_set(v___y_4481_, 6, v___x_4475_);
lean_closure_set(v___y_4481_, 7, v___x_4473_);
lean_closure_set(v___y_4481_, 8, v___x_4477_);
lean_closure_set(v___y_4481_, 9, v___x_4473_);
lean_closure_set(v___y_4481_, 10, v___x_4473_);
lean_closure_set(v___y_4481_, 11, v___x_4473_);
lean_closure_set(v___y_4481_, 12, v_snd_4464_);
lean_closure_set(v___y_4481_, 13, v___x_4478_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v___y_4481_);
v___x_4483_ = v___x_4461_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___y_4481_);
v___x_4483_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4485_; 
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 1, v___x_4483_);
lean_ctor_set(v___x_4466_, 0, v___x_4478_);
v___x_4485_ = v___x_4466_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4478_);
lean_ctor_set(v_reuseFailAlloc_4492_, 1, v___x_4483_);
v___x_4485_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4490_; 
v___x_4486_ = lean_unsigned_to_nat(1u);
v___x_4487_ = lean_mk_empty_array_with_capacity(v___x_4486_);
v___x_4488_ = lean_array_push(v___x_4487_, v___x_4485_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 0, v___x_4488_);
v___x_4490_ = v___x_4471_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4488_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
lean_dec(v_res_4458_);
v___x_4497_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
return v___x_4498_;
}
}
else
{
lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4499_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
return v___x_4500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4501_, v_a_4502_);
lean_dec_ref(v_a_4502_);
lean_dec_ref(v_node_4501_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4505_, lean_object* v_x_4506_, lean_object* v_x_4507_, lean_object* v_node_4508_, lean_object* v_a_4509_){
_start:
{
lean_object* v___x_4511_; 
v___x_4511_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4508_, v_a_4509_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4512_, lean_object* v_x_4513_, lean_object* v_x_4514_, lean_object* v_node_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4512_, v_x_4513_, v_x_4514_, v_node_4515_, v_a_4516_);
lean_dec_ref(v_a_4516_);
lean_dec_ref(v_node_4515_);
lean_dec_ref(v_x_4514_);
lean_dec_ref(v_x_4513_);
lean_dec_ref(v_x_4512_);
return v_res_4518_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4519_, lean_object* v_inst_4520_, lean_object* v_R_4521_, lean_object* v_a_4522_, uint8_t v_b_4523_, lean_object* v_c_4524_){
_start:
{
uint8_t v___x_4525_; 
v___x_4525_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4519_, v_a_4522_, v_b_4523_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4526_, lean_object* v_inst_4527_, lean_object* v_R_4528_, lean_object* v_a_4529_, lean_object* v_b_4530_, lean_object* v_c_4531_){
_start:
{
uint8_t v_b_boxed_4532_; uint8_t v_res_4533_; lean_object* v_r_4534_; 
v_b_boxed_4532_ = lean_unbox(v_b_4530_);
v_res_4533_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4526_, v_inst_4527_, v_R_4528_, v_a_4529_, v_b_boxed_4532_, v_c_4531_);
lean_dec_ref(v_s_4526_);
v_r_4534_ = lean_box(v_res_4533_);
return v_r_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_(){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_));
v___x_4541_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4542_ = l_Lean_CodeAction_insertBuiltin(v___x_4540_, v___x_4541_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354____boxed(lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_();
return v_res_4544_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___x_4550_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4551_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4550_);
return v___x_4551_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4552_ = lean_unsigned_to_nat(0u);
v___x_4553_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
v___x_4554_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4555_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
lean_ctor_set(v___x_4555_, 1, v___x_4553_);
lean_ctor_set(v___x_4555_, 2, v___x_4552_);
lean_ctor_set(v___x_4555_, 3, v___x_4552_);
return v___x_4555_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4556_){
_start:
{
lean_object* v___x_4557_; uint8_t v___x_4558_; uint8_t v___x_4559_; 
v___x_4557_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4558_ = 0;
v___x_4559_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4556_, v___x_4557_, v___x_4558_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4560_){
_start:
{
uint8_t v_res_4561_; lean_object* v_r_4562_; 
v_res_4561_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4560_);
lean_dec_ref(v_s_4560_);
v_r_4562_ = lean_box(v_res_4561_);
return v_r_4562_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4563_, lean_object* v_as_x27_4564_, uint8_t v_b_4565_){
_start:
{
if (lean_obj_tag(v_as_x27_4564_) == 0)
{
lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4567_ = lean_box(v_b_4565_);
v___x_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
return v___x_4568_;
}
else
{
lean_object* v_head_4569_; uint8_t v_isSilent_4570_; 
v_head_4569_ = lean_ctor_get(v_as_x27_4564_, 0);
v_isSilent_4570_ = lean_ctor_get_uint8(v_head_4569_, sizeof(void*)*5 + 2);
if (v_isSilent_4570_ == 0)
{
lean_object* v_tail_4571_; lean_object* v_data_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; uint8_t v___x_4577_; 
v_tail_4571_ = lean_ctor_get(v_as_x27_4564_, 1);
v_data_4572_ = lean_ctor_get(v_head_4569_, 4);
lean_inc(v_data_4572_);
v___x_4573_ = l_Lean_MessageData_toString(v_data_4572_);
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = lean_string_utf8_byte_size(v___x_4573_);
v___x_4576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4573_);
lean_ctor_set(v___x_4576_, 1, v___x_4574_);
lean_ctor_set(v___x_4576_, 2, v___x_4575_);
v___x_4577_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4576_);
lean_dec_ref_known(v___x_4576_, 3);
if (v___x_4577_ == 0)
{
v_as_x27_4564_ = v_tail_4571_;
goto _start;
}
else
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4579_ = lean_box(v_foundPanic_4563_);
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
return v___x_4580_;
}
}
else
{
lean_object* v_tail_4581_; 
v_tail_4581_ = lean_ctor_get(v_as_x27_4564_, 1);
v_as_x27_4564_ = v_tail_4581_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4583_, lean_object* v_as_x27_4584_, lean_object* v_b_4585_, lean_object* v___y_4586_){
_start:
{
uint8_t v_foundPanic_boxed_4587_; uint8_t v_b_boxed_4588_; lean_object* v_res_4589_; 
v_foundPanic_boxed_4587_ = lean_unbox(v_foundPanic_4583_);
v_b_boxed_4588_ = lean_unbox(v_b_4585_);
v_res_4589_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4587_, v_as_x27_4584_, v_b_boxed_4588_);
lean_dec(v_as_x27_4584_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4590_, uint8_t v_severity_4591_, uint8_t v_isSilent_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v___x_4596_; 
v___x_4596_ = l_Lean_Elab_Command_getRef___redArg(v___y_4593_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4598_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref_known(v___x_4596_, 1);
v___x_4598_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4597_, v_msgData_4590_, v_severity_4591_, v_isSilent_4592_, v___y_4593_, v___y_4594_);
lean_dec(v_a_4597_);
return v___x_4598_;
}
else
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4606_; 
lean_dec_ref(v_msgData_4590_);
v_a_4599_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4601_ = v___x_4596_;
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4596_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4604_; 
if (v_isShared_4602_ == 0)
{
v___x_4604_ = v___x_4601_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4607_, lean_object* v_severity_4608_, lean_object* v_isSilent_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
uint8_t v_severity_boxed_4613_; uint8_t v_isSilent_boxed_4614_; lean_object* v_res_4615_; 
v_severity_boxed_4613_ = lean_unbox(v_severity_4608_);
v_isSilent_boxed_4614_ = lean_unbox(v_isSilent_4609_);
v_res_4615_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4607_, v_severity_boxed_4613_, v_isSilent_boxed_4614_, v___y_4610_, v___y_4611_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
uint8_t v___x_4620_; uint8_t v___x_4621_; lean_object* v___x_4622_; 
v___x_4620_ = 2;
v___x_4621_ = 0;
v___x_4622_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4616_, v___x_4620_, v___x_4621_, v___y_4617_, v___y_4618_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4623_, v___y_4624_, v___y_4625_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
return v_res_4627_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4636_ = l_Lean_MessageData_ofFormat(v___x_4635_);
return v___x_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_){
_start:
{
lean_object* v___x_4641_; uint8_t v_foundPanic_4642_; 
v___x_4641_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4637_);
v_foundPanic_4642_ = l_Lean_Syntax_isOfKind(v_x_4637_, v___x_4641_);
if (v_foundPanic_4642_ == 0)
{
lean_object* v___x_4643_; 
lean_dec(v_x_4637_);
v___x_4643_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4643_;
}
else
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4644_ = lean_unsigned_to_nat(2u);
v___x_4645_ = l_Lean_Syntax_getArg(v_x_4637_, v___x_4644_);
lean_dec(v_x_4637_);
v___x_4646_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4645_, v_a_4638_, v_a_4639_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; uint8_t v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4707_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
lean_dec_ref_known(v___x_4646_, 1);
v___x_4648_ = 0;
v___x_4649_ = l_Lean_MessageLog_toList(v_a_4647_);
v___x_4650_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4642_, v___x_4649_, v___x_4648_);
lean_dec(v___x_4649_);
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4653_ = v___x_4650_;
v_isShared_4654_ = v_isSharedCheck_4707_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4650_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4707_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
uint8_t v___x_4655_; 
v___x_4655_ = lean_unbox(v_a_4651_);
lean_dec(v_a_4651_);
if (v___x_4655_ == 0)
{
lean_object* v___x_4656_; lean_object* v_env_4657_; lean_object* v_scopes_4658_; lean_object* v_usedQuotCtxts_4659_; lean_object* v_nextMacroScope_4660_; lean_object* v_maxRecDepth_4661_; lean_object* v_ngen_4662_; lean_object* v_auxDeclNGen_4663_; lean_object* v_infoState_4664_; lean_object* v_traceState_4665_; lean_object* v_snapshotTasks_4666_; lean_object* v_prevLinterStates_4667_; lean_object* v_codeQualityEntryTasks_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4678_; 
lean_del_object(v___x_4653_);
v___x_4656_ = lean_st_ref_take(v_a_4639_);
v_env_4657_ = lean_ctor_get(v___x_4656_, 0);
v_scopes_4658_ = lean_ctor_get(v___x_4656_, 2);
v_usedQuotCtxts_4659_ = lean_ctor_get(v___x_4656_, 3);
v_nextMacroScope_4660_ = lean_ctor_get(v___x_4656_, 4);
v_maxRecDepth_4661_ = lean_ctor_get(v___x_4656_, 5);
v_ngen_4662_ = lean_ctor_get(v___x_4656_, 6);
v_auxDeclNGen_4663_ = lean_ctor_get(v___x_4656_, 7);
v_infoState_4664_ = lean_ctor_get(v___x_4656_, 8);
v_traceState_4665_ = lean_ctor_get(v___x_4656_, 9);
v_snapshotTasks_4666_ = lean_ctor_get(v___x_4656_, 10);
v_prevLinterStates_4667_ = lean_ctor_get(v___x_4656_, 11);
v_codeQualityEntryTasks_4668_ = lean_ctor_get(v___x_4656_, 12);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4678_ == 0)
{
lean_object* v_unused_4679_; 
v_unused_4679_ = lean_ctor_get(v___x_4656_, 1);
lean_dec(v_unused_4679_);
v___x_4670_ = v___x_4656_;
v_isShared_4671_ = v_isSharedCheck_4678_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4668_);
lean_inc(v_prevLinterStates_4667_);
lean_inc(v_snapshotTasks_4666_);
lean_inc(v_traceState_4665_);
lean_inc(v_infoState_4664_);
lean_inc(v_auxDeclNGen_4663_);
lean_inc(v_ngen_4662_);
lean_inc(v_maxRecDepth_4661_);
lean_inc(v_nextMacroScope_4660_);
lean_inc(v_usedQuotCtxts_4659_);
lean_inc(v_scopes_4658_);
lean_inc(v_env_4657_);
lean_dec(v___x_4656_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4678_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 1, v_a_4647_);
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_env_4657_);
lean_ctor_set(v_reuseFailAlloc_4677_, 1, v_a_4647_);
lean_ctor_set(v_reuseFailAlloc_4677_, 2, v_scopes_4658_);
lean_ctor_set(v_reuseFailAlloc_4677_, 3, v_usedQuotCtxts_4659_);
lean_ctor_set(v_reuseFailAlloc_4677_, 4, v_nextMacroScope_4660_);
lean_ctor_set(v_reuseFailAlloc_4677_, 5, v_maxRecDepth_4661_);
lean_ctor_set(v_reuseFailAlloc_4677_, 6, v_ngen_4662_);
lean_ctor_set(v_reuseFailAlloc_4677_, 7, v_auxDeclNGen_4663_);
lean_ctor_set(v_reuseFailAlloc_4677_, 8, v_infoState_4664_);
lean_ctor_set(v_reuseFailAlloc_4677_, 9, v_traceState_4665_);
lean_ctor_set(v_reuseFailAlloc_4677_, 10, v_snapshotTasks_4666_);
lean_ctor_set(v_reuseFailAlloc_4677_, 11, v_prevLinterStates_4667_);
lean_ctor_set(v_reuseFailAlloc_4677_, 12, v_codeQualityEntryTasks_4668_);
v___x_4673_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4674_ = lean_st_ref_put(v_a_4639_, v___x_4673_);
v___x_4675_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4676_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4675_, v_a_4638_, v_a_4639_);
return v___x_4676_;
}
}
}
else
{
lean_object* v___x_4680_; lean_object* v_env_4681_; lean_object* v_scopes_4682_; lean_object* v_usedQuotCtxts_4683_; lean_object* v_nextMacroScope_4684_; lean_object* v_maxRecDepth_4685_; lean_object* v_ngen_4686_; lean_object* v_auxDeclNGen_4687_; lean_object* v_infoState_4688_; lean_object* v_traceState_4689_; lean_object* v_snapshotTasks_4690_; lean_object* v_prevLinterStates_4691_; lean_object* v_codeQualityEntryTasks_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4705_; 
lean_dec(v_a_4647_);
v___x_4680_ = lean_st_ref_take(v_a_4639_);
v_env_4681_ = lean_ctor_get(v___x_4680_, 0);
v_scopes_4682_ = lean_ctor_get(v___x_4680_, 2);
v_usedQuotCtxts_4683_ = lean_ctor_get(v___x_4680_, 3);
v_nextMacroScope_4684_ = lean_ctor_get(v___x_4680_, 4);
v_maxRecDepth_4685_ = lean_ctor_get(v___x_4680_, 5);
v_ngen_4686_ = lean_ctor_get(v___x_4680_, 6);
v_auxDeclNGen_4687_ = lean_ctor_get(v___x_4680_, 7);
v_infoState_4688_ = lean_ctor_get(v___x_4680_, 8);
v_traceState_4689_ = lean_ctor_get(v___x_4680_, 9);
v_snapshotTasks_4690_ = lean_ctor_get(v___x_4680_, 10);
v_prevLinterStates_4691_ = lean_ctor_get(v___x_4680_, 11);
v_codeQualityEntryTasks_4692_ = lean_ctor_get(v___x_4680_, 12);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4705_ == 0)
{
lean_object* v_unused_4706_; 
v_unused_4706_ = lean_ctor_get(v___x_4680_, 1);
lean_dec(v_unused_4706_);
v___x_4694_ = v___x_4680_;
v_isShared_4695_ = v_isSharedCheck_4705_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4692_);
lean_inc(v_prevLinterStates_4691_);
lean_inc(v_snapshotTasks_4690_);
lean_inc(v_traceState_4689_);
lean_inc(v_infoState_4688_);
lean_inc(v_auxDeclNGen_4687_);
lean_inc(v_ngen_4686_);
lean_inc(v_maxRecDepth_4685_);
lean_inc(v_nextMacroScope_4684_);
lean_inc(v_usedQuotCtxts_4683_);
lean_inc(v_scopes_4682_);
lean_inc(v_env_4681_);
lean_dec(v___x_4680_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4705_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4699_; 
v___x_4696_ = lean_box(0);
v___x_4697_ = l_Lean_MessageLog_empty;
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 1, v___x_4697_);
v___x_4699_ = v___x_4694_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_env_4681_);
lean_ctor_set(v_reuseFailAlloc_4704_, 1, v___x_4697_);
lean_ctor_set(v_reuseFailAlloc_4704_, 2, v_scopes_4682_);
lean_ctor_set(v_reuseFailAlloc_4704_, 3, v_usedQuotCtxts_4683_);
lean_ctor_set(v_reuseFailAlloc_4704_, 4, v_nextMacroScope_4684_);
lean_ctor_set(v_reuseFailAlloc_4704_, 5, v_maxRecDepth_4685_);
lean_ctor_set(v_reuseFailAlloc_4704_, 6, v_ngen_4686_);
lean_ctor_set(v_reuseFailAlloc_4704_, 7, v_auxDeclNGen_4687_);
lean_ctor_set(v_reuseFailAlloc_4704_, 8, v_infoState_4688_);
lean_ctor_set(v_reuseFailAlloc_4704_, 9, v_traceState_4689_);
lean_ctor_set(v_reuseFailAlloc_4704_, 10, v_snapshotTasks_4690_);
lean_ctor_set(v_reuseFailAlloc_4704_, 11, v_prevLinterStates_4691_);
lean_ctor_set(v_reuseFailAlloc_4704_, 12, v_codeQualityEntryTasks_4692_);
v___x_4699_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
lean_object* v___x_4700_; lean_object* v___x_4702_; 
v___x_4700_ = lean_st_ref_put(v_a_4639_, v___x_4699_);
if (v_isShared_4654_ == 0)
{
lean_ctor_set(v___x_4653_, 0, v___x_4696_);
v___x_4702_ = v___x_4653_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4696_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
}
}
else
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4715_; 
v_a_4708_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4710_ = v___x_4646_;
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4646_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4713_; 
if (v_isShared_4711_ == 0)
{
v___x_4713_ = v___x_4710_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_){
_start:
{
lean_object* v_res_4720_; 
v_res_4720_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4716_, v_a_4717_, v_a_4718_);
lean_dec(v_a_4718_);
lean_dec_ref(v_a_4717_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4721_, lean_object* v_as_4722_, lean_object* v_as_x27_4723_, uint8_t v_b_4724_, lean_object* v_a_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v___x_4729_; 
v___x_4729_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4721_, v_as_x27_4723_, v_b_4724_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4730_, lean_object* v_as_4731_, lean_object* v_as_x27_4732_, lean_object* v_b_4733_, lean_object* v_a_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
uint8_t v_foundPanic_boxed_4738_; uint8_t v_b_boxed_4739_; lean_object* v_res_4740_; 
v_foundPanic_boxed_4738_ = lean_unbox(v_foundPanic_4730_);
v_b_boxed_4739_ = lean_unbox(v_b_4733_);
v_res_4740_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4738_, v_as_4731_, v_as_x27_4732_, v_b_boxed_4739_, v_a_4734_, v___y_4735_, v___y_4736_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v_as_x27_4732_);
lean_dec(v_as_4731_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4749_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4750_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4751_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4752_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4753_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4749_, v___x_4750_, v___x_4751_, v___x_4752_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4755_;
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
