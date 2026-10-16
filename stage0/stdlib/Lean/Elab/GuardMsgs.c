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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*);
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
uint8_t v___x_792__boxed_424_; uint8_t v_res_425_; lean_object* v_r_426_; 
v___x_792__boxed_424_ = lean_unbox(v___x_422_);
v_res_425_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0(v___x_792__boxed_424_, v_x_423_);
lean_dec_ref(v_x_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(uint8_t v___x_427_, lean_object* v_msg_428_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = l_Lean_Message_isTrace(v_msg_428_);
if (v___x_429_ == 0)
{
uint8_t v_severity_430_; uint8_t v___x_431_; uint8_t v___x_432_; 
v_severity_430_ = lean_ctor_get_uint8(v_msg_428_, sizeof(void*)*5 + 1);
v___x_431_ = 2;
v___x_432_ = l_Lean_instBEqMessageSeverity_beq(v_severity_430_, v___x_431_);
return v___x_432_;
}
else
{
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed(lean_object* v___x_433_, lean_object* v_msg_434_){
_start:
{
uint8_t v___x_798__boxed_435_; uint8_t v_res_436_; lean_object* v_r_437_; 
v___x_798__boxed_435_ = lean_unbox(v___x_433_);
v_res_436_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1(v___x_798__boxed_435_, v_msg_434_);
lean_dec_ref(v_msg_434_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(uint8_t v___x_438_, lean_object* v_msg_439_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = l_Lean_Message_isTrace(v_msg_439_);
if (v___x_440_ == 0)
{
uint8_t v_severity_441_; uint8_t v___x_442_; uint8_t v___x_443_; 
v_severity_441_ = lean_ctor_get_uint8(v_msg_439_, sizeof(void*)*5 + 1);
v___x_442_ = 1;
v___x_443_ = l_Lean_instBEqMessageSeverity_beq(v_severity_441_, v___x_442_);
return v___x_443_;
}
else
{
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed(lean_object* v___x_444_, lean_object* v_msg_445_){
_start:
{
uint8_t v___x_807__boxed_446_; uint8_t v_res_447_; lean_object* v_r_448_; 
v___x_807__boxed_446_ = lean_unbox(v___x_444_);
v_res_447_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2(v___x_807__boxed_446_, v_msg_445_);
lean_dec_ref(v_msg_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(uint8_t v___x_449_, lean_object* v_msg_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = l_Lean_Message_isTrace(v_msg_450_);
if (v___x_451_ == 0)
{
uint8_t v_severity_452_; uint8_t v___x_453_; uint8_t v___x_454_; 
v_severity_452_ = lean_ctor_get_uint8(v_msg_450_, sizeof(void*)*5 + 1);
v___x_453_ = 0;
v___x_454_ = l_Lean_instBEqMessageSeverity_beq(v_severity_452_, v___x_453_);
return v___x_454_;
}
else
{
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed(lean_object* v___x_455_, lean_object* v_msg_456_){
_start:
{
uint8_t v___x_816__boxed_457_; uint8_t v_res_458_; lean_object* v_r_459_; 
v___x_816__boxed_457_ = lean_unbox(v___x_455_);
v_res_458_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3(v___x_816__boxed_457_, v_msg_456_);
lean_dec_ref(v_msg_456_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(lean_object* v_x_485_){
_start:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__1));
lean_inc(v_x_485_);
v___x_488_ = l_Lean_Syntax_isOfKind(v_x_485_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_dec(v_x_485_);
v___x_489_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_489_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = l_Lean_Syntax_getArg(v_x_485_, v___x_490_);
lean_dec(v_x_485_);
v___x_492_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__3));
lean_inc(v___x_491_);
v___x_493_ = l_Lean_Syntax_isOfKind(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__5));
lean_inc(v___x_491_);
v___x_495_ = l_Lean_Syntax_isOfKind(v___x_491_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__7));
lean_inc(v___x_491_);
v___x_497_ = l_Lean_Syntax_isOfKind(v___x_491_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__9));
lean_inc(v___x_491_);
v___x_499_ = l_Lean_Syntax_isOfKind(v___x_491_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__11));
v___x_501_ = l_Lean_Syntax_isOfKind(v___x_491_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_502_;
}
else
{
lean_object* v___x_503_; lean_object* v___f_504_; lean_object* v___x_505_; 
v___x_503_ = lean_box(v___x_501_);
v___f_504_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_504_, 0, v___x_503_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___f_504_);
return v___x_505_;
}
}
else
{
lean_object* v___x_506_; lean_object* v___f_507_; lean_object* v___x_508_; 
lean_dec(v___x_491_);
v___x_506_ = lean_box(v___x_497_);
v___f_507_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_507_, 0, v___x_506_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___f_507_);
return v___x_508_;
}
}
else
{
lean_object* v___x_509_; lean_object* v___f_510_; lean_object* v___x_511_; 
lean_dec(v___x_491_);
v___x_509_ = lean_box(v___x_495_);
v___f_510_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_510_, 0, v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___f_510_);
return v___x_511_;
}
}
else
{
lean_object* v___x_512_; lean_object* v___f_513_; lean_object* v___x_514_; 
lean_dec(v___x_491_);
v___x_512_ = lean_box(v___x_493_);
v___f_513_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_513_, 0, v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___f_513_);
return v___x_514_;
}
}
else
{
lean_object* v___f_515_; lean_object* v___x_516_; 
lean_dec(v___x_491_);
v___f_515_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__12));
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___f_515_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___boxed(lean_object* v_x_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(lean_object* v_x_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v_x_520_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___boxed(lean_object* v_x_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity(v_x_525_, v_a_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
return v_res_529_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(lean_object* v_x_530_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = 0;
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0___boxed(lean_object* v_x_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__0(v_x_532_);
lean_dec_ref(v_x_532_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(lean_object* v_snd_535_, lean_object* v___y_536_){
_start:
{
if (lean_obj_tag(v_snd_535_) == 0)
{
uint8_t v___x_537_; 
lean_dec_ref(v___y_536_);
v___x_537_ = 0;
return v___x_537_;
}
else
{
lean_object* v_val_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_val_538_ = lean_ctor_get(v_snd_535_, 0);
lean_inc(v_val_538_);
lean_dec_ref_known(v_snd_535_, 1);
v___x_539_ = lean_apply_1(v_val_538_, v___y_536_);
v___x_540_ = lean_unbox(v___x_539_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed(lean_object* v_snd_541_, lean_object* v___y_542_){
_start:
{
uint8_t v_res_543_; lean_object* v_r_544_; 
v_res_543_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1(v_snd_541_, v___y_542_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(lean_object* v_a_545_, lean_object* v_snd_546_, uint8_t v_a_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_549_; uint8_t v___x_550_; 
lean_inc_ref(v___y_548_);
v___x_549_ = lean_apply_1(v_a_545_, v___y_548_);
v___x_550_ = lean_unbox(v___x_549_);
if (v___x_550_ == 0)
{
if (lean_obj_tag(v_snd_546_) == 0)
{
uint8_t v___x_551_; 
lean_dec_ref(v___y_548_);
v___x_551_ = 2;
return v___x_551_;
}
else
{
lean_object* v_val_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_val_552_ = lean_ctor_get(v_snd_546_, 0);
lean_inc(v_val_552_);
lean_dec_ref_known(v_snd_546_, 1);
v___x_553_ = lean_apply_1(v_val_552_, v___y_548_);
v___x_554_ = lean_unbox(v___x_553_);
return v___x_554_;
}
}
else
{
lean_dec_ref(v___y_548_);
lean_dec(v_snd_546_);
return v_a_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed(lean_object* v_a_555_, lean_object* v_snd_556_, lean_object* v_a_557_, lean_object* v___y_558_){
_start:
{
uint8_t v_a_6388__boxed_559_; uint8_t v_res_560_; lean_object* v_r_561_; 
v_a_6388__boxed_559_ = lean_unbox(v_a_557_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0(v_a_555_, v_snd_556_, v_a_6388__boxed_559_, v___y_558_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(lean_object* v_as_622_, size_t v_sz_623_, size_t v_i_624_, lean_object* v_b_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_a_630_; uint8_t v___x_634_; 
v___x_634_ = lean_usize_dec_lt(v_i_624_, v_sz_623_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v_b_625_);
return v___x_635_;
}
else
{
lean_object* v_snd_636_; lean_object* v_snd_637_; lean_object* v_snd_638_; lean_object* v_fst_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_946_; 
v_snd_636_ = lean_ctor_get(v_b_625_, 1);
lean_inc(v_snd_636_);
v_snd_637_ = lean_ctor_get(v_snd_636_, 1);
lean_inc(v_snd_637_);
v_snd_638_ = lean_ctor_get(v_snd_637_, 1);
lean_inc(v_snd_638_);
v_fst_639_ = lean_ctor_get(v_b_625_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v_b_625_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v_b_625_, 1);
lean_dec(v_unused_947_);
v___x_641_ = v_b_625_;
v_isShared_642_ = v_isSharedCheck_946_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_fst_639_);
lean_dec(v_b_625_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_946_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_fst_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_944_; 
v_fst_643_ = lean_ctor_get(v_snd_636_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v_snd_636_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v_snd_636_, 1);
lean_dec(v_unused_945_);
v___x_645_ = v_snd_636_;
v_isShared_646_ = v_isSharedCheck_944_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_fst_643_);
lean_dec(v_snd_636_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_944_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_fst_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_942_; 
v_fst_647_ = lean_ctor_get(v_snd_637_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v_snd_637_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v_snd_637_, 1);
lean_dec(v_unused_943_);
v___x_649_ = v_snd_637_;
v_isShared_650_ = v_isSharedCheck_942_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_fst_647_);
lean_dec(v_snd_637_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_942_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_fst_651_; lean_object* v_snd_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_941_; 
v_fst_651_ = lean_ctor_get(v_snd_638_, 0);
v_snd_652_ = lean_ctor_get(v_snd_638_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_snd_638_);
if (v_isSharedCheck_941_ == 0)
{
v___x_654_ = v_snd_638_;
v_isShared_655_ = v_isSharedCheck_941_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_snd_652_);
lean_inc(v_fst_651_);
lean_dec(v_snd_638_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_941_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_a_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_a_656_ = lean_array_uget_borrowed(v_as_622_, v_i_624_);
v___x_657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_a_656_);
v___x_658_ = l_Lean_Syntax_isOfKind(v_a_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v___x_661_; 
lean_dec_ref_known(v___x_659_, 1);
if (v_isShared_655_ == 0)
{
v___x_661_ = v___x_654_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_fst_651_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_snd_652_);
v___x_661_ = v_reuseFailAlloc_671_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_661_);
v___x_663_ = v___x_649_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_fst_647_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_661_);
v___x_663_ = v_reuseFailAlloc_670_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_663_);
v___x_665_ = v___x_645_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fst_643_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_663_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_667_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v___x_665_);
v___x_667_ = v___x_641_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_fst_639_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
v_a_630_ = v___x_667_;
goto v___jp_629_;
}
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_del_object(v___x_654_);
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_del_object(v___x_649_);
lean_dec(v_fst_647_);
lean_del_object(v___x_645_);
lean_dec(v_fst_643_);
lean_del_object(v___x_641_);
lean_dec(v_fst_639_);
v_a_672_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_659_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_659_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_action_x3f_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = l_Lean_Syntax_getArg(v_a_656_, v___x_680_);
v___x_722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__3));
lean_inc(v___x_681_);
v___x_723_ = l_Lean_Syntax_isOfKind(v___x_681_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint8_t v___x_725_; 
lean_del_object(v___x_654_);
lean_del_object(v___x_649_);
lean_del_object(v___x_645_);
lean_del_object(v___x_641_);
v___x_724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__5));
lean_inc(v___x_681_);
v___x_725_ = l_Lean_Syntax_isOfKind(v___x_681_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; uint8_t v_reportPositions_727_; 
v___x_726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__7));
lean_inc(v___x_681_);
v_reportPositions_727_ = l_Lean_Syntax_isOfKind(v___x_681_, v___x_726_);
if (v_reportPositions_727_ == 0)
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__9));
lean_inc(v___x_681_);
v___x_729_ = l_Lean_Syntax_isOfKind(v___x_681_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__11));
lean_inc(v___x_681_);
v___x_731_ = l_Lean_Syntax_isOfKind(v___x_681_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_dec(v___x_681_);
v___x_732_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec_ref_known(v___x_732_, 1);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_fst_651_);
lean_ctor_set(v___x_733_, 1, v_snd_652_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v_fst_647_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v_fst_643_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_fst_639_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v_a_630_ = v___x_736_;
goto v___jp_629_;
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_dec(v_fst_647_);
lean_dec(v_fst_643_);
lean_dec(v_fst_639_);
v_a_737_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_732_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_732_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_745_ = lean_unsigned_to_nat(2u);
v___x_746_ = l_Lean_Syntax_getArg(v___x_681_, v___x_745_);
lean_dec(v___x_681_);
v___x_747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_746_);
v___x_748_ = l_Lean_Syntax_isOfKind(v___x_746_, v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_750_ = l_Lean_Syntax_isOfKind(v___x_746_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec_ref_known(v___x_751_, 1);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_fst_651_);
lean_ctor_set(v___x_752_, 1, v_snd_652_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_fst_647_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_fst_643_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_fst_639_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v_a_630_ = v___x_755_;
goto v___jp_629_;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_dec(v_fst_647_);
lean_dec(v_fst_643_);
lean_dec(v_fst_639_);
v_a_756_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_751_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_751_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v_fst_651_);
v___x_764_ = lean_box(v_reportPositions_727_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v_snd_652_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_fst_647_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_fst_643_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v_fst_639_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v_a_630_ = v___x_768_;
goto v___jp_629_;
}
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec(v___x_746_);
lean_dec(v_fst_651_);
v___x_769_ = lean_box(v___x_658_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v_snd_652_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_fst_647_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_fst_643_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_fst_639_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v_a_630_ = v___x_773_;
goto v___jp_629_;
}
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_774_ = lean_unsigned_to_nat(2u);
v___x_775_ = l_Lean_Syntax_getArg(v___x_681_, v___x_774_);
lean_dec(v___x_681_);
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__17));
lean_inc(v___x_775_);
v___x_777_ = l_Lean_Syntax_isOfKind(v___x_775_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
lean_dec(v___x_775_);
v___x_778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref_known(v___x_778_, 1);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_fst_651_);
lean_ctor_set(v___x_779_, 1, v_snd_652_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_fst_647_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_fst_643_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_fst_639_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v_a_630_ = v___x_782_;
goto v___jp_629_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_dec(v_fst_647_);
lean_dec(v_fst_643_);
lean_dec(v_fst_639_);
v_a_783_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_778_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_778_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_791_ = l_Lean_Syntax_getArg(v___x_775_, v___x_680_);
lean_dec(v___x_775_);
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__13));
lean_inc(v___x_791_);
v___x_793_ = l_Lean_Syntax_isOfKind(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__15));
v___x_795_ = l_Lean_Syntax_isOfKind(v___x_791_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref_known(v___x_796_, 1);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_fst_651_);
lean_ctor_set(v___x_797_, 1, v_snd_652_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v_fst_647_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_fst_643_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_fst_639_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v_a_630_ = v___x_800_;
goto v___jp_629_;
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_dec(v_fst_647_);
lean_dec(v_fst_643_);
lean_dec(v_fst_639_);
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
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec(v_fst_647_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v_fst_651_);
lean_ctor_set(v___x_809_, 1, v_snd_652_);
v___x_810_ = lean_box(v_reportPositions_727_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v_fst_643_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v_fst_639_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v_a_630_ = v___x_813_;
goto v___jp_629_;
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec(v___x_791_);
lean_dec(v_fst_647_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_fst_651_);
lean_ctor_set(v___x_814_, 1, v_snd_652_);
v___x_815_ = lean_box(v___x_658_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___x_814_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_fst_643_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_fst_639_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v_a_630_ = v___x_818_;
goto v___jp_629_;
}
}
}
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_819_ = lean_unsigned_to_nat(2u);
v___x_820_ = l_Lean_Syntax_getArg(v___x_681_, v___x_819_);
lean_dec(v___x_681_);
v___x_821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__19));
lean_inc(v___x_820_);
v___x_822_ = l_Lean_Syntax_isOfKind(v___x_820_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; 
lean_dec(v___x_820_);
v___x_823_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
lean_dec_ref_known(v___x_823_, 1);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_fst_651_);
lean_ctor_set(v___x_824_, 1, v_snd_652_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_fst_647_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v_fst_643_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v_fst_639_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v_a_630_ = v___x_827_;
goto v___jp_629_;
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_dec(v_fst_647_);
lean_dec(v_fst_643_);
lean_dec(v_fst_639_);
v_a_828_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_823_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_823_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_836_ = l_Lean_Syntax_getArg(v___x_820_, v___x_680_);
lean_dec(v___x_820_);
v___x_837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_836_);
v___x_838_ = l_Lean_Syntax_isOfKind(v___x_836_, v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__23));
v___x_840_ = l_Lean_Syntax_isOfKind(v___x_836_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref_known(v___x_841_, 1);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v_fst_651_);
lean_ctor_set(v___x_842_, 1, v_snd_652_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_fst_647_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_fst_643_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_fst_639_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v_a_630_ = v___x_845_;
goto v___jp_629_;
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_dec(v_fst_647_);
lean_dec(v_fst_643_);
lean_dec(v_fst_639_);
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
uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v_fst_643_);
v___x_854_ = 1;
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v_fst_651_);
lean_ctor_set(v___x_855_, 1, v_snd_652_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_fst_647_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = lean_box(v___x_854_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_fst_639_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v_a_630_ = v___x_859_;
goto v___jp_629_;
}
}
else
{
uint8_t v_ordering_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec(v___x_836_);
lean_dec(v_fst_643_);
v_ordering_860_ = 0;
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_fst_651_);
lean_ctor_set(v___x_861_, 1, v_snd_652_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_fst_647_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_box(v_ordering_860_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_862_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v_fst_639_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v_a_630_ = v___x_865_;
goto v___jp_629_;
}
}
}
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_866_ = lean_unsigned_to_nat(2u);
v___x_867_ = l_Lean_Syntax_getArg(v___x_681_, v___x_866_);
lean_dec(v___x_681_);
v___x_868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__25));
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
lean_ctor_set(v___x_871_, 0, v_fst_651_);
lean_ctor_set(v___x_871_, 1, v_snd_652_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_fst_647_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_fst_643_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_fst_639_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v_a_630_ = v___x_874_;
goto v___jp_629_;
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_dec(v_fst_647_);
lean_dec(v_fst_643_);
lean_dec(v_fst_639_);
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
v___x_883_ = l_Lean_Syntax_getArg(v___x_867_, v___x_680_);
lean_dec(v___x_867_);
v___x_884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__21));
lean_inc(v___x_883_);
v___x_885_ = l_Lean_Syntax_isOfKind(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__27));
lean_inc(v___x_883_);
v___x_887_ = l_Lean_Syntax_isOfKind(v___x_883_, v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__29));
v___x_889_ = l_Lean_Syntax_isOfKind(v___x_883_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec_ref_known(v___x_890_, 1);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_fst_651_);
lean_ctor_set(v___x_891_, 1, v_snd_652_);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v_fst_647_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_fst_643_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v_fst_639_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v_a_630_ = v___x_894_;
goto v___jp_629_;
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_dec(v_fst_647_);
lean_dec(v_fst_643_);
lean_dec(v_fst_639_);
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
uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec(v_fst_639_);
v___x_903_ = 2;
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v_fst_651_);
lean_ctor_set(v___x_904_, 1, v_snd_652_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v_fst_647_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v_fst_643_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_box(v___x_903_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_906_);
v_a_630_ = v___x_908_;
goto v___jp_629_;
}
}
else
{
uint8_t v_whitespace_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v___x_883_);
lean_dec(v_fst_639_);
v_whitespace_909_ = 1;
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_fst_651_);
lean_ctor_set(v___x_910_, 1, v_snd_652_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_fst_647_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_fst_643_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_box(v_whitespace_909_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_912_);
v_a_630_ = v___x_914_;
goto v___jp_629_;
}
}
else
{
uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v___x_883_);
lean_dec(v_fst_639_);
v___x_915_ = 0;
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_fst_651_);
lean_ctor_set(v___x_916_, 1, v_snd_652_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_fst_647_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v_fst_643_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_box(v___x_915_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___x_918_);
v_a_630_ = v___x_920_;
goto v___jp_629_;
}
}
}
}
else
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = l_Lean_Syntax_getArg(v___x_681_, v___x_680_);
v___x_922_ = l_Lean_Syntax_isNone(v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_921_);
v___x_924_ = l_Lean_Syntax_matchesNull(v___x_921_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; 
lean_dec(v___x_921_);
lean_dec(v___x_681_);
lean_del_object(v___x_654_);
lean_del_object(v___x_649_);
lean_del_object(v___x_645_);
lean_del_object(v___x_641_);
v___x_925_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec_ref_known(v___x_925_, 1);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_fst_651_);
lean_ctor_set(v___x_926_, 1, v_snd_652_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_fst_647_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_fst_643_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_fst_639_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v_a_630_ = v___x_929_;
goto v___jp_629_;
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_dec(v_fst_647_);
lean_dec(v_fst_643_);
lean_dec(v_fst_639_);
v_a_930_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_925_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_925_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = l_Lean_Syntax_getArg(v___x_921_, v___x_680_);
lean_dec(v___x_921_);
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
v_action_x3f_683_ = v___x_939_;
v___y_684_ = v___y_626_;
v___y_685_ = v___y_627_;
goto v___jp_682_;
}
}
else
{
lean_object* v___x_940_; 
lean_dec(v___x_921_);
v___x_940_ = lean_box(0);
v_action_x3f_683_ = v___x_940_;
v___y_684_ = v___y_626_;
v___y_685_ = v___y_627_;
goto v___jp_682_;
}
}
v___jp_682_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = l_Lean_Syntax_getArg(v___x_681_, v___x_686_);
lean_dec(v___x_681_);
v___x_688_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction(v_action_x3f_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg(v___x_687_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___f_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___f_692_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_692_, 0, v_a_691_);
lean_closure_set(v___f_692_, 1, v_snd_652_);
lean_closure_set(v___f_692_, 2, v_a_689_);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v___f_692_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_693_);
v___x_695_ = v___x_654_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_fst_651_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_705_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_695_);
v___x_697_ = v___x_649_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_fst_647_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_695_);
v___x_697_ = v_reuseFailAlloc_704_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_697_);
v___x_699_ = v___x_645_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_fst_643_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v___x_699_);
v___x_701_ = v___x_641_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_fst_639_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v_a_630_ = v___x_701_;
goto v___jp_629_;
}
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec(v_a_689_);
lean_del_object(v___x_654_);
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_del_object(v___x_649_);
lean_dec(v_fst_647_);
lean_del_object(v___x_645_);
lean_dec(v_fst_643_);
lean_del_object(v___x_641_);
lean_dec(v_fst_639_);
v_a_706_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_690_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_690_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v___x_687_);
lean_del_object(v___x_654_);
lean_dec(v_snd_652_);
lean_dec(v_fst_651_);
lean_del_object(v___x_649_);
lean_dec(v_fst_647_);
lean_del_object(v___x_645_);
lean_dec(v_fst_643_);
lean_del_object(v___x_641_);
lean_dec(v_fst_639_);
v_a_714_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_688_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_688_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
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
v___jp_629_:
{
size_t v___x_631_; size_t v___x_632_; 
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_add(v_i_624_, v___x_631_);
v_i_624_ = v___x_632_;
v_b_625_ = v_a_630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___boxed(lean_object* v_as_948_, lean_object* v_sz_949_, lean_object* v_i_950_, lean_object* v_b_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
size_t v_sz_boxed_955_; size_t v_i_boxed_956_; lean_object* v_res_957_; 
v_sz_boxed_955_ = lean_unbox_usize(v_sz_949_);
lean_dec(v_sz_949_);
v_i_boxed_956_ = lean_unbox_usize(v_i_950_);
lean_dec(v_i_950_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v_as_948_, v_sz_boxed_955_, v_i_boxed_956_, v_b_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v_as_948_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(size_t v_sz_958_, size_t v_i_959_, lean_object* v_bs_960_){
_start:
{
uint8_t v___x_961_; 
v___x_961_ = lean_usize_dec_lt(v_i_959_, v_sz_958_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_962_, 0, v_bs_960_);
return v___x_962_;
}
else
{
lean_object* v_v_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v_v_963_ = lean_array_uget(v_bs_960_, v_i_959_);
v___x_964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0___closed__1));
lean_inc(v_v_963_);
v___x_965_ = l_Lean_Syntax_isOfKind(v_v_963_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
lean_dec(v_v_963_);
lean_dec_ref(v_bs_960_);
v___x_966_ = lean_box(0);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v_bs_x27_968_; size_t v___x_969_; size_t v___x_970_; lean_object* v___x_971_; 
v___x_967_ = lean_unsigned_to_nat(0u);
v_bs_x27_968_ = lean_array_uset(v_bs_960_, v_i_959_, v___x_967_);
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_add(v_i_959_, v___x_969_);
v___x_971_ = lean_array_uset(v_bs_x27_968_, v_i_959_, v_v_963_);
v_i_959_ = v___x_970_;
v_bs_960_ = v___x_971_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1___boxed(lean_object* v_sz_973_, lean_object* v_i_974_, lean_object* v_bs_975_){
_start:
{
size_t v_sz_boxed_976_; size_t v_i_boxed_977_; lean_object* v_res_978_; 
v_sz_boxed_976_ = lean_unbox_usize(v_sz_973_);
lean_dec(v_sz_973_);
v_i_boxed_977_ = lean_unbox_usize(v_i_974_);
lean_dec(v_i_974_);
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_boxed_976_, v_i_boxed_977_, v_bs_975_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(uint8_t v___x_979_, lean_object* v_as_980_, size_t v_i_981_, size_t v_stop_982_, lean_object* v_b_983_){
_start:
{
lean_object* v___y_985_; uint8_t v___x_989_; 
v___x_989_ = lean_usize_dec_eq(v_i_981_, v_stop_982_);
if (v___x_989_ == 0)
{
lean_object* v_fst_990_; uint8_t v___x_991_; 
v_fst_990_ = lean_ctor_get(v_b_983_, 0);
v___x_991_ = lean_unbox(v_fst_990_);
if (v___x_991_ == 0)
{
lean_object* v_snd_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1000_; 
v_snd_992_ = lean_ctor_get(v_b_983_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_b_983_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v_b_983_, 0);
lean_dec(v_unused_1001_);
v___x_994_ = v_b_983_;
v_isShared_995_ = v_isSharedCheck_1000_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_snd_992_);
lean_dec(v_b_983_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1000_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_996_ = lean_box(v___x_979_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_996_);
v___x_998_ = v___x_994_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_snd_992_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
v___y_985_ = v___x_998_;
goto v___jp_984_;
}
}
}
else
{
lean_object* v_snd_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1012_; 
v_snd_1002_ = lean_ctor_get(v_b_983_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_b_983_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_b_983_, 0);
lean_dec(v_unused_1013_);
v___x_1004_ = v_b_983_;
v_isShared_1005_ = v_isSharedCheck_1012_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_snd_1002_);
lean_dec(v_b_983_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1012_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1006_ = lean_array_uget_borrowed(v_as_980_, v_i_981_);
lean_inc(v___x_1006_);
v___x_1007_ = lean_array_push(v_snd_1002_, v___x_1006_);
v___x_1008_ = lean_box(v___x_989_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v___x_1007_);
lean_ctor_set(v___x_1004_, 0, v___x_1008_);
v___x_1010_ = v___x_1004_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v___x_1007_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
v___y_985_ = v___x_1010_;
goto v___jp_984_;
}
}
}
}
else
{
return v_b_983_;
}
v___jp_984_:
{
size_t v___x_986_; size_t v___x_987_; 
v___x_986_ = ((size_t)1ULL);
v___x_987_ = lean_usize_add(v_i_981_, v___x_986_);
v_i_981_ = v___x_987_;
v_b_983_ = v___y_985_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2___boxed(lean_object* v___x_1014_, lean_object* v_as_1015_, lean_object* v_i_1016_, lean_object* v_stop_1017_, lean_object* v_b_1018_){
_start:
{
uint8_t v___x_7263__boxed_1019_; size_t v_i_boxed_1020_; size_t v_stop_boxed_1021_; lean_object* v_res_1022_; 
v___x_7263__boxed_1019_ = lean_unbox(v___x_1014_);
v_i_boxed_1020_ = lean_unbox_usize(v_i_1016_);
lean_dec(v_i_1016_);
v_stop_boxed_1021_ = lean_unbox_usize(v_stop_1017_);
lean_dec(v_stop_1017_);
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_7263__boxed_1019_, v_as_1015_, v_i_boxed_1020_, v_stop_boxed_1021_, v_b_1018_);
lean_dec_ref(v_as_1015_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(lean_object* v_spec_x3f_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_elts_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1095_; lean_object* v_cfg_1109_; 
v_cfg_1109_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__5));
if (lean_obj_tag(v_spec_x3f_1051_) == 1)
{
lean_object* v_val_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v_val_1110_ = lean_ctor_get(v_spec_x3f_1051_, 0);
lean_inc_n(v_val_1110_, 2);
lean_dec_ref_known(v_spec_x3f_1051_, 1);
v___x_1111_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__7));
v___x_1112_ = l_Lean_Syntax_isOfKind(v_val_1110_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v_val_1110_);
v___x_1113_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = l_Lean_Syntax_getArg(v_val_1110_, v___x_1122_);
lean_dec(v_val_1110_);
v___x_1124_ = l_Lean_Syntax_getArgs(v___x_1123_);
lean_dec(v___x_1123_);
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__8));
v___x_1127_ = lean_array_get_size(v___x_1124_);
v___x_1128_ = lean_nat_dec_lt(v___x_1125_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_dec_ref(v___x_1124_);
v___y_1095_ = v___x_1126_;
goto v___jp_1094_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; lean_object* v___x_1133_; lean_object* v_snd_1134_; 
v___x_1129_ = lean_box(v___x_1128_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
lean_ctor_set(v___x_1130_, 1, v___x_1126_);
v___x_1131_ = ((size_t)0ULL);
v___x_1132_ = lean_usize_of_nat(v___x_1127_);
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__2(v___x_1112_, v___x_1124_, v___x_1131_, v___x_1132_, v___x_1130_);
lean_dec_ref(v___x_1124_);
v_snd_1134_ = lean_ctor_get(v___x_1133_, 1);
lean_inc(v_snd_1134_);
lean_dec_ref(v___x_1133_);
v___y_1095_ = v_snd_1134_;
goto v___jp_1094_;
}
}
}
else
{
lean_object* v___x_1135_; 
lean_dec(v_spec_x3f_1051_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_cfg_1109_);
return v___x_1135_;
}
v___jp_1055_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; size_t v_sz_1061_; size_t v___x_1062_; lean_object* v___x_1063_; 
v___x_1059_ = l_Array_reverse___redArg(v_elts_1056_);
v___x_1060_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___closed__4));
v_sz_1061_ = lean_array_size(v___x_1059_);
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__0(v___x_1059_, v_sz_1061_, v___x_1062_, v___x_1060_, v___y_1057_, v___y_1058_);
lean_dec_ref(v___x_1059_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1085_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1085_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1085_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_snd_1068_; lean_object* v_snd_1069_; lean_object* v_snd_1070_; lean_object* v_fst_1071_; lean_object* v_fst_1072_; lean_object* v_fst_1073_; lean_object* v_fst_1074_; lean_object* v_snd_1075_; lean_object* v___y_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; uint8_t v___x_1079_; uint8_t v___x_1080_; uint8_t v___x_1081_; lean_object* v___x_1083_; 
v_snd_1068_ = lean_ctor_get(v_a_1064_, 1);
lean_inc(v_snd_1068_);
v_snd_1069_ = lean_ctor_get(v_snd_1068_, 1);
lean_inc(v_snd_1069_);
v_snd_1070_ = lean_ctor_get(v_snd_1069_, 1);
lean_inc(v_snd_1070_);
v_fst_1071_ = lean_ctor_get(v_a_1064_, 0);
lean_inc(v_fst_1071_);
lean_dec(v_a_1064_);
v_fst_1072_ = lean_ctor_get(v_snd_1068_, 0);
lean_inc(v_fst_1072_);
lean_dec(v_snd_1068_);
v_fst_1073_ = lean_ctor_get(v_snd_1069_, 0);
lean_inc(v_fst_1073_);
lean_dec(v_snd_1069_);
v_fst_1074_ = lean_ctor_get(v_snd_1070_, 0);
lean_inc(v_fst_1074_);
v_snd_1075_ = lean_ctor_get(v_snd_1070_, 1);
lean_inc(v_snd_1075_);
lean_dec(v_snd_1070_);
v___y_1076_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___y_1076_, 0, v_snd_1075_);
v___x_1077_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1077_, 0, v___y_1076_);
v___x_1078_ = lean_unbox(v_fst_1071_);
lean_dec(v_fst_1071_);
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*1, v___x_1078_);
v___x_1079_ = lean_unbox(v_fst_1072_);
lean_dec(v_fst_1072_);
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*1 + 1, v___x_1079_);
v___x_1080_ = lean_unbox(v_fst_1073_);
lean_dec(v_fst_1073_);
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*1 + 2, v___x_1080_);
v___x_1081_ = lean_unbox(v_fst_1074_);
lean_dec(v_fst_1074_);
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*1 + 3, v___x_1081_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1077_);
v___x_1083_ = v___x_1066_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1077_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_a_1086_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1063_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1063_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
v___jp_1094_:
{
size_t v_sz_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
v_sz_1096_ = lean_array_size(v___y_1095_);
v___x_1097_ = ((size_t)0ULL);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec_spec__1(v_sz_1096_, v___x_1097_, v___y_1095_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v___x_1099_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
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
lean_object* v_val_1108_; 
v_val_1108_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_val_1108_);
lean_dec_ref_known(v___x_1098_, 1);
v_elts_1056_ = v_val_1108_;
v___y_1057_ = v_a_1052_;
v___y_1058_ = v_a_1053_;
goto v___jp_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec___boxed(lean_object* v_spec_x3f_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v_spec_x3f_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(lean_object* v_s_1153_, lean_object* v_replacement_1154_, lean_object* v_a_1155_, lean_object* v_b_1156_){
_start:
{
lean_object* v_it_1158_; lean_object* v_startPos_1159_; lean_object* v_endPos_1160_; lean_object* v_it_1169_; 
switch(lean_obj_tag(v_a_1155_))
{
case 0:
{
lean_object* v_pos_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1187_; 
v_pos_1175_ = lean_ctor_get(v_a_1155_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_a_1155_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1177_ = v_a_1155_;
v_isShared_1178_ = v_isSharedCheck_1187_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_pos_1175_);
lean_dec(v_a_1155_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1187_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_startInclusive_1179_; lean_object* v_endExclusive_1180_; lean_object* v___x_1181_; uint8_t v_decide_1182_; 
v_startInclusive_1179_ = lean_ctor_get(v_s_1153_, 1);
v_endExclusive_1180_ = lean_ctor_get(v_s_1153_, 2);
v___x_1181_ = lean_nat_sub(v_endExclusive_1180_, v_startInclusive_1179_);
v_decide_1182_ = lean_nat_dec_eq(v_pos_1175_, v___x_1181_);
lean_dec(v___x_1181_);
if (v_decide_1182_ == 0)
{
lean_object* v___x_1184_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 1);
v___x_1184_ = v___x_1177_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_pos_1175_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
v_it_1169_ = v___x_1184_;
goto v___jp_1168_;
}
}
else
{
lean_object* v___x_1186_; 
lean_del_object(v___x_1177_);
lean_dec(v_pos_1175_);
v___x_1186_ = lean_box(3);
v_it_1169_ = v___x_1186_;
goto v___jp_1168_;
}
}
}
case 1:
{
lean_object* v_pos_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1200_; 
v_pos_1188_ = lean_ctor_get(v_a_1155_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_a_1155_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1190_ = v_a_1155_;
v_isShared_1191_ = v_isSharedCheck_1200_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_pos_1188_);
lean_dec(v_a_1155_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1200_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_str_1192_; lean_object* v_startInclusive_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v_str_1192_ = lean_ctor_get(v_s_1153_, 0);
v_startInclusive_1193_ = lean_ctor_get(v_s_1153_, 1);
v___x_1194_ = lean_nat_add(v_startInclusive_1193_, v_pos_1188_);
v___x_1195_ = lean_string_utf8_next_fast(v_str_1192_, v___x_1194_);
lean_dec(v___x_1194_);
v___x_1196_ = lean_nat_sub(v___x_1195_, v_startInclusive_1193_);
lean_inc(v___x_1196_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set_tag(v___x_1190_, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1196_);
v___x_1198_ = v___x_1190_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
v_it_1158_ = v___x_1198_;
v_startPos_1159_ = v_pos_1188_;
v_endPos_1160_ = v___x_1196_;
goto v___jp_1157_;
}
}
}
case 2:
{
lean_object* v_needle_1201_; lean_object* v_table_1202_; lean_object* v_stackPos_1203_; lean_object* v_needlePos_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1265_; 
v_needle_1201_ = lean_ctor_get(v_a_1155_, 0);
v_table_1202_ = lean_ctor_get(v_a_1155_, 1);
v_stackPos_1203_ = lean_ctor_get(v_a_1155_, 2);
v_needlePos_1204_ = lean_ctor_get(v_a_1155_, 3);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_a_1155_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1206_ = v_a_1155_;
v_isShared_1207_ = v_isSharedCheck_1265_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_needlePos_1204_);
lean_inc(v_stackPos_1203_);
lean_inc(v_table_1202_);
lean_inc(v_needle_1201_);
lean_dec(v_a_1155_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1265_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_str_1208_; lean_object* v_startInclusive_1209_; lean_object* v_endExclusive_1210_; lean_object* v_str_1211_; lean_object* v_startInclusive_1212_; lean_object* v_endExclusive_1213_; lean_object* v_basePos_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v_str_1208_ = lean_ctor_get(v_needle_1201_, 0);
v_startInclusive_1209_ = lean_ctor_get(v_needle_1201_, 1);
v_endExclusive_1210_ = lean_ctor_get(v_needle_1201_, 2);
v_str_1211_ = lean_ctor_get(v_s_1153_, 0);
v_startInclusive_1212_ = lean_ctor_get(v_s_1153_, 1);
v_endExclusive_1213_ = lean_ctor_get(v_s_1153_, 2);
v_basePos_1214_ = lean_nat_sub(v_stackPos_1203_, v_needlePos_1204_);
v___x_1215_ = lean_nat_sub(v_endExclusive_1210_, v_startInclusive_1209_);
v___x_1216_ = lean_nat_add(v_basePos_1214_, v___x_1215_);
v___x_1217_ = lean_nat_sub(v_endExclusive_1213_, v_startInclusive_1212_);
v___x_1218_ = lean_nat_dec_le(v___x_1216_, v___x_1217_);
lean_dec(v___x_1216_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
lean_dec(v___x_1215_);
lean_del_object(v___x_1206_);
lean_dec(v_needlePos_1204_);
lean_dec(v_stackPos_1203_);
lean_dec_ref(v_table_1202_);
lean_dec_ref(v_needle_1201_);
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = lean_nat_add(v_basePos_1214_, v___x_1219_);
v___x_1221_ = lean_nat_dec_le(v___x_1220_, v___x_1217_);
lean_dec(v___x_1220_);
if (v___x_1221_ == 0)
{
lean_dec(v___x_1217_);
lean_dec(v_basePos_1214_);
lean_dec_ref(v_s_1153_);
return v_b_1156_;
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = l_String_Slice_pos_x21(v_s_1153_, v_basePos_1214_);
lean_dec(v_basePos_1214_);
v___x_1223_ = lean_box(3);
v_it_1158_ = v___x_1223_;
v_startPos_1159_ = v___x_1222_;
v_endPos_1160_ = v___x_1217_;
goto v___jp_1157_;
}
}
else
{
lean_object* v___x_1224_; uint8_t v_stackByte_1225_; lean_object* v___x_1226_; uint8_t v_patByte_1227_; uint8_t v___x_1228_; 
lean_dec(v___x_1217_);
v___x_1224_ = lean_nat_add(v_startInclusive_1212_, v_stackPos_1203_);
v_stackByte_1225_ = lean_string_get_byte_fast(v_str_1211_, v___x_1224_);
v___x_1226_ = lean_nat_add(v_startInclusive_1209_, v_needlePos_1204_);
v_patByte_1227_ = lean_string_get_byte_fast(v_str_1208_, v___x_1226_);
v___x_1228_ = lean_uint8_dec_eq(v_stackByte_1225_, v_patByte_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; uint8_t v_decide_1230_; 
lean_dec(v___x_1215_);
v___x_1229_ = lean_unsigned_to_nat(0u);
v_decide_1230_ = lean_nat_dec_eq(v_needlePos_1204_, v___x_1229_);
if (v_decide_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_newNeedlePos_1233_; uint8_t v___x_1234_; 
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = lean_nat_sub(v_needlePos_1204_, v___x_1231_);
lean_dec(v_needlePos_1204_);
v_newNeedlePos_1233_ = lean_array_fget_borrowed(v_table_1202_, v___x_1232_);
lean_dec(v___x_1232_);
v___x_1234_ = lean_nat_dec_eq(v_newNeedlePos_1233_, v___x_1229_);
if (v___x_1234_ == 0)
{
lean_object* v_oldBasePos_1235_; lean_object* v___x_1236_; lean_object* v_newBasePos_1237_; lean_object* v___x_1239_; 
lean_inc(v_newNeedlePos_1233_);
v_oldBasePos_1235_ = l_String_Slice_pos_x21(v_s_1153_, v_basePos_1214_);
lean_dec(v_basePos_1214_);
v___x_1236_ = lean_nat_sub(v_stackPos_1203_, v_newNeedlePos_1233_);
v_newBasePos_1237_ = l_String_Slice_pos_x21(v_s_1153_, v___x_1236_);
lean_dec(v___x_1236_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 3, v_newNeedlePos_1233_);
v___x_1239_ = v___x_1206_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_needle_1201_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_table_1202_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_stackPos_1203_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_newNeedlePos_1233_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
v_it_1158_ = v___x_1239_;
v_startPos_1159_ = v_oldBasePos_1235_;
v_endPos_1160_ = v_newBasePos_1237_;
goto v___jp_1157_;
}
}
else
{
lean_object* v_basePos_1241_; lean_object* v_nextStackPos_1242_; lean_object* v___x_1244_; 
v_basePos_1241_ = l_String_Slice_pos_x21(v_s_1153_, v_basePos_1214_);
lean_dec(v_basePos_1214_);
v_nextStackPos_1242_ = l_String_Slice_posGE___redArg(v_s_1153_, v_stackPos_1203_);
lean_inc(v_nextStackPos_1242_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 3, v___x_1229_);
lean_ctor_set(v___x_1206_, 2, v_nextStackPos_1242_);
v___x_1244_ = v___x_1206_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_needle_1201_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_table_1202_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_nextStackPos_1242_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v___x_1229_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
v_it_1158_ = v___x_1244_;
v_startPos_1159_ = v_basePos_1241_;
v_endPos_1160_ = v_nextStackPos_1242_;
goto v___jp_1157_;
}
}
}
else
{
lean_object* v_basePos_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_nextStackPos_1249_; lean_object* v___x_1251_; 
lean_dec(v_basePos_1214_);
lean_dec(v_needlePos_1204_);
v_basePos_1246_ = l_String_Slice_pos_x21(v_s_1153_, v_stackPos_1203_);
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_nat_add(v_stackPos_1203_, v___x_1247_);
lean_dec(v_stackPos_1203_);
v_nextStackPos_1249_ = l_String_Slice_posGE___redArg(v_s_1153_, v___x_1248_);
lean_inc(v_nextStackPos_1249_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 3, v___x_1229_);
lean_ctor_set(v___x_1206_, 2, v_nextStackPos_1249_);
v___x_1251_ = v___x_1206_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_needle_1201_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_table_1202_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_nextStackPos_1249_);
lean_ctor_set(v_reuseFailAlloc_1252_, 3, v___x_1229_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
v_it_1158_ = v___x_1251_;
v_startPos_1159_ = v_basePos_1246_;
v_endPos_1160_ = v_nextStackPos_1249_;
goto v___jp_1157_;
}
}
}
else
{
lean_object* v___x_1253_; lean_object* v_nextStackPos_1254_; lean_object* v_nextNeedlePos_1255_; uint8_t v_decide_1256_; 
lean_dec(v_basePos_1214_);
v___x_1253_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1254_ = lean_nat_add(v_stackPos_1203_, v___x_1253_);
lean_dec(v_stackPos_1203_);
v_nextNeedlePos_1255_ = lean_nat_add(v_needlePos_1204_, v___x_1253_);
lean_dec(v_needlePos_1204_);
v_decide_1256_ = lean_nat_dec_eq(v_nextNeedlePos_1255_, v___x_1215_);
lean_dec(v___x_1215_);
if (v_decide_1256_ == 0)
{
lean_object* v___x_1258_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 3, v_nextNeedlePos_1255_);
lean_ctor_set(v___x_1206_, 2, v_nextStackPos_1254_);
v___x_1258_ = v___x_1206_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_needle_1201_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_table_1202_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_nextStackPos_1254_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_nextNeedlePos_1255_);
v___x_1258_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
v_a_1155_ = v___x_1258_;
goto _start;
}
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
lean_dec(v_nextNeedlePos_1255_);
v___x_1261_ = lean_unsigned_to_nat(0u);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 3, v___x_1261_);
lean_ctor_set(v___x_1206_, 2, v_nextStackPos_1254_);
v___x_1263_ = v___x_1206_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_needle_1201_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_table_1202_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_nextStackPos_1254_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v_it_1169_ = v___x_1263_;
goto v___jp_1168_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1153_);
return v_b_1156_;
}
}
v___jp_1157_:
{
lean_object* v___x_1161_; lean_object* v_str_1162_; lean_object* v_startInclusive_1163_; lean_object* v_endExclusive_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_inc_ref(v_s_1153_);
v___x_1161_ = l_String_Slice_slice_x21(v_s_1153_, v_startPos_1159_, v_endPos_1160_);
lean_dec(v_endPos_1160_);
lean_dec(v_startPos_1159_);
v_str_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc_ref(v_str_1162_);
v_startInclusive_1163_ = lean_ctor_get(v___x_1161_, 1);
lean_inc(v_startInclusive_1163_);
v_endExclusive_1164_ = lean_ctor_get(v___x_1161_, 2);
lean_inc(v_endExclusive_1164_);
lean_dec_ref(v___x_1161_);
v___x_1165_ = lean_string_utf8_extract_fast(v_str_1162_, v_startInclusive_1163_, v_endExclusive_1164_);
lean_dec(v_endExclusive_1164_);
lean_dec(v_startInclusive_1163_);
lean_dec_ref(v_str_1162_);
v___x_1166_ = lean_string_append(v_b_1156_, v___x_1165_);
lean_dec_ref(v___x_1165_);
v_a_1155_ = v_it_1158_;
v_b_1156_ = v___x_1166_;
goto _start;
}
v___jp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_string_utf8_byte_size(v_replacement_1154_);
v___x_1172_ = lean_string_utf8_extract_fast(v_replacement_1154_, v___x_1170_, v___x_1171_);
v___x_1173_ = lean_string_append(v_b_1156_, v___x_1172_);
lean_dec_ref(v___x_1172_);
v_a_1155_ = v_it_1169_;
v_b_1156_ = v___x_1173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg___boxed(lean_object* v_s_1266_, lean_object* v_replacement_1267_, lean_object* v_a_1268_, lean_object* v_b_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1266_, v_replacement_1267_, v_a_1268_, v_b_1269_);
lean_dec_ref(v_replacement_1267_);
return v_res_1270_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1));
v___x_1277_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1276_);
return v___x_1277_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__2);
v___x_1280_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__1));
v___x_1281_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v___x_1279_);
lean_ctor_set(v___x_1281_, 2, v___x_1278_);
lean_ctor_set(v___x_1281_, 3, v___x_1278_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(lean_object* v_s_1282_, lean_object* v_replacement_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1285_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___closed__3);
v___x_1286_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1282_, v_replacement_1283_, v___x_1285_, v___x_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg___boxed(lean_object* v_s_1287_, lean_object* v_replacement_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1287_, v_replacement_1288_);
lean_dec_ref(v_replacement_1288_);
return v_res_1289_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1));
v___x_1296_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__2);
v___x_1299_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__1));
v___x_1300_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1298_);
lean_ctor_set(v___x_1300_, 2, v___x_1297_);
lean_ctor_set(v___x_1300_, 3, v___x_1297_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(lean_object* v_s_1301_, lean_object* v_replacement_1302_){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1304_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___closed__3);
v___x_1305_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1301_, v_replacement_1302_, v___x_1304_, v___x_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg___boxed(lean_object* v_s_1306_, lean_object* v_replacement_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1306_, v_replacement_1307_);
lean_dec_ref(v_replacement_1307_);
return v_res_1308_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1));
v___x_1315_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__2);
v___x_1318_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__1));
v___x_1319_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v___x_1317_);
lean_ctor_set(v___x_1319_, 2, v___x_1316_);
lean_ctor_set(v___x_1319_, 3, v___x_1316_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(lean_object* v_s_1320_, lean_object* v_replacement_1321_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1323_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___closed__3);
v___x_1324_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1320_, v_replacement_1321_, v___x_1323_, v___x_1322_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg___boxed(lean_object* v_s_1325_, lean_object* v_replacement_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1325_, v_replacement_1326_);
lean_dec_ref(v_replacement_1326_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(lean_object* v_s_1331_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1332_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__0));
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_string_utf8_byte_size(v_s_1331_);
v___x_1335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1335_, 0, v_s_1331_);
lean_ctor_set(v___x_1335_, 1, v___x_1333_);
lean_ctor_set(v___x_1335_, 2, v___x_1334_);
v___x_1336_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1335_, v___x_1332_);
v___x_1337_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__1));
v___x_1338_ = lean_string_utf8_byte_size(v___x_1336_);
v___x_1339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1336_);
lean_ctor_set(v___x_1339_, 1, v___x_1333_);
lean_ctor_set(v___x_1339_, 2, v___x_1338_);
v___x_1340_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v___x_1339_, v___x_1337_);
v___x_1341_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace___closed__2));
v___x_1342_ = lean_string_utf8_byte_size(v___x_1340_);
v___x_1343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1340_);
lean_ctor_set(v___x_1343_, 1, v___x_1333_);
lean_ctor_set(v___x_1343_, 2, v___x_1342_);
v___x_1344_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v___x_1343_, v___x_1341_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(lean_object* v_s_1345_, lean_object* v_pattern_1346_, lean_object* v_replacement_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v_s_1345_, v_replacement_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___boxed(lean_object* v_s_1349_, lean_object* v_pattern_1350_, lean_object* v_replacement_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0(v_s_1349_, v_pattern_1350_, v_replacement_1351_);
lean_dec_ref(v_replacement_1351_);
lean_dec_ref(v_pattern_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(lean_object* v_s_1353_, lean_object* v_pattern_1354_, lean_object* v_replacement_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___redArg(v_s_1353_, v_replacement_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1___boxed(lean_object* v_s_1357_, lean_object* v_pattern_1358_, lean_object* v_replacement_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__1(v_s_1357_, v_pattern_1358_, v_replacement_1359_);
lean_dec_ref(v_replacement_1359_);
lean_dec_ref(v_pattern_1358_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(lean_object* v_s_1361_, lean_object* v_pattern_1362_, lean_object* v_replacement_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___redArg(v_s_1361_, v_replacement_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2___boxed(lean_object* v_s_1365_, lean_object* v_pattern_1366_, lean_object* v_replacement_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__2(v_s_1365_, v_pattern_1366_, v_replacement_1367_);
lean_dec_ref(v_replacement_1367_);
lean_dec_ref(v_pattern_1366_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(lean_object* v_s_1369_, lean_object* v_replacement_1370_, lean_object* v_inst_1371_, lean_object* v_R_1372_, lean_object* v_a_1373_, lean_object* v_b_1374_, lean_object* v_c_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1369_, v_replacement_1370_, v_a_1373_, v_b_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___boxed(lean_object* v_s_1377_, lean_object* v_replacement_1378_, lean_object* v_inst_1379_, lean_object* v_R_1380_, lean_object* v_a_1381_, lean_object* v_b_1382_, lean_object* v_c_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0(v_s_1377_, v_replacement_1378_, v_inst_1379_, v_R_1380_, v_a_1381_, v_b_1382_, v_c_1383_);
lean_dec_ref(v_replacement_1378_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(lean_object* v_s_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1386_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_string_utf8_byte_size(v_s_1385_);
v___x_1389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1389_, 0, v_s_1385_);
lean_ctor_set(v___x_1389_, 1, v___x_1387_);
lean_ctor_set(v___x_1389_, 2, v___x_1388_);
v___x_1390_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0___redArg(v___x_1389_, v___x_1386_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg(){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___closed__0));
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg___boxed(lean_object* v___dummy_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
return v_res_1396_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___redArg();
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(lean_object* v_s_1398_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___boxed(lean_object* v_s_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1(v_s_1400_);
lean_dec_ref(v_s_1400_);
return v_res_1401_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0));
v___x_1407_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1406_);
return v___x_1407_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__1);
v___x_1410_ = ((lean_object*)(l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__0));
v___x_1411_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___x_1409_);
lean_ctor_set(v___x_1411_, 2, v___x_1408_);
lean_ctor_set(v___x_1411_, 3, v___x_1408_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(lean_object* v_s_1412_, lean_object* v_replacement_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_1415_ = lean_obj_once(&l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___closed__2);
v___x_1416_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace_spec__0_spec__0___redArg(v_s_1412_, v_replacement_1413_, v___x_1415_, v___x_1414_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg___boxed(lean_object* v_s_1417_, lean_object* v_replacement_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1417_, v_replacement_1418_);
lean_dec_ref(v_replacement_1418_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(lean_object* v_s_1420_, lean_object* v___x_1421_, lean_object* v___x_1422_, lean_object* v_a_1423_, lean_object* v_b_1424_){
_start:
{
lean_object* v_it_1426_; lean_object* v_startInclusive_1427_; lean_object* v_endExclusive_1428_; 
if (lean_obj_tag(v_a_1423_) == 0)
{
lean_object* v_currPos_1436_; lean_object* v_searcher_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1465_; 
v_currPos_1436_ = lean_ctor_get(v_a_1423_, 0);
v_searcher_1437_ = lean_ctor_get(v_a_1423_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_a_1423_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1439_ = v_a_1423_;
v_isShared_1440_ = v_isSharedCheck_1465_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_searcher_1437_);
lean_inc(v_currPos_1436_);
lean_dec(v_a_1423_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1465_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
uint8_t v_decide_1451_; 
v_decide_1451_ = lean_nat_dec_eq(v_searcher_1437_, v___x_1422_);
if (v_decide_1451_ == 0)
{
uint32_t v___x_1452_; uint32_t v___x_1453_; uint8_t v___x_1454_; 
v___x_1452_ = lean_string_utf8_get_fast(v_s_1420_, v_searcher_1437_);
v___x_1453_ = 32;
v___x_1454_ = lean_uint32_dec_eq(v___x_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
uint32_t v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = 9;
v___x_1456_ = lean_uint32_dec_eq(v___x_1452_, v___x_1455_);
if (v___x_1456_ == 0)
{
uint32_t v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = 13;
v___x_1458_ = lean_uint32_dec_eq(v___x_1452_, v___x_1457_);
if (v___x_1458_ == 0)
{
uint32_t v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = 10;
v___x_1460_ = lean_uint32_dec_eq(v___x_1452_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_del_object(v___x_1439_);
v___x_1461_ = lean_string_utf8_next_fast(v_s_1420_, v_searcher_1437_);
lean_dec(v_searcher_1437_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_currPos_1436_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v_a_1423_ = v___x_1462_;
goto _start;
}
else
{
goto v___jp_1441_;
}
}
else
{
goto v___jp_1441_;
}
}
else
{
goto v___jp_1441_;
}
}
else
{
goto v___jp_1441_;
}
}
else
{
lean_object* v___x_1464_; 
lean_del_object(v___x_1439_);
lean_dec(v_searcher_1437_);
v___x_1464_ = lean_box(1);
lean_inc(v___x_1422_);
v_it_1426_ = v___x_1464_;
v_startInclusive_1427_ = v_currPos_1436_;
v_endExclusive_1428_ = v___x_1422_;
goto v___jp_1425_;
}
v___jp_1441_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v_slice_1445_; lean_object* v_nextIt_1447_; 
v___x_1442_ = lean_string_utf8_next_fast(v_s_1420_, v_searcher_1437_);
v___x_1443_ = lean_nat_sub(v___x_1442_, v_searcher_1437_);
v___x_1444_ = lean_nat_add(v_searcher_1437_, v___x_1443_);
lean_dec(v___x_1443_);
v_slice_1445_ = l_String_Slice_subslice_x21(v___x_1421_, v_currPos_1436_, v_searcher_1437_);
lean_inc(v___x_1444_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1444_);
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v_nextIt_1447_ = v___x_1439_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1444_);
v_nextIt_1447_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v_startInclusive_1448_; lean_object* v_endExclusive_1449_; 
v_startInclusive_1448_ = lean_ctor_get(v_slice_1445_, 0);
lean_inc(v_startInclusive_1448_);
v_endExclusive_1449_ = lean_ctor_get(v_slice_1445_, 1);
lean_inc(v_endExclusive_1449_);
lean_dec_ref(v_slice_1445_);
v_it_1426_ = v_nextIt_1447_;
v_startInclusive_1427_ = v_startInclusive_1448_;
v_endExclusive_1428_ = v_endExclusive_1449_;
goto v___jp_1425_;
}
}
}
}
else
{
lean_dec(v___x_1422_);
lean_dec_ref(v_s_1420_);
return v_b_1424_;
}
v___jp_1425_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1429_ = lean_nat_sub(v_endExclusive_1428_, v_startInclusive_1427_);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_nat_dec_eq(v___x_1429_, v___x_1430_);
lean_dec(v___x_1429_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_inc_ref(v_s_1420_);
v___x_1432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1432_, 0, v_s_1420_);
lean_ctor_set(v___x_1432_, 1, v_startInclusive_1427_);
lean_ctor_set(v___x_1432_, 2, v_endExclusive_1428_);
v___x_1433_ = lean_array_push(v_b_1424_, v___x_1432_);
v_a_1423_ = v_it_1426_;
v_b_1424_ = v___x_1433_;
goto _start;
}
else
{
lean_dec(v_endExclusive_1428_);
lean_dec(v_startInclusive_1427_);
v_a_1423_ = v_it_1426_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg___boxed(lean_object* v_s_1466_, lean_object* v___x_1467_, lean_object* v___x_1468_, lean_object* v_a_1469_, lean_object* v_b_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1466_, v___x_1467_, v___x_1468_, v_a_1469_, v_b_1470_);
lean_dec_ref(v___x_1467_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(uint8_t v_mode_1478_, lean_object* v_s_1479_){
_start:
{
switch(v_mode_1478_)
{
case 0:
{
return v_s_1479_;
}
case 1:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1480_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_string_utf8_byte_size(v_s_1479_);
v___x_1483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1483_, 0, v_s_1479_);
lean_ctor_set(v___x_1483_, 1, v___x_1481_);
lean_ctor_set(v___x_1483_, 2, v___x_1482_);
v___x_1484_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v___x_1483_, v___x_1480_);
return v___x_1484_;
}
default: 
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1485_ = lean_unsigned_to_nat(0u);
v___x_1486_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__0));
v___x_1487_ = lean_string_utf8_byte_size(v_s_1479_);
lean_inc_ref(v_s_1479_);
v___x_1488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1488_, 0, v_s_1479_);
lean_ctor_set(v___x_1488_, 1, v___x_1485_);
lean_ctor_set(v___x_1488_, 2, v___x_1487_);
v___x_1489_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__1___closed__0);
v___x_1490_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___closed__1));
v___x_1491_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1479_, v___x_1488_, v___x_1487_, v___x_1489_, v___x_1490_);
lean_dec_ref_known(v___x_1488_, 3);
v___x_1492_ = lean_array_to_list(v___x_1491_);
v___x_1493_ = l_String_Slice_intercalate(v___x_1486_, v___x_1492_);
lean_dec(v___x_1492_);
return v___x_1493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply___boxed(lean_object* v_mode_1494_, lean_object* v_s_1495_){
_start:
{
uint8_t v_mode_boxed_1496_; lean_object* v_res_1497_; 
v_mode_boxed_1496_ = lean_unbox(v_mode_1494_);
v_res_1497_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v_mode_boxed_1496_, v_s_1495_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(lean_object* v_s_1498_, lean_object* v_pattern_1499_, lean_object* v_replacement_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___redArg(v_s_1498_, v_replacement_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0___boxed(lean_object* v_s_1502_, lean_object* v_pattern_1503_, lean_object* v_replacement_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_String_Slice_replace___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__0(v_s_1502_, v_pattern_1503_, v_replacement_1504_);
lean_dec_ref(v_replacement_1504_);
lean_dec_ref(v_pattern_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(lean_object* v_s_1506_, lean_object* v___x_1507_, lean_object* v___x_1508_, lean_object* v_inst_1509_, lean_object* v_R_1510_, lean_object* v_a_1511_, lean_object* v_b_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___redArg(v_s_1506_, v___x_1507_, v___x_1508_, v_a_1511_, v_b_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2___boxed(lean_object* v_s_1514_, lean_object* v___x_1515_, lean_object* v___x_1516_, lean_object* v_inst_1517_, lean_object* v_R_1518_, lean_object* v_a_1519_, lean_object* v_b_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply_spec__2(v_s_1514_, v___x_1515_, v___x_1516_, v_inst_1517_, v_R_1518_, v_a_1519_, v_b_1520_);
lean_dec_ref(v___x_1515_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(lean_object* v_hi_1522_, lean_object* v_pivot_1523_, lean_object* v_as_1524_, lean_object* v_i_1525_, lean_object* v_k_1526_){
_start:
{
uint8_t v___x_1527_; 
v___x_1527_ = lean_nat_dec_lt(v_k_1526_, v_hi_1522_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_k_1526_);
v___x_1528_ = lean_array_fswap(v_as_1524_, v_i_1525_, v_hi_1522_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_i_1525_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1530_ = lean_array_fget_borrowed(v_as_1524_, v_k_1526_);
v___x_1531_ = lean_string_dec_lt(v___x_1530_, v_pivot_1523_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_unsigned_to_nat(1u);
v___x_1533_ = lean_nat_add(v_k_1526_, v___x_1532_);
lean_dec(v_k_1526_);
v_k_1526_ = v___x_1533_;
goto _start;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1535_ = lean_array_fswap(v_as_1524_, v_i_1525_, v_k_1526_);
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_nat_add(v_i_1525_, v___x_1536_);
lean_dec(v_i_1525_);
v___x_1538_ = lean_nat_add(v_k_1526_, v___x_1536_);
lean_dec(v_k_1526_);
v_as_1524_ = v___x_1535_;
v_i_1525_ = v___x_1537_;
v_k_1526_ = v___x_1538_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg___boxed(lean_object* v_hi_1540_, lean_object* v_pivot_1541_, lean_object* v_as_1542_, lean_object* v_i_1543_, lean_object* v_k_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1540_, v_pivot_1541_, v_as_1542_, v_i_1543_, v_k_1544_);
lean_dec_ref(v_pivot_1541_);
lean_dec(v_hi_1540_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(lean_object* v_n_1546_, lean_object* v_as_1547_, lean_object* v_lo_1548_, lean_object* v_hi_1549_){
_start:
{
lean_object* v___y_1551_; uint8_t v___x_1561_; 
v___x_1561_ = lean_nat_dec_lt(v_lo_1548_, v_hi_1549_);
if (v___x_1561_ == 0)
{
lean_dec(v_lo_1548_);
return v_as_1547_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_mid_1564_; lean_object* v___y_1566_; lean_object* v___y_1572_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1562_ = lean_nat_add(v_lo_1548_, v_hi_1549_);
v___x_1563_ = lean_unsigned_to_nat(1u);
v_mid_1564_ = lean_nat_shiftr(v___x_1562_, v___x_1563_);
lean_dec(v___x_1562_);
v___x_1577_ = lean_array_fget_borrowed(v_as_1547_, v_mid_1564_);
v___x_1578_ = lean_array_fget_borrowed(v_as_1547_, v_lo_1548_);
v___x_1579_ = lean_string_dec_lt(v___x_1577_, v___x_1578_);
if (v___x_1579_ == 0)
{
v___y_1572_ = v_as_1547_;
goto v___jp_1571_;
}
else
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_array_fswap(v_as_1547_, v_lo_1548_, v_mid_1564_);
v___y_1572_ = v___x_1580_;
goto v___jp_1571_;
}
v___jp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1567_ = lean_array_fget_borrowed(v___y_1566_, v_mid_1564_);
v___x_1568_ = lean_array_fget_borrowed(v___y_1566_, v_hi_1549_);
v___x_1569_ = lean_string_dec_lt(v___x_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_dec(v_mid_1564_);
v___y_1551_ = v___y_1566_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_array_fswap(v___y_1566_, v_mid_1564_, v_hi_1549_);
lean_dec(v_mid_1564_);
v___y_1551_ = v___x_1570_;
goto v___jp_1550_;
}
}
v___jp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1573_ = lean_array_fget_borrowed(v___y_1572_, v_hi_1549_);
v___x_1574_ = lean_array_fget_borrowed(v___y_1572_, v_lo_1548_);
v___x_1575_ = lean_string_dec_lt(v___x_1573_, v___x_1574_);
if (v___x_1575_ == 0)
{
v___y_1566_ = v___y_1572_;
goto v___jp_1565_;
}
else
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_array_fswap(v___y_1572_, v_lo_1548_, v_hi_1549_);
v___y_1566_ = v___x_1576_;
goto v___jp_1565_;
}
}
}
v___jp_1550_:
{
lean_object* v_pivot_1552_; lean_object* v___x_1553_; lean_object* v_fst_1554_; lean_object* v_snd_1555_; uint8_t v___x_1556_; 
v_pivot_1552_ = lean_array_fget(v___y_1551_, v_hi_1549_);
lean_inc_n(v_lo_1548_, 2);
v___x_1553_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1549_, v_pivot_1552_, v___y_1551_, v_lo_1548_, v_lo_1548_);
lean_dec(v_pivot_1552_);
v_fst_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_fst_1554_);
v_snd_1555_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_snd_1555_);
lean_dec_ref(v___x_1553_);
v___x_1556_ = lean_nat_dec_le(v_hi_1549_, v_fst_1554_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1546_, v_snd_1555_, v_lo_1548_, v_fst_1554_);
v___x_1558_ = lean_unsigned_to_nat(1u);
v___x_1559_ = lean_nat_add(v_fst_1554_, v___x_1558_);
lean_dec(v_fst_1554_);
v_as_1547_ = v___x_1557_;
v_lo_1548_ = v___x_1559_;
goto _start;
}
else
{
lean_dec(v_fst_1554_);
lean_dec(v_lo_1548_);
return v_snd_1555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg___boxed(lean_object* v_n_1581_, lean_object* v_as_1582_, lean_object* v_lo_1583_, lean_object* v_hi_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1581_, v_as_1582_, v_lo_1583_, v_hi_1584_);
lean_dec(v_hi_1584_);
lean_dec(v_n_1581_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(uint8_t v_mode_1586_, lean_object* v_msgs_1587_){
_start:
{
if (v_mode_1586_ == 0)
{
return v_msgs_1587_;
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1588_ = lean_array_mk(v_msgs_1587_);
v___x_1589_ = lean_array_get_size(v___x_1588_);
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = lean_nat_dec_eq(v___x_1589_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___y_1600_; uint8_t v___x_1602_; 
v___x_1597_ = lean_unsigned_to_nat(1u);
v___x_1598_ = lean_nat_sub(v___x_1589_, v___x_1597_);
v___x_1602_ = lean_nat_dec_le(v___x_1595_, v___x_1598_);
if (v___x_1602_ == 0)
{
lean_inc(v___x_1598_);
v___y_1600_ = v___x_1598_;
goto v___jp_1599_;
}
else
{
v___y_1600_ = v___x_1595_;
goto v___jp_1599_;
}
v___jp_1599_:
{
uint8_t v___x_1601_; 
v___x_1601_ = lean_nat_dec_le(v___y_1600_, v___x_1598_);
if (v___x_1601_ == 0)
{
lean_dec(v___x_1598_);
lean_inc(v___y_1600_);
v___y_1591_ = v___y_1600_;
v___y_1592_ = v___y_1600_;
goto v___jp_1590_;
}
else
{
v___y_1591_ = v___y_1600_;
v___y_1592_ = v___x_1598_;
goto v___jp_1590_;
}
}
}
else
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_array_to_list(v___x_1588_);
return v___x_1603_;
}
v___jp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v___x_1589_, v___x_1588_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
v___x_1594_ = lean_array_to_list(v___x_1593_);
return v___x_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply___boxed(lean_object* v_mode_1604_, lean_object* v_msgs_1605_){
_start:
{
uint8_t v_mode_boxed_1606_; lean_object* v_res_1607_; 
v_mode_boxed_1606_ = lean_unbox(v_mode_1604_);
v_res_1607_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v_mode_boxed_1606_, v_msgs_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(lean_object* v_n_1608_, lean_object* v_as_1609_, lean_object* v_lo_1610_, lean_object* v_hi_1611_, lean_object* v_w_1612_, lean_object* v_hlo_1613_, lean_object* v_hhi_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___redArg(v_n_1608_, v_as_1609_, v_lo_1610_, v_hi_1611_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0___boxed(lean_object* v_n_1616_, lean_object* v_as_1617_, lean_object* v_lo_1618_, lean_object* v_hi_1619_, lean_object* v_w_1620_, lean_object* v_hlo_1621_, lean_object* v_hhi_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0(v_n_1616_, v_as_1617_, v_lo_1618_, v_hi_1619_, v_w_1620_, v_hlo_1621_, v_hhi_1622_);
lean_dec(v_hi_1619_);
lean_dec(v_n_1616_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(lean_object* v_n_1624_, lean_object* v_lo_1625_, lean_object* v_hi_1626_, lean_object* v_hhi_1627_, lean_object* v_pivot_1628_, lean_object* v_as_1629_, lean_object* v_i_1630_, lean_object* v_k_1631_, lean_object* v_ilo_1632_, lean_object* v_ik_1633_, lean_object* v_w_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___redArg(v_hi_1626_, v_pivot_1628_, v_as_1629_, v_i_1630_, v_k_1631_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0___boxed(lean_object* v_n_1636_, lean_object* v_lo_1637_, lean_object* v_hi_1638_, lean_object* v_hhi_1639_, lean_object* v_pivot_1640_, lean_object* v_as_1641_, lean_object* v_i_1642_, lean_object* v_k_1643_, lean_object* v_ilo_1644_, lean_object* v_ik_1645_, lean_object* v_w_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply_spec__0_spec__0(v_n_1636_, v_lo_1637_, v_hi_1638_, v_hhi_1639_, v_pivot_1640_, v_as_1641_, v_i_1642_, v_k_1643_, v_ilo_1644_, v_ik_1645_, v_w_1646_);
lean_dec_ref(v_pivot_1640_);
lean_dec(v_hi_1638_);
lean_dec(v_lo_1637_);
lean_dec(v_n_1636_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(lean_object* v_as_1648_, size_t v_i_1649_, size_t v_stop_1650_, lean_object* v_b_1651_){
_start:
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_usize_dec_eq(v_i_1649_, v_stop_1650_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v_diagnostics_1654_; lean_object* v_msgLog_1655_; lean_object* v___x_1656_; size_t v___x_1657_; size_t v___x_1658_; 
v___x_1653_ = lean_array_uget_borrowed(v_as_1648_, v_i_1649_);
v_diagnostics_1654_ = lean_ctor_get(v___x_1653_, 1);
v_msgLog_1655_ = lean_ctor_get(v_diagnostics_1654_, 0);
lean_inc_ref(v_msgLog_1655_);
v___x_1656_ = l_Lean_MessageLog_append(v_b_1651_, v_msgLog_1655_);
v___x_1657_ = ((size_t)1ULL);
v___x_1658_ = lean_usize_add(v_i_1649_, v___x_1657_);
v_i_1649_ = v___x_1658_;
v_b_1651_ = v___x_1656_;
goto _start;
}
else
{
return v_b_1651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0___boxed(lean_object* v_as_1660_, lean_object* v_i_1661_, lean_object* v_stop_1662_, lean_object* v_b_1663_){
_start:
{
size_t v_i_boxed_1664_; size_t v_stop_boxed_1665_; lean_object* v_res_1666_; 
v_i_boxed_1664_ = lean_unbox_usize(v_i_1661_);
lean_dec(v_i_1661_);
v_stop_boxed_1665_ = lean_unbox_usize(v_stop_1662_);
lean_dec(v_stop_1662_);
v_res_1666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v_as_1660_, v_i_boxed_1664_, v_stop_boxed_1665_, v_b_1663_);
lean_dec_ref(v_as_1660_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(lean_object* v_as_1667_, size_t v_i_1668_, size_t v_stop_1669_, lean_object* v_b_1670_){
_start:
{
lean_object* v___y_1672_; uint8_t v___x_1676_; 
v___x_1676_ = lean_usize_dec_eq(v_i_1668_, v_stop_1669_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1677_ = lean_array_uget_borrowed(v_as_1667_, v_i_1668_);
v___x_1678_ = l_Lean_MessageLog_empty;
lean_inc(v___x_1677_);
v___x_1679_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1677_);
v___x_1680_ = l_Lean_Language_SnapshotTree_getAll(v___x_1679_);
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = lean_array_get_size(v___x_1680_);
v___x_1683_ = lean_nat_dec_lt(v___x_1681_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref(v___x_1680_);
v___x_1684_ = l_Lean_MessageLog_append(v_b_1670_, v___x_1678_);
v___y_1672_ = v___x_1684_;
goto v___jp_1671_;
}
else
{
size_t v___x_1685_; size_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1685_ = ((size_t)0ULL);
v___x_1686_ = lean_usize_of_nat(v___x_1682_);
v___x_1687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__0(v___x_1680_, v___x_1685_, v___x_1686_, v___x_1678_);
lean_dec_ref(v___x_1680_);
v___x_1688_ = l_Lean_MessageLog_append(v_b_1670_, v___x_1687_);
v___y_1672_ = v___x_1688_;
goto v___jp_1671_;
}
}
else
{
return v_b_1670_;
}
v___jp_1671_:
{
size_t v___x_1673_; size_t v___x_1674_; 
v___x_1673_ = ((size_t)1ULL);
v___x_1674_ = lean_usize_add(v_i_1668_, v___x_1673_);
v_i_1668_ = v___x_1674_;
v_b_1670_ = v___y_1672_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1___boxed(lean_object* v_as_1689_, lean_object* v_i_1690_, lean_object* v_stop_1691_, lean_object* v_b_1692_){
_start:
{
size_t v_i_boxed_1693_; size_t v_stop_boxed_1694_; lean_object* v_res_1695_; 
v_i_boxed_1693_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_stop_boxed_1694_ = lean_unbox_usize(v_stop_1691_);
lean_dec(v_stop_1691_);
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_as_1689_, v_i_boxed_1693_, v_stop_boxed_1694_, v_b_1692_);
lean_dec_ref(v_as_1689_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(lean_object* v_cmd_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_fileName_1702_; lean_object* v_fileMap_1703_; lean_object* v_currRecDepth_1704_; lean_object* v_cmdPos_1705_; lean_object* v_macroStack_1706_; lean_object* v_quotContext_x3f_1707_; lean_object* v_currMacroScope_1708_; lean_object* v_ref_1709_; lean_object* v_cancelTk_x3f_1710_; uint8_t v_suppressElabErrors_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_fileName_1702_ = lean_ctor_get(v_a_1699_, 0);
v_fileMap_1703_ = lean_ctor_get(v_a_1699_, 1);
v_currRecDepth_1704_ = lean_ctor_get(v_a_1699_, 2);
v_cmdPos_1705_ = lean_ctor_get(v_a_1699_, 3);
v_macroStack_1706_ = lean_ctor_get(v_a_1699_, 4);
v_quotContext_x3f_1707_ = lean_ctor_get(v_a_1699_, 5);
v_currMacroScope_1708_ = lean_ctor_get(v_a_1699_, 6);
v_ref_1709_ = lean_ctor_get(v_a_1699_, 7);
v_cancelTk_x3f_1710_ = lean_ctor_get(v_a_1699_, 9);
v_suppressElabErrors_1711_ = lean_ctor_get_uint8(v_a_1699_, sizeof(void*)*10);
v___x_1712_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1710_);
lean_inc(v_ref_1709_);
lean_inc(v_currMacroScope_1708_);
lean_inc(v_quotContext_x3f_1707_);
lean_inc(v_macroStack_1706_);
lean_inc(v_cmdPos_1705_);
lean_inc(v_currRecDepth_1704_);
lean_inc_ref(v_fileMap_1703_);
lean_inc_ref(v_fileName_1702_);
v___x_1713_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1713_, 0, v_fileName_1702_);
lean_ctor_set(v___x_1713_, 1, v_fileMap_1703_);
lean_ctor_set(v___x_1713_, 2, v_currRecDepth_1704_);
lean_ctor_set(v___x_1713_, 3, v_cmdPos_1705_);
lean_ctor_set(v___x_1713_, 4, v_macroStack_1706_);
lean_ctor_set(v___x_1713_, 5, v_quotContext_x3f_1707_);
lean_ctor_set(v___x_1713_, 6, v_currMacroScope_1708_);
lean_ctor_set(v___x_1713_, 7, v_ref_1709_);
lean_ctor_set(v___x_1713_, 8, v___x_1712_);
lean_ctor_set(v___x_1713_, 9, v_cancelTk_x3f_1710_);
lean_ctor_set_uint8(v___x_1713_, sizeof(void*)*10, v_suppressElabErrors_1711_);
v___x_1714_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1698_, v___x_1713_, v_a_1700_);
lean_dec_ref_known(v___x_1713_, 10);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1758_; 
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; 
v_unused_1759_ = lean_ctor_get(v___x_1714_, 0);
lean_dec(v_unused_1759_);
v___x_1716_ = v___x_1714_;
v_isShared_1717_ = v_isSharedCheck_1758_;
goto v_resetjp_1715_;
}
else
{
lean_dec(v___x_1714_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1758_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v_messages_1720_; lean_object* v___y_1722_; lean_object* v_snapshotTasks_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1718_ = lean_st_ref_get(v_a_1700_);
v___x_1719_ = lean_st_ref_get(v_a_1700_);
v_messages_1720_ = lean_ctor_get(v___x_1718_, 1);
lean_inc_ref(v_messages_1720_);
lean_dec(v___x_1718_);
v_snapshotTasks_1750_ = lean_ctor_get(v___x_1719_, 10);
lean_inc_ref(v_snapshotTasks_1750_);
lean_dec(v___x_1719_);
v___x_1751_ = l_Lean_MessageLog_empty;
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = lean_array_get_size(v_snapshotTasks_1750_);
v___x_1754_ = lean_nat_dec_lt(v___x_1752_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_dec_ref(v_snapshotTasks_1750_);
v___y_1722_ = v___x_1751_;
goto v___jp_1721_;
}
else
{
size_t v___x_1755_; size_t v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = ((size_t)0ULL);
v___x_1756_ = lean_usize_of_nat(v___x_1753_);
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1750_, v___x_1755_, v___x_1756_, v___x_1751_);
lean_dec_ref(v_snapshotTasks_1750_);
v___y_1722_ = v___x_1757_;
goto v___jp_1721_;
}
v___jp_1721_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v_env_1725_; lean_object* v_messages_1726_; lean_object* v_scopes_1727_; lean_object* v_usedQuotCtxts_1728_; lean_object* v_nextMacroScope_1729_; lean_object* v_maxRecDepth_1730_; lean_object* v_ngen_1731_; lean_object* v_auxDeclNGen_1732_; lean_object* v_infoState_1733_; lean_object* v_traceState_1734_; lean_object* v_prevLinterStates_1735_; lean_object* v_codeQualityEntryTasks_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1748_; 
v___x_1723_ = l_Lean_MessageLog_append(v_messages_1720_, v___y_1722_);
v___x_1724_ = lean_st_ref_take(v_a_1700_);
v_env_1725_ = lean_ctor_get(v___x_1724_, 0);
v_messages_1726_ = lean_ctor_get(v___x_1724_, 1);
v_scopes_1727_ = lean_ctor_get(v___x_1724_, 2);
v_usedQuotCtxts_1728_ = lean_ctor_get(v___x_1724_, 3);
v_nextMacroScope_1729_ = lean_ctor_get(v___x_1724_, 4);
v_maxRecDepth_1730_ = lean_ctor_get(v___x_1724_, 5);
v_ngen_1731_ = lean_ctor_get(v___x_1724_, 6);
v_auxDeclNGen_1732_ = lean_ctor_get(v___x_1724_, 7);
v_infoState_1733_ = lean_ctor_get(v___x_1724_, 8);
v_traceState_1734_ = lean_ctor_get(v___x_1724_, 9);
v_prevLinterStates_1735_ = lean_ctor_get(v___x_1724_, 11);
v_codeQualityEntryTasks_1736_ = lean_ctor_get(v___x_1724_, 12);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; 
v_unused_1749_ = lean_ctor_get(v___x_1724_, 10);
lean_dec(v_unused_1749_);
v___x_1738_ = v___x_1724_;
v_isShared_1739_ = v_isSharedCheck_1748_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1736_);
lean_inc(v_prevLinterStates_1735_);
lean_inc(v_traceState_1734_);
lean_inc(v_infoState_1733_);
lean_inc(v_auxDeclNGen_1732_);
lean_inc(v_ngen_1731_);
lean_inc(v_maxRecDepth_1730_);
lean_inc(v_nextMacroScope_1729_);
lean_inc(v_usedQuotCtxts_1728_);
lean_inc(v_scopes_1727_);
lean_inc(v_messages_1726_);
lean_inc(v_env_1725_);
lean_dec(v___x_1724_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1748_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1740_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 10, v___x_1740_);
v___x_1742_ = v___x_1738_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_env_1725_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_messages_1726_);
lean_ctor_set(v_reuseFailAlloc_1747_, 2, v_scopes_1727_);
lean_ctor_set(v_reuseFailAlloc_1747_, 3, v_usedQuotCtxts_1728_);
lean_ctor_set(v_reuseFailAlloc_1747_, 4, v_nextMacroScope_1729_);
lean_ctor_set(v_reuseFailAlloc_1747_, 5, v_maxRecDepth_1730_);
lean_ctor_set(v_reuseFailAlloc_1747_, 6, v_ngen_1731_);
lean_ctor_set(v_reuseFailAlloc_1747_, 7, v_auxDeclNGen_1732_);
lean_ctor_set(v_reuseFailAlloc_1747_, 8, v_infoState_1733_);
lean_ctor_set(v_reuseFailAlloc_1747_, 9, v_traceState_1734_);
lean_ctor_set(v_reuseFailAlloc_1747_, 10, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1747_, 11, v_prevLinterStates_1735_);
lean_ctor_set(v_reuseFailAlloc_1747_, 12, v_codeQualityEntryTasks_1736_);
v___x_1742_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1743_ = lean_st_ref_put(v_a_1700_, v___x_1742_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1723_);
v___x_1745_ = v___x_1716_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1723_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
v_a_1760_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1714_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1714_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1768_, v_a_1769_, v_a_1770_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
return v_res_1772_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1773_, lean_object* v_opt_1774_){
_start:
{
lean_object* v_name_1775_; lean_object* v_defValue_1776_; lean_object* v_map_1777_; lean_object* v___x_1778_; 
v_name_1775_ = lean_ctor_get(v_opt_1774_, 0);
v_defValue_1776_ = lean_ctor_get(v_opt_1774_, 1);
v_map_1777_ = lean_ctor_get(v_opts_1773_, 0);
v___x_1778_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1777_, v_name_1775_);
if (lean_obj_tag(v___x_1778_) == 0)
{
uint8_t v___x_1779_; 
v___x_1779_ = lean_unbox(v_defValue_1776_);
return v___x_1779_;
}
else
{
lean_object* v_val_1780_; 
v_val_1780_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v___x_1778_, 1);
if (lean_obj_tag(v_val_1780_) == 1)
{
uint8_t v_v_1781_; 
v_v_1781_ = lean_ctor_get_uint8(v_val_1780_, 0);
lean_dec_ref_known(v_val_1780_, 0);
return v_v_1781_;
}
else
{
uint8_t v___x_1782_; 
lean_dec(v_val_1780_);
v___x_1782_ = lean_unbox(v_defValue_1776_);
return v___x_1782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1783_, lean_object* v_opt_1784_){
_start:
{
uint8_t v_res_1785_; lean_object* v_r_1786_; 
v_res_1785_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1783_, v_opt_1784_);
lean_dec_ref(v_opt_1784_);
lean_dec_ref(v_opts_1783_);
v_r_1786_ = lean_box(v_res_1785_);
return v_r_1786_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg(){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___closed__0));
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___boxed(lean_object* v___dummy_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v_res_1792_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1796_);
lean_dec_ref(v_s_1796_);
return v_res_1797_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_box(1);
v___x_1799_ = l_Lean_MessageData_ofFormat(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1804_ = l_Lean_MessageData_ofFormat(v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1805_, lean_object* v_x_1806_){
_start:
{
if (lean_obj_tag(v_x_1806_) == 0)
{
return v_x_1805_;
}
else
{
lean_object* v_head_1807_; lean_object* v_tail_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1830_; 
v_head_1807_ = lean_ctor_get(v_x_1806_, 0);
v_tail_1808_ = lean_ctor_get(v_x_1806_, 1);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_x_1806_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1810_ = v_x_1806_;
v_isShared_1811_ = v_isSharedCheck_1830_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_tail_1808_);
lean_inc(v_head_1807_);
lean_dec(v_x_1806_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1830_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_before_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1828_; 
v_before_1812_ = lean_ctor_get(v_head_1807_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_head_1807_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v_head_1807_, 1);
lean_dec(v_unused_1829_);
v___x_1814_ = v_head_1807_;
v_isShared_1815_ = v_isSharedCheck_1828_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_before_1812_);
lean_dec(v_head_1807_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1828_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 7);
lean_ctor_set(v___x_1814_, 1, v___x_1816_);
lean_ctor_set(v___x_1814_, 0, v_x_1805_);
v___x_1818_ = v___x_1814_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_x_1805_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1811_ == 0)
{
lean_ctor_set_tag(v___x_1810_, 7);
lean_ctor_set(v___x_1810_, 1, v___x_1819_);
lean_ctor_set(v___x_1810_, 0, v___x_1818_);
v___x_1821_ = v___x_1810_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = l_Lean_MessageData_ofSyntax(v_before_1812_);
v___x_1823_ = l_Lean_indentD(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1821_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v_x_1805_ = v___x_1824_;
v_x_1806_ = v_tail_1808_;
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
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1835_ = l_Lean_MessageData_ofFormat(v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1836_, lean_object* v_macroStack_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v_scopes_1842_; lean_object* v___x_1843_; lean_object* v_opts_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1840_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1841_ = lean_st_ref_get(v___y_1838_);
v_scopes_1842_ = lean_ctor_get(v___x_1841_, 2);
lean_inc(v_scopes_1842_);
lean_dec(v___x_1841_);
v___x_1843_ = l_List_head_x21___redArg(v___x_1840_, v_scopes_1842_);
lean_dec(v_scopes_1842_);
v_opts_1844_ = lean_ctor_get(v___x_1843_, 1);
lean_inc_ref(v_opts_1844_);
lean_dec(v___x_1843_);
v___x_1845_ = l_Lean_Elab_pp_macroStack;
v___x_1846_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1844_, v___x_1845_);
lean_dec_ref(v_opts_1844_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
lean_dec(v_macroStack_1837_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_msgData_1836_);
return v___x_1847_;
}
else
{
if (lean_obj_tag(v_macroStack_1837_) == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v_msgData_1836_);
return v___x_1848_;
}
else
{
lean_object* v_head_1849_; lean_object* v_after_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1865_; 
v_head_1849_ = lean_ctor_get(v_macroStack_1837_, 0);
lean_inc(v_head_1849_);
v_after_1850_ = lean_ctor_get(v_head_1849_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_head_1849_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v_head_1849_, 0);
lean_dec(v_unused_1866_);
v___x_1852_ = v_head_1849_;
v_isShared_1853_ = v_isSharedCheck_1865_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_after_1850_);
lean_dec(v_head_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1865_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 7);
lean_ctor_set(v___x_1852_, 1, v___x_1854_);
lean_ctor_set(v___x_1852_, 0, v_msgData_1836_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_msgData_1836_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_msgData_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1857_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = l_Lean_MessageData_ofSyntax(v_after_1850_);
v___x_1860_ = l_Lean_indentD(v___x_1859_);
v_msgData_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1861_, 0, v___x_1858_);
lean_ctor_set(v_msgData_1861_, 1, v___x_1860_);
v___x_1862_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1861_, v_macroStack_1837_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1867_, lean_object* v_macroStack_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1867_, v_macroStack_1868_, v___y_1869_);
lean_dec(v___y_1869_);
return v_res_1871_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1872_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1875_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1876_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
lean_ctor_set(v___x_1878_, 2, v___x_1877_);
lean_ctor_set(v___x_1878_, 3, v___x_1877_);
lean_ctor_set(v___x_1878_, 4, v___x_1876_);
lean_ctor_set(v___x_1878_, 5, v___x_1876_);
lean_ctor_set(v___x_1878_, 6, v___x_1876_);
lean_ctor_set(v___x_1878_, 7, v___x_1876_);
lean_ctor_set(v___x_1878_, 8, v___x_1876_);
lean_ctor_set(v___x_1878_, 9, v___x_1876_);
lean_ctor_set(v___x_1878_, 10, v___x_1876_);
lean_ctor_set(v___x_1878_, 11, v___x_1875_);
return v___x_1878_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = lean_unsigned_to_nat(32u);
v___x_1880_ = lean_mk_empty_array_with_capacity(v___x_1879_);
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1882_ = ((size_t)5ULL);
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = lean_unsigned_to_nat(32u);
v___x_1885_ = lean_mk_empty_array_with_capacity(v___x_1884_);
v___x_1886_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1887_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
lean_ctor_set(v___x_1887_, 1, v___x_1885_);
lean_ctor_set(v___x_1887_, 2, v___x_1883_);
lean_ctor_set(v___x_1887_, 3, v___x_1883_);
lean_ctor_set_usize(v___x_1887_, 4, v___x_1882_);
return v___x_1887_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1888_ = lean_box(1);
v___x_1889_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1890_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v___x_1889_);
lean_ctor_set(v___x_1891_, 2, v___x_1888_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v_env_1896_; uint8_t v___x_1897_; lean_object* v_env_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v_scopes_1901_; lean_object* v___x_1902_; lean_object* v_opts_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1895_ = lean_st_ref_get(v___y_1893_);
v_env_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc_ref(v_env_1896_);
lean_dec(v___x_1895_);
v___x_1897_ = 0;
v_env_1898_ = l_Lean_Environment_setRecordingDeps(v_env_1896_, v___x_1897_);
v___x_1899_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1900_ = lean_st_ref_get(v___y_1893_);
v_scopes_1901_ = lean_ctor_get(v___x_1900_, 2);
lean_inc(v_scopes_1901_);
lean_dec(v___x_1900_);
v___x_1902_ = l_List_head_x21___redArg(v___x_1899_, v_scopes_1901_);
lean_dec(v_scopes_1901_);
v_opts_1903_ = lean_ctor_get(v___x_1902_, 1);
lean_inc_ref(v_opts_1903_);
lean_dec(v___x_1902_);
v___x_1904_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2);
v___x_1905_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5);
v___x_1906_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1906_, 0, v_env_1898_);
lean_ctor_set(v___x_1906_, 1, v___x_1904_);
lean_ctor_set(v___x_1906_, 2, v___x_1905_);
lean_ctor_set(v___x_1906_, 3, v_opts_1903_);
v___x_1907_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v_msgData_1892_);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_1909_, v___y_1910_);
lean_dec(v___y_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(lean_object* v_msg_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_Elab_Command_getRef___redArg(v___y_1914_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v_macroStack_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v_a_1922_; lean_object* v___x_1923_; lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1932_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v_macroStack_1919_ = lean_ctor_get(v___y_1914_, 4);
v___x_1920_ = l_Lean_Elab_getBetterRef(v_a_1918_, v_macroStack_1919_);
lean_dec(v_a_1918_);
v___x_1921_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msg_1913_, v___y_1915_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref(v___x_1921_);
lean_inc(v_macroStack_1919_);
v___x_1923_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_a_1922_, v_macroStack_1919_, v___y_1915_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1920_);
lean_ctor_set(v___x_1928_, 1, v_a_1924_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set_tag(v___x_1926_, 1);
lean_ctor_set(v___x_1926_, 0, v___x_1928_);
v___x_1930_ = v___x_1926_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec_ref(v_msg_1913_);
v_a_1933_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1917_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1917_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg___boxed(lean_object* v_msg_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(lean_object* v_ref_1946_, lean_object* v_msg_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Elab_Command_getRef___redArg(v___y_1948_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v_fileName_1953_; lean_object* v_fileMap_1954_; lean_object* v_currRecDepth_1955_; lean_object* v_cmdPos_1956_; lean_object* v_macroStack_1957_; lean_object* v_quotContext_x3f_1958_; lean_object* v_currMacroScope_1959_; lean_object* v_snap_x3f_1960_; lean_object* v_cancelTk_x3f_1961_; uint8_t v_suppressElabErrors_1962_; lean_object* v_ref_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v_fileName_1953_ = lean_ctor_get(v___y_1948_, 0);
v_fileMap_1954_ = lean_ctor_get(v___y_1948_, 1);
v_currRecDepth_1955_ = lean_ctor_get(v___y_1948_, 2);
v_cmdPos_1956_ = lean_ctor_get(v___y_1948_, 3);
v_macroStack_1957_ = lean_ctor_get(v___y_1948_, 4);
v_quotContext_x3f_1958_ = lean_ctor_get(v___y_1948_, 5);
v_currMacroScope_1959_ = lean_ctor_get(v___y_1948_, 6);
v_snap_x3f_1960_ = lean_ctor_get(v___y_1948_, 8);
v_cancelTk_x3f_1961_ = lean_ctor_get(v___y_1948_, 9);
v_suppressElabErrors_1962_ = lean_ctor_get_uint8(v___y_1948_, sizeof(void*)*10);
v_ref_1963_ = l_Lean_replaceRef(v_ref_1946_, v_a_1952_);
lean_dec(v_a_1952_);
lean_inc(v_cancelTk_x3f_1961_);
lean_inc(v_snap_x3f_1960_);
lean_inc(v_currMacroScope_1959_);
lean_inc(v_quotContext_x3f_1958_);
lean_inc(v_macroStack_1957_);
lean_inc(v_cmdPos_1956_);
lean_inc(v_currRecDepth_1955_);
lean_inc_ref(v_fileMap_1954_);
lean_inc_ref(v_fileName_1953_);
v___x_1964_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1964_, 0, v_fileName_1953_);
lean_ctor_set(v___x_1964_, 1, v_fileMap_1954_);
lean_ctor_set(v___x_1964_, 2, v_currRecDepth_1955_);
lean_ctor_set(v___x_1964_, 3, v_cmdPos_1956_);
lean_ctor_set(v___x_1964_, 4, v_macroStack_1957_);
lean_ctor_set(v___x_1964_, 5, v_quotContext_x3f_1958_);
lean_ctor_set(v___x_1964_, 6, v_currMacroScope_1959_);
lean_ctor_set(v___x_1964_, 7, v_ref_1963_);
lean_ctor_set(v___x_1964_, 8, v_snap_x3f_1960_);
lean_ctor_set(v___x_1964_, 9, v_cancelTk_x3f_1961_);
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*10, v_suppressElabErrors_1962_);
v___x_1965_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1947_, v___x_1964_, v___y_1949_);
lean_dec_ref_known(v___x_1964_, 10);
return v___x_1965_;
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v_msg_1947_);
v_a_1966_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1951_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1951_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_1974_, lean_object* v_msg_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_1974_, v_msg_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v_ref_1974_);
return v_res_1979_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_1982_ = l_Lean_stringToMessageData(v___x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_unsigned_to_nat(1u);
v___x_1997_ = l_Lean_Syntax_getArg(v_stx_1986_, v___x_1996_);
if (lean_obj_tag(v___x_1997_) == 1)
{
lean_object* v_kind_1998_; 
v_kind_1998_ = lean_ctor_get(v___x_1997_, 1);
lean_inc(v_kind_1998_);
if (lean_obj_tag(v_kind_1998_) == 1)
{
lean_object* v_pre_1999_; 
v_pre_1999_ = lean_ctor_get(v_kind_1998_, 0);
lean_inc(v_pre_1999_);
if (lean_obj_tag(v_pre_1999_) == 1)
{
lean_object* v_pre_2000_; 
v_pre_2000_ = lean_ctor_get(v_pre_1999_, 0);
lean_inc(v_pre_2000_);
if (lean_obj_tag(v_pre_2000_) == 1)
{
lean_object* v_pre_2001_; 
v_pre_2001_ = lean_ctor_get(v_pre_2000_, 0);
lean_inc(v_pre_2001_);
if (lean_obj_tag(v_pre_2001_) == 1)
{
lean_object* v_pre_2002_; 
v_pre_2002_ = lean_ctor_get(v_pre_2001_, 0);
if (lean_obj_tag(v_pre_2002_) == 0)
{
lean_object* v_args_2003_; lean_object* v_str_2004_; lean_object* v_str_2005_; lean_object* v_str_2006_; lean_object* v_str_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_args_2003_ = lean_ctor_get(v___x_1997_, 2);
lean_inc_ref(v_args_2003_);
lean_dec_ref_known(v___x_1997_, 3);
v_str_2004_ = lean_ctor_get(v_kind_1998_, 1);
lean_inc_ref(v_str_2004_);
lean_dec_ref_known(v_kind_1998_, 2);
v_str_2005_ = lean_ctor_get(v_pre_1999_, 1);
lean_inc_ref(v_str_2005_);
lean_dec_ref_known(v_pre_1999_, 2);
v_str_2006_ = lean_ctor_get(v_pre_2000_, 1);
lean_inc_ref(v_str_2006_);
lean_dec_ref_known(v_pre_2000_, 2);
v_str_2007_ = lean_ctor_get(v_pre_2001_, 1);
lean_inc_ref(v_str_2007_);
lean_dec_ref_known(v_pre_2001_, 2);
v___x_2008_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_2009_ = lean_string_dec_eq(v_str_2007_, v___x_2008_);
lean_dec_ref(v_str_2007_);
if (v___x_2009_ == 0)
{
lean_dec_ref(v_str_2006_);
lean_dec_ref(v_str_2005_);
lean_dec_ref(v_str_2004_);
lean_dec_ref(v_args_2003_);
goto v___jp_1990_;
}
else
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2011_ = lean_string_dec_eq(v_str_2006_, v___x_2010_);
lean_dec_ref(v_str_2006_);
if (v___x_2011_ == 0)
{
lean_dec_ref(v_str_2005_);
lean_dec_ref(v_str_2004_);
lean_dec_ref(v_args_2003_);
goto v___jp_1990_;
}
else
{
lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2013_ = lean_string_dec_eq(v_str_2005_, v___x_2012_);
lean_dec_ref(v_str_2005_);
if (v___x_2013_ == 0)
{
lean_dec_ref(v_str_2004_);
lean_dec_ref(v_args_2003_);
goto v___jp_1990_;
}
else
{
lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2015_ = lean_string_dec_eq(v_str_2004_, v___x_2014_);
lean_dec_ref(v_str_2004_);
if (v___x_2015_ == 0)
{
lean_dec_ref(v_args_2003_);
goto v___jp_1990_;
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2016_ = lean_array_get_size(v_args_2003_);
v___x_2017_ = lean_unsigned_to_nat(2u);
v___x_2018_ = lean_nat_dec_eq(v___x_2016_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_dec_ref(v_args_2003_);
goto v___jp_1990_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2020_ = lean_array_fget(v_args_2003_, v___x_2019_);
lean_dec_ref(v_args_2003_);
if (lean_obj_tag(v___x_2020_) == 2)
{
lean_object* v_val_2021_; lean_object* v___x_2022_; 
lean_dec(v_stx_1986_);
v_val_2021_ = lean_ctor_get(v___x_2020_, 1);
lean_inc_ref(v_val_2021_);
lean_dec_ref_known(v___x_2020_, 2);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_val_2021_);
return v___x_2022_;
}
else
{
lean_dec(v___x_2020_);
goto v___jp_1990_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2001_, 2);
lean_dec_ref_known(v_pre_2000_, 2);
lean_dec_ref_known(v_pre_1999_, 2);
lean_dec_ref_known(v_kind_1998_, 2);
lean_dec_ref_known(v___x_1997_, 3);
goto v___jp_1990_;
}
}
else
{
lean_dec_ref_known(v_pre_2000_, 2);
lean_dec(v_pre_2001_);
lean_dec_ref_known(v_pre_1999_, 2);
lean_dec_ref_known(v_kind_1998_, 2);
lean_dec_ref_known(v___x_1997_, 3);
goto v___jp_1990_;
}
}
else
{
lean_dec_ref_known(v_pre_1999_, 2);
lean_dec(v_pre_2000_);
lean_dec_ref_known(v_kind_1998_, 2);
lean_dec_ref_known(v___x_1997_, 3);
goto v___jp_1990_;
}
}
else
{
lean_dec(v_pre_1999_);
lean_dec_ref_known(v_kind_1998_, 2);
lean_dec_ref_known(v___x_1997_, 3);
goto v___jp_1990_;
}
}
else
{
lean_dec_ref_known(v___x_1997_, 3);
lean_dec(v_kind_1998_);
goto v___jp_1990_;
}
}
else
{
lean_dec(v___x_1997_);
goto v___jp_1990_;
}
v___jp_1990_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1991_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_1986_);
v___x_1992_ = l_Lean_MessageData_ofSyntax(v_stx_1986_);
v___x_1993_ = l_Lean_indentD(v___x_1992_);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1991_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_1986_, v___x_1994_, v___y_1987_, v___y_1988_);
lean_dec(v_stx_1986_);
return v___x_1995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2028_, size_t v_sz_2029_, size_t v_i_2030_, lean_object* v_b_2031_){
_start:
{
lean_object* v_a_2033_; uint8_t v___x_2037_; 
v___x_2037_ = lean_usize_dec_lt(v_i_2030_, v_sz_2029_);
if (v___x_2037_ == 0)
{
return v_b_2031_;
}
else
{
lean_object* v_a_2038_; lean_object* v_fst_2039_; lean_object* v_snd_2040_; lean_object* v_out_2041_; uint8_t v___x_2042_; 
v_a_2038_ = lean_array_uget_borrowed(v_as_2028_, v_i_2030_);
v_fst_2039_ = lean_ctor_get(v_a_2038_, 0);
v_snd_2040_ = lean_ctor_get(v_a_2038_, 1);
v_out_2041_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2042_ = lean_string_dec_eq(v_snd_2040_, v_out_2041_);
if (v___x_2042_ == 0)
{
uint8_t v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2043_ = lean_unbox(v_fst_2039_);
v___x_2044_ = l_Lean_Diff_Action_linePrefix(v___x_2043_);
v___x_2045_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2046_ = lean_string_append(v___x_2044_, v___x_2045_);
v___x_2047_ = lean_string_append(v___x_2046_, v_snd_2040_);
v___x_2048_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2049_ = lean_string_append(v___x_2047_, v___x_2048_);
v___x_2050_ = lean_string_append(v_b_2031_, v___x_2049_);
lean_dec_ref(v___x_2049_);
v_a_2033_ = v___x_2050_;
goto v___jp_2032_;
}
else
{
uint8_t v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2051_ = lean_unbox(v_fst_2039_);
v___x_2052_ = l_Lean_Diff_Action_linePrefix(v___x_2051_);
v___x_2053_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2054_ = lean_string_append(v___x_2052_, v___x_2053_);
v___x_2055_ = lean_string_append(v_b_2031_, v___x_2054_);
lean_dec_ref(v___x_2054_);
v_a_2033_ = v___x_2055_;
goto v___jp_2032_;
}
}
v___jp_2032_:
{
size_t v___x_2034_; size_t v___x_2035_; 
v___x_2034_ = ((size_t)1ULL);
v___x_2035_ = lean_usize_add(v_i_2030_, v___x_2034_);
v_i_2030_ = v___x_2035_;
v_b_2031_ = v_a_2033_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2056_, lean_object* v_sz_2057_, lean_object* v_i_2058_, lean_object* v_b_2059_){
_start:
{
size_t v_sz_boxed_2060_; size_t v_i_boxed_2061_; lean_object* v_res_2062_; 
v_sz_boxed_2060_ = lean_unbox_usize(v_sz_2057_);
lean_dec(v_sz_2057_);
v_i_boxed_2061_ = lean_unbox_usize(v_i_2058_);
lean_dec(v_i_2058_);
v_res_2062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2056_, v_sz_boxed_2060_, v_i_boxed_2061_, v_b_2059_);
lean_dec_ref(v_as_2056_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2063_){
_start:
{
lean_object* v_out_2064_; size_t v_sz_2065_; size_t v___x_2066_; lean_object* v___x_2067_; 
v_out_2064_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v_sz_2065_ = lean_array_size(v_lines_2063_);
v___x_2066_ = ((size_t)0ULL);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2063_, v_sz_2065_, v___x_2066_, v_out_2064_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2068_);
lean_dec_ref(v_lines_2068_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2070_, lean_object* v_as_x27_2071_, lean_object* v_b_2072_){
_start:
{
if (lean_obj_tag(v_as_x27_2071_) == 0)
{
lean_object* v___x_2074_; 
lean_dec_ref(v_filterFn_2070_);
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v_b_2072_);
return v___x_2074_;
}
else
{
lean_object* v_head_2075_; uint8_t v_isSilent_2076_; 
v_head_2075_ = lean_ctor_get(v_as_x27_2071_, 0);
v_isSilent_2076_ = lean_ctor_get_uint8(v_head_2075_, sizeof(void*)*5 + 2);
if (v_isSilent_2076_ == 0)
{
lean_object* v_tail_2077_; lean_object* v_fst_2078_; lean_object* v_snd_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2099_; 
v_tail_2077_ = lean_ctor_get(v_as_x27_2071_, 1);
v_fst_2078_ = lean_ctor_get(v_b_2072_, 0);
v_snd_2079_ = lean_ctor_get(v_b_2072_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_b_2072_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2081_ = v_b_2072_;
v_isShared_2082_ = v_isSharedCheck_2099_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_snd_2079_);
lean_inc(v_fst_2078_);
lean_dec(v_b_2072_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2099_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
lean_inc_ref(v_filterFn_2070_);
lean_inc(v_head_2075_);
v___x_2083_ = lean_apply_1(v_filterFn_2070_, v_head_2075_);
v___x_2084_ = lean_unbox(v___x_2083_);
switch(v___x_2084_)
{
case 0:
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
lean_inc(v_head_2075_);
v___x_2085_ = l_Lean_MessageLog_add(v_head_2075_, v_fst_2078_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2085_);
v___x_2087_ = v___x_2081_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_snd_2079_);
v___x_2087_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
v_as_x27_2071_ = v_tail_2077_;
v_b_2072_ = v___x_2087_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2091_; 
if (v_isShared_2082_ == 0)
{
v___x_2091_ = v___x_2081_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_fst_2078_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_snd_2079_);
v___x_2091_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
v_as_x27_2071_ = v_tail_2077_;
v_b_2072_ = v___x_2091_;
goto _start;
}
}
default: 
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
lean_inc(v_head_2075_);
v___x_2094_ = l_Lean_MessageLog_add(v_head_2075_, v_snd_2079_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v___x_2094_);
v___x_2096_ = v___x_2081_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_fst_2078_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
v_as_x27_2071_ = v_tail_2077_;
v_b_2072_ = v___x_2096_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2100_; lean_object* v_fst_2101_; lean_object* v_snd_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2110_; 
v_tail_2100_ = lean_ctor_get(v_as_x27_2071_, 1);
v_fst_2101_ = lean_ctor_get(v_b_2072_, 0);
v_snd_2102_ = lean_ctor_get(v_b_2072_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_b_2072_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2104_ = v_b_2072_;
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_snd_2102_);
lean_inc(v_fst_2101_);
lean_dec(v_b_2072_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_fst_2101_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_snd_2102_);
v___x_2107_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
v_as_x27_2071_ = v_tail_2100_;
v_b_2072_ = v___x_2107_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2111_, lean_object* v_as_x27_2112_, lean_object* v_b_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2111_, v_as_x27_2112_, v_b_2113_);
lean_dec(v_as_x27_2112_);
return v_res_2115_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2116_, lean_object* v_a_2117_, uint8_t v_b_2118_){
_start:
{
uint8_t v___x_2119_; 
v___x_2119_ = 0;
switch(lean_obj_tag(v_a_2117_))
{
case 0:
{
lean_object* v_pos_2120_; lean_object* v_startInclusive_2121_; lean_object* v_endExclusive_2122_; lean_object* v___x_2123_; uint8_t v_decide_2124_; 
v_pos_2120_ = lean_ctor_get(v_a_2117_, 0);
lean_inc(v_pos_2120_);
lean_dec_ref_known(v_a_2117_, 1);
v_startInclusive_2121_ = lean_ctor_get(v_s_2116_, 1);
v_endExclusive_2122_ = lean_ctor_get(v_s_2116_, 2);
v___x_2123_ = lean_nat_sub(v_endExclusive_2122_, v_startInclusive_2121_);
v_decide_2124_ = lean_nat_dec_eq(v_pos_2120_, v___x_2123_);
lean_dec(v___x_2123_);
lean_dec(v_pos_2120_);
if (v_decide_2124_ == 0)
{
uint8_t v___x_2125_; 
v___x_2125_ = 1;
return v___x_2125_;
}
else
{
return v_decide_2124_;
}
}
case 1:
{
lean_object* v_pos_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2139_; 
v_pos_2126_ = lean_ctor_get(v_a_2117_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_a_2117_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2128_ = v_a_2117_;
v_isShared_2129_ = v_isSharedCheck_2139_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_pos_2126_);
lean_dec(v_a_2117_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2139_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_str_2130_; lean_object* v_startInclusive_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
v_str_2130_ = lean_ctor_get(v_s_2116_, 0);
v_startInclusive_2131_ = lean_ctor_get(v_s_2116_, 1);
v___x_2132_ = lean_nat_add(v_startInclusive_2131_, v_pos_2126_);
lean_dec(v_pos_2126_);
v___x_2133_ = lean_string_utf8_next_fast(v_str_2130_, v___x_2132_);
lean_dec(v___x_2132_);
v___x_2134_ = lean_nat_sub(v___x_2133_, v_startInclusive_2131_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2134_);
v___x_2136_ = v___x_2128_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
v_a_2117_ = v___x_2136_;
v_b_2118_ = v___x_2119_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2140_; lean_object* v_table_2141_; lean_object* v_stackPos_2142_; lean_object* v_needlePos_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2198_; 
v_needle_2140_ = lean_ctor_get(v_a_2117_, 0);
v_table_2141_ = lean_ctor_get(v_a_2117_, 1);
v_stackPos_2142_ = lean_ctor_get(v_a_2117_, 2);
v_needlePos_2143_ = lean_ctor_get(v_a_2117_, 3);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_a_2117_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2145_ = v_a_2117_;
v_isShared_2146_ = v_isSharedCheck_2198_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_needlePos_2143_);
lean_inc(v_stackPos_2142_);
lean_inc(v_table_2141_);
lean_inc(v_needle_2140_);
lean_dec(v_a_2117_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2198_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v_str_2147_; lean_object* v_startInclusive_2148_; lean_object* v_endExclusive_2149_; lean_object* v_str_2150_; lean_object* v_startInclusive_2151_; lean_object* v_endExclusive_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v_str_2147_ = lean_ctor_get(v_needle_2140_, 0);
v_startInclusive_2148_ = lean_ctor_get(v_needle_2140_, 1);
v_endExclusive_2149_ = lean_ctor_get(v_needle_2140_, 2);
v_str_2150_ = lean_ctor_get(v_s_2116_, 0);
v_startInclusive_2151_ = lean_ctor_get(v_s_2116_, 1);
v_endExclusive_2152_ = lean_ctor_get(v_s_2116_, 2);
v___x_2153_ = lean_nat_sub(v_stackPos_2142_, v_needlePos_2143_);
v___x_2154_ = lean_nat_sub(v_endExclusive_2149_, v_startInclusive_2148_);
v___x_2155_ = lean_nat_add(v___x_2153_, v___x_2154_);
v___x_2156_ = lean_nat_sub(v_endExclusive_2152_, v_startInclusive_2151_);
v___x_2157_ = lean_nat_dec_le(v___x_2155_, v___x_2156_);
lean_dec(v___x_2155_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
lean_dec(v___x_2154_);
lean_del_object(v___x_2145_);
lean_dec(v_needlePos_2143_);
lean_dec(v_stackPos_2142_);
lean_dec_ref(v_table_2141_);
lean_dec_ref(v_needle_2140_);
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = lean_nat_add(v___x_2153_, v___x_2158_);
lean_dec(v___x_2153_);
v___x_2160_ = lean_nat_dec_le(v___x_2159_, v___x_2156_);
lean_dec(v___x_2156_);
lean_dec(v___x_2159_);
if (v___x_2160_ == 0)
{
return v_b_2118_;
}
else
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_box(3);
v_a_2117_ = v___x_2161_;
v_b_2118_ = v___x_2119_;
goto _start;
}
}
else
{
lean_object* v___x_2163_; uint8_t v_stackByte_2164_; lean_object* v___x_2165_; uint8_t v_patByte_2166_; uint8_t v___x_2167_; 
lean_dec(v___x_2156_);
lean_dec(v___x_2153_);
v___x_2163_ = lean_nat_add(v_startInclusive_2151_, v_stackPos_2142_);
v_stackByte_2164_ = lean_string_get_byte_fast(v_str_2150_, v___x_2163_);
v___x_2165_ = lean_nat_add(v_startInclusive_2148_, v_needlePos_2143_);
v_patByte_2166_ = lean_string_get_byte_fast(v_str_2147_, v___x_2165_);
v___x_2167_ = lean_uint8_dec_eq(v_stackByte_2164_, v_patByte_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; uint8_t v_decide_2169_; 
lean_dec(v___x_2154_);
v___x_2168_ = lean_unsigned_to_nat(0u);
v_decide_2169_ = lean_nat_dec_eq(v_needlePos_2143_, v___x_2168_);
if (v_decide_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v_newNeedlePos_2172_; uint8_t v___x_2173_; 
v___x_2170_ = lean_unsigned_to_nat(1u);
v___x_2171_ = lean_nat_sub(v_needlePos_2143_, v___x_2170_);
lean_dec(v_needlePos_2143_);
v_newNeedlePos_2172_ = lean_array_fget_borrowed(v_table_2141_, v___x_2171_);
lean_dec(v___x_2171_);
v___x_2173_ = lean_nat_dec_eq(v_newNeedlePos_2172_, v___x_2168_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2175_; 
lean_inc(v_newNeedlePos_2172_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 3, v_newNeedlePos_2172_);
v___x_2175_ = v___x_2145_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_needle_2140_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_table_2141_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_stackPos_2142_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_newNeedlePos_2172_);
v___x_2175_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
v_a_2117_ = v___x_2175_;
v_b_2118_ = v___x_2119_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2178_; lean_object* v___x_2180_; 
v_nextStackPos_2178_ = l_String_Slice_posGE___redArg(v_s_2116_, v_stackPos_2142_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 3, v___x_2168_);
lean_ctor_set(v___x_2145_, 2, v_nextStackPos_2178_);
v___x_2180_ = v___x_2145_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_needle_2140_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_table_2141_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_nextStackPos_2178_);
lean_ctor_set(v_reuseFailAlloc_2182_, 3, v___x_2168_);
v___x_2180_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
v_a_2117_ = v___x_2180_;
v_b_2118_ = v___x_2119_;
goto _start;
}
}
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v_nextStackPos_2185_; lean_object* v___x_2187_; 
lean_dec(v_needlePos_2143_);
v___x_2183_ = lean_unsigned_to_nat(1u);
v___x_2184_ = lean_nat_add(v_stackPos_2142_, v___x_2183_);
lean_dec(v_stackPos_2142_);
v_nextStackPos_2185_ = l_String_Slice_posGE___redArg(v_s_2116_, v___x_2184_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 3, v___x_2168_);
lean_ctor_set(v___x_2145_, 2, v_nextStackPos_2185_);
v___x_2187_ = v___x_2145_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_needle_2140_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_table_2141_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_nextStackPos_2185_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v___x_2168_);
v___x_2187_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
v_a_2117_ = v___x_2187_;
v_b_2118_ = v___x_2119_;
goto _start;
}
}
}
else
{
lean_object* v___x_2190_; lean_object* v_nextNeedlePos_2191_; uint8_t v_decide_2192_; 
v___x_2190_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2191_ = lean_nat_add(v_needlePos_2143_, v___x_2190_);
lean_dec(v_needlePos_2143_);
v_decide_2192_ = lean_nat_dec_eq(v_nextNeedlePos_2191_, v___x_2154_);
lean_dec(v___x_2154_);
if (v_decide_2192_ == 0)
{
lean_object* v_nextStackPos_2193_; lean_object* v___x_2195_; 
v_nextStackPos_2193_ = lean_nat_add(v_stackPos_2142_, v___x_2190_);
lean_dec(v_stackPos_2142_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 3, v_nextNeedlePos_2191_);
lean_ctor_set(v___x_2145_, 2, v_nextStackPos_2193_);
v___x_2195_ = v___x_2145_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_needle_2140_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_table_2141_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_nextStackPos_2193_);
lean_ctor_set(v_reuseFailAlloc_2197_, 3, v_nextNeedlePos_2191_);
v___x_2195_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
v_a_2117_ = v___x_2195_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2191_);
lean_del_object(v___x_2145_);
lean_dec(v_stackPos_2142_);
lean_dec_ref(v_table_2141_);
lean_dec_ref(v_needle_2140_);
return v_decide_2192_;
}
}
}
}
}
default: 
{
return v_b_2118_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2199_, lean_object* v_a_2200_, lean_object* v_b_2201_){
_start:
{
uint8_t v_b_boxed_2202_; uint8_t v_res_2203_; lean_object* v_r_2204_; 
v_b_boxed_2202_ = lean_unbox(v_b_2201_);
v_res_2203_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2199_, v_a_2200_, v_b_boxed_2202_);
lean_dec_ref(v_s_2199_);
v_r_2204_ = lean_box(v_res_2203_);
return v_r_2204_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2207_, lean_object* v_s_2208_){
_start:
{
lean_object* v___y_2210_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = lean_string_utf8_byte_size(v___x_2207_);
v___x_2215_ = lean_nat_dec_eq(v___x_2214_, v___x_2213_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2207_);
lean_ctor_set(v___x_2216_, 1, v___x_2213_);
lean_ctor_set(v___x_2216_, 2, v___x_2214_);
v___x_2217_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2216_);
v___x_2218_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
lean_ctor_set(v___x_2218_, 2, v___x_2213_);
lean_ctor_set(v___x_2218_, 3, v___x_2213_);
v___y_2210_ = v___x_2218_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2219_; 
lean_dec_ref(v___x_2207_);
v___x_2219_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___closed__0));
v___y_2210_ = v___x_2219_;
goto v___jp_2209_;
}
v___jp_2209_:
{
uint8_t v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = 0;
v___x_2212_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2208_, v___y_2210_, v___x_2211_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2220_, lean_object* v_s_2221_){
_start:
{
uint8_t v_res_2222_; lean_object* v_r_2223_; 
v_res_2222_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2220_, v_s_2221_);
lean_dec_ref(v_s_2221_);
v_r_2223_ = lean_box(v_res_2222_);
return v_r_2223_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v_suppressElabErrors_2224_, lean_object* v_x_2225_){
_start:
{
if (lean_obj_tag(v_x_2225_) == 1)
{
lean_object* v_pre_2226_; 
v_pre_2226_ = lean_ctor_get(v_x_2225_, 0);
if (lean_obj_tag(v_pre_2226_) == 0)
{
lean_object* v_str_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v_str_2227_ = lean_ctor_get(v_x_2225_, 1);
v___x_2228_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2229_ = lean_string_dec_eq(v_str_2227_, v___x_2228_);
if (v___x_2229_ == 0)
{
return v___x_2229_;
}
else
{
return v_suppressElabErrors_2224_;
}
}
else
{
uint8_t v___x_2230_; 
v___x_2230_ = 0;
return v___x_2230_;
}
}
else
{
uint8_t v___x_2231_; 
v___x_2231_ = 0;
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_2232_, lean_object* v_x_2233_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2234_; uint8_t v_res_2235_; lean_object* v_r_2236_; 
v_suppressElabErrors_boxed_2234_ = lean_unbox(v_suppressElabErrors_2232_);
v_res_2235_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v_suppressElabErrors_boxed_2234_, v_x_2233_);
lean_dec(v_x_2233_);
v_r_2236_ = lean_box(v_res_2235_);
return v_r_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2237_, lean_object* v_msgData_2238_, uint8_t v_severity_2239_, uint8_t v_isSilent_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___y_2245_; lean_object* v___y_2246_; uint8_t v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; uint8_t v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; uint8_t v___y_2310_; uint8_t v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; uint8_t v___y_2336_; uint8_t v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; uint8_t v___y_2343_; uint8_t v___y_2344_; uint8_t v___x_2359_; uint8_t v___y_2361_; uint8_t v___x_2371_; 
v___x_2359_ = 2;
v___x_2371_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2239_, v___x_2359_);
if (v___x_2371_ == 0)
{
v___y_2361_ = v___x_2371_;
goto v___jp_2360_;
}
else
{
uint8_t v___x_2372_; 
lean_inc_ref(v_msgData_2238_);
v___x_2372_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2238_);
if (v___x_2372_ == 0)
{
v___y_2361_ = v___x_2372_;
goto v___jp_2360_;
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec_ref(v_msgData_2238_);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
v___jp_2244_:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Elab_Command_getScope___redArg(v___y_2252_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v_currNamespace_2255_; lean_object* v___x_2256_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v_currNamespace_2255_ = lean_ctor_get(v_a_2254_, 2);
lean_inc(v_currNamespace_2255_);
lean_dec(v_a_2254_);
v___x_2256_ = l_Lean_Elab_Command_getScope___redArg(v___y_2252_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2292_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2292_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2292_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_openDecls_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v_env_2266_; lean_object* v_messages_2267_; lean_object* v_scopes_2268_; lean_object* v_usedQuotCtxts_2269_; lean_object* v_nextMacroScope_2270_; lean_object* v_maxRecDepth_2271_; lean_object* v_ngen_2272_; lean_object* v_auxDeclNGen_2273_; lean_object* v_infoState_2274_; lean_object* v_traceState_2275_; lean_object* v_snapshotTasks_2276_; lean_object* v_prevLinterStates_2277_; lean_object* v_codeQualityEntryTasks_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2291_; 
v_openDecls_2261_ = lean_ctor_get(v_a_2257_, 3);
lean_inc(v_openDecls_2261_);
lean_dec(v_a_2257_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v_currNamespace_2255_);
lean_ctor_set(v___x_2262_, 1, v_openDecls_2261_);
v___x_2263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v___y_2248_);
lean_inc_ref(v___y_2246_);
lean_inc_ref(v___y_2249_);
v___x_2264_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2264_, 0, v___y_2249_);
lean_ctor_set(v___x_2264_, 1, v___y_2251_);
lean_ctor_set(v___x_2264_, 2, v___y_2245_);
lean_ctor_set(v___x_2264_, 3, v___y_2246_);
lean_ctor_set(v___x_2264_, 4, v___x_2263_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*5, v___y_2247_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*5 + 1, v___y_2250_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*5 + 2, v_isSilent_2240_);
v___x_2265_ = lean_st_ref_take(v___y_2252_);
v_env_2266_ = lean_ctor_get(v___x_2265_, 0);
v_messages_2267_ = lean_ctor_get(v___x_2265_, 1);
v_scopes_2268_ = lean_ctor_get(v___x_2265_, 2);
v_usedQuotCtxts_2269_ = lean_ctor_get(v___x_2265_, 3);
v_nextMacroScope_2270_ = lean_ctor_get(v___x_2265_, 4);
v_maxRecDepth_2271_ = lean_ctor_get(v___x_2265_, 5);
v_ngen_2272_ = lean_ctor_get(v___x_2265_, 6);
v_auxDeclNGen_2273_ = lean_ctor_get(v___x_2265_, 7);
v_infoState_2274_ = lean_ctor_get(v___x_2265_, 8);
v_traceState_2275_ = lean_ctor_get(v___x_2265_, 9);
v_snapshotTasks_2276_ = lean_ctor_get(v___x_2265_, 10);
v_prevLinterStates_2277_ = lean_ctor_get(v___x_2265_, 11);
v_codeQualityEntryTasks_2278_ = lean_ctor_get(v___x_2265_, 12);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2280_ = v___x_2265_;
v_isShared_2281_ = v_isSharedCheck_2291_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2278_);
lean_inc(v_prevLinterStates_2277_);
lean_inc(v_snapshotTasks_2276_);
lean_inc(v_traceState_2275_);
lean_inc(v_infoState_2274_);
lean_inc(v_auxDeclNGen_2273_);
lean_inc(v_ngen_2272_);
lean_inc(v_maxRecDepth_2271_);
lean_inc(v_nextMacroScope_2270_);
lean_inc(v_usedQuotCtxts_2269_);
lean_inc(v_scopes_2268_);
lean_inc(v_messages_2267_);
lean_inc(v_env_2266_);
lean_dec(v___x_2265_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2291_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2282_ = lean_box(0);
v___x_2283_ = l_Lean_MessageLog_add(v___x_2264_, v_messages_2267_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 1, v___x_2283_);
v___x_2285_ = v___x_2280_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_env_2266_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_scopes_2268_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v_usedQuotCtxts_2269_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v_nextMacroScope_2270_);
lean_ctor_set(v_reuseFailAlloc_2290_, 5, v_maxRecDepth_2271_);
lean_ctor_set(v_reuseFailAlloc_2290_, 6, v_ngen_2272_);
lean_ctor_set(v_reuseFailAlloc_2290_, 7, v_auxDeclNGen_2273_);
lean_ctor_set(v_reuseFailAlloc_2290_, 8, v_infoState_2274_);
lean_ctor_set(v_reuseFailAlloc_2290_, 9, v_traceState_2275_);
lean_ctor_set(v_reuseFailAlloc_2290_, 10, v_snapshotTasks_2276_);
lean_ctor_set(v_reuseFailAlloc_2290_, 11, v_prevLinterStates_2277_);
lean_ctor_set(v_reuseFailAlloc_2290_, 12, v_codeQualityEntryTasks_2278_);
v___x_2285_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = lean_st_ref_put(v___y_2252_, v___x_2285_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2282_);
v___x_2288_ = v___x_2259_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2282_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_currNamespace_2255_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2245_);
v_a_2293_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2256_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2256_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v___y_2251_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2245_);
v_a_2301_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2253_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2253_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
v___jp_2309_:
{
lean_object* v_fileName_2314_; lean_object* v_fileMap_2315_; uint8_t v_suppressElabErrors_2316_; lean_object* v___x_2317_; lean_object* v___f_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2334_; 
v_fileName_2314_ = lean_ctor_get(v___y_2241_, 0);
v_fileMap_2315_ = lean_ctor_get(v___y_2241_, 1);
v_suppressElabErrors_2316_ = lean_ctor_get_uint8(v___y_2241_, sizeof(void*)*10);
v___x_2317_ = lean_box(v_suppressElabErrors_2316_);
v___f_2318_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2318_, 0, v___x_2317_);
v___x_2319_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2238_);
v___x_2320_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2319_, v___y_2242_);
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_inc_ref_n(v_fileMap_2315_, 2);
v___x_2325_ = l_Lean_FileMap_toPosition(v_fileMap_2315_, v___y_2312_);
lean_dec(v___y_2312_);
v___x_2326_ = l_Lean_FileMap_toPosition(v_fileMap_2315_, v___y_2313_);
lean_dec(v___y_2313_);
v___x_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
v___x_2328_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
if (v_suppressElabErrors_2316_ == 0)
{
lean_del_object(v___x_2323_);
lean_dec_ref(v___f_2318_);
v___y_2245_ = v___x_2327_;
v___y_2246_ = v___x_2328_;
v___y_2247_ = v___y_2310_;
v___y_2248_ = v_a_2321_;
v___y_2249_ = v_fileName_2314_;
v___y_2250_ = v___y_2311_;
v___y_2251_ = v___x_2325_;
v___y_2252_ = v___y_2242_;
goto v___jp_2244_;
}
else
{
uint8_t v___x_2329_; 
lean_inc(v_a_2321_);
v___x_2329_ = l_Lean_MessageData_hasTag(v___f_2318_, v_a_2321_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_dec_ref_known(v___x_2327_, 1);
lean_dec_ref(v___x_2325_);
lean_dec(v_a_2321_);
v___x_2330_ = lean_box(0);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2330_);
v___x_2332_ = v___x_2323_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
else
{
lean_del_object(v___x_2323_);
v___y_2245_ = v___x_2327_;
v___y_2246_ = v___x_2328_;
v___y_2247_ = v___y_2310_;
v___y_2248_ = v_a_2321_;
v___y_2249_ = v_fileName_2314_;
v___y_2250_ = v___y_2311_;
v___y_2251_ = v___x_2325_;
v___y_2252_ = v___y_2242_;
goto v___jp_2244_;
}
}
}
}
v___jp_2335_:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_Syntax_getTailPos_x3f(v___y_2338_, v___y_2336_);
lean_dec(v___y_2338_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_inc(v___y_2339_);
v___y_2310_ = v___y_2336_;
v___y_2311_ = v___y_2337_;
v___y_2312_ = v___y_2339_;
v___y_2313_ = v___y_2339_;
goto v___jp_2309_;
}
else
{
lean_object* v_val_2341_; 
v_val_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_val_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___y_2310_ = v___y_2336_;
v___y_2311_ = v___y_2337_;
v___y_2312_ = v___y_2339_;
v___y_2313_ = v_val_2341_;
goto v___jp_2309_;
}
}
v___jp_2342_:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Elab_Command_getRef___redArg(v___y_2241_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v_ref_2347_; lean_object* v___x_2348_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v_ref_2347_ = l_Lean_replaceRef(v_ref_2237_, v_a_2346_);
lean_dec(v_a_2346_);
v___x_2348_ = l_Lean_Syntax_getPos_x3f(v_ref_2347_, v___y_2343_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_unsigned_to_nat(0u);
v___y_2336_ = v___y_2343_;
v___y_2337_ = v___y_2344_;
v___y_2338_ = v_ref_2347_;
v___y_2339_ = v___x_2349_;
goto v___jp_2335_;
}
else
{
lean_object* v_val_2350_; 
v_val_2350_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_val_2350_);
lean_dec_ref_known(v___x_2348_, 1);
v___y_2336_ = v___y_2343_;
v___y_2337_ = v___y_2344_;
v___y_2338_ = v_ref_2347_;
v___y_2339_ = v_val_2350_;
goto v___jp_2335_;
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec_ref(v_msgData_2238_);
v_a_2351_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2345_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2345_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
v___jp_2360_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v_scopes_2364_; lean_object* v___x_2365_; lean_object* v_opts_2366_; uint8_t v___x_2367_; uint8_t v___x_2368_; 
v___x_2362_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2363_ = lean_st_ref_get(v___y_2242_);
v_scopes_2364_ = lean_ctor_get(v___x_2363_, 2);
lean_inc(v_scopes_2364_);
lean_dec(v___x_2363_);
v___x_2365_ = l_List_head_x21___redArg(v___x_2362_, v_scopes_2364_);
lean_dec(v_scopes_2364_);
v_opts_2366_ = lean_ctor_get(v___x_2365_, 1);
lean_inc_ref(v_opts_2366_);
lean_dec(v___x_2365_);
v___x_2367_ = 1;
v___x_2368_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2239_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_dec_ref(v_opts_2366_);
v___y_2343_ = v___y_2361_;
v___y_2344_ = v_severity_2239_;
goto v___jp_2342_;
}
else
{
lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2369_ = l_Lean_warningAsError;
v___x_2370_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2366_, v___x_2369_);
lean_dec_ref(v_opts_2366_);
if (v___x_2370_ == 0)
{
v___y_2343_ = v___y_2361_;
v___y_2344_ = v_severity_2239_;
goto v___jp_2342_;
}
else
{
v___y_2343_ = v___y_2361_;
v___y_2344_ = v___x_2359_;
goto v___jp_2342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2375_, lean_object* v_msgData_2376_, lean_object* v_severity_2377_, lean_object* v_isSilent_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
uint8_t v_severity_boxed_2382_; uint8_t v_isSilent_boxed_2383_; lean_object* v_res_2384_; 
v_severity_boxed_2382_ = lean_unbox(v_severity_2377_);
v_isSilent_boxed_2383_ = lean_unbox(v_isSilent_2378_);
v_res_2384_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2375_, v_msgData_2376_, v_severity_boxed_2382_, v_isSilent_boxed_2383_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v_ref_2375_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2385_, lean_object* v_msgData_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
uint8_t v___x_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; 
v___x_2390_ = 2;
v___x_2391_ = 0;
v___x_2392_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2385_, v_msgData_2386_, v___x_2390_, v___x_2391_, v___y_2387_, v___y_2388_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2393_, lean_object* v_msgData_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2393_, v_msgData_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v_ref_2393_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2399_, lean_object* v___x_2400_, lean_object* v___x_2401_, lean_object* v_a_2402_, lean_object* v_b_2403_){
_start:
{
lean_object* v_it_2405_; lean_object* v_startInclusive_2406_; lean_object* v_endExclusive_2407_; 
if (lean_obj_tag(v_a_2402_) == 0)
{
lean_object* v_currPos_2412_; lean_object* v_searcher_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2442_; 
v_currPos_2412_ = lean_ctor_get(v_a_2402_, 0);
v_searcher_2413_ = lean_ctor_get(v_a_2402_, 1);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_a_2402_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2415_ = v_a_2402_;
v_isShared_2416_ = v_isSharedCheck_2442_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_searcher_2413_);
lean_inc(v_currPos_2412_);
lean_dec(v_a_2402_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2442_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v_str_2417_; lean_object* v_startInclusive_2418_; lean_object* v_endExclusive_2419_; lean_object* v___x_2420_; uint8_t v_decide_2421_; 
v_str_2417_ = lean_ctor_get(v___x_2400_, 0);
v_startInclusive_2418_ = lean_ctor_get(v___x_2400_, 1);
v_endExclusive_2419_ = lean_ctor_get(v___x_2400_, 2);
v___x_2420_ = lean_nat_sub(v_endExclusive_2419_, v_startInclusive_2418_);
v_decide_2421_ = lean_nat_dec_eq(v_searcher_2413_, v___x_2420_);
lean_dec(v___x_2420_);
if (v_decide_2421_ == 0)
{
uint32_t v___x_2422_; lean_object* v___x_2423_; uint32_t v___x_2424_; uint8_t v___x_2425_; 
v___x_2422_ = 10;
v___x_2423_ = lean_nat_add(v_startInclusive_2418_, v_searcher_2413_);
v___x_2424_ = lean_string_utf8_get_fast(v_str_2417_, v___x_2423_);
v___x_2425_ = lean_uint32_dec_eq(v___x_2424_, v___x_2422_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
lean_dec(v_searcher_2413_);
v___x_2426_ = lean_string_utf8_next_fast(v_str_2417_, v___x_2423_);
lean_dec(v___x_2423_);
v___x_2427_ = lean_nat_sub(v___x_2426_, v_startInclusive_2418_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 1, v___x_2427_);
v___x_2429_ = v___x_2415_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_currPos_2412_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
v_a_2402_ = v___x_2429_;
goto _start;
}
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v_slice_2435_; lean_object* v_nextIt_2437_; 
v___x_2432_ = lean_string_utf8_next_fast(v_str_2417_, v___x_2423_);
v___x_2433_ = lean_nat_sub(v___x_2432_, v___x_2423_);
lean_dec(v___x_2423_);
v___x_2434_ = lean_nat_add(v_searcher_2413_, v___x_2433_);
lean_dec(v___x_2433_);
v_slice_2435_ = l_String_Slice_subslice_x21(v___x_2400_, v_currPos_2412_, v_searcher_2413_);
lean_inc(v___x_2434_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 1, v___x_2434_);
lean_ctor_set(v___x_2415_, 0, v___x_2434_);
v_nextIt_2437_ = v___x_2415_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v___x_2434_);
v_nextIt_2437_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v_startInclusive_2438_; lean_object* v_endExclusive_2439_; 
v_startInclusive_2438_ = lean_ctor_get(v_slice_2435_, 0);
lean_inc(v_startInclusive_2438_);
v_endExclusive_2439_ = lean_ctor_get(v_slice_2435_, 1);
lean_inc(v_endExclusive_2439_);
lean_dec_ref(v_slice_2435_);
v_it_2405_ = v_nextIt_2437_;
v_startInclusive_2406_ = v_startInclusive_2438_;
v_endExclusive_2407_ = v_endExclusive_2439_;
goto v___jp_2404_;
}
}
}
else
{
lean_object* v___x_2441_; 
lean_del_object(v___x_2415_);
lean_dec(v_searcher_2413_);
v___x_2441_ = lean_box(1);
lean_inc(v___x_2401_);
v_it_2405_ = v___x_2441_;
v_startInclusive_2406_ = v_currPos_2412_;
v_endExclusive_2407_ = v___x_2401_;
goto v___jp_2404_;
}
}
}
else
{
lean_dec(v___x_2401_);
lean_dec_ref(v___x_2399_);
return v_b_2403_;
}
v___jp_2404_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_inc_ref(v___x_2399_);
v___x_2408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2399_);
lean_ctor_set(v___x_2408_, 1, v_startInclusive_2406_);
lean_ctor_set(v___x_2408_, 2, v_endExclusive_2407_);
v___x_2409_ = l_String_Slice_toString(v___x_2408_);
lean_dec_ref_known(v___x_2408_, 3);
v___x_2410_ = lean_array_push(v_b_2403_, v___x_2409_);
v_a_2402_ = v_it_2405_;
v_b_2403_ = v___x_2410_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2443_, lean_object* v___x_2444_, lean_object* v___x_2445_, lean_object* v_a_2446_, lean_object* v_b_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2443_, v___x_2444_, v___x_2445_, v_a_2446_, v_b_2447_);
lean_dec_ref(v___x_2444_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2449_, lean_object* v___x_2450_, lean_object* v___x_2451_, lean_object* v_a_2452_, lean_object* v_b_2453_){
_start:
{
lean_object* v_it_2455_; lean_object* v_startInclusive_2456_; lean_object* v_endExclusive_2457_; 
if (lean_obj_tag(v_a_2452_) == 0)
{
lean_object* v_currPos_2462_; lean_object* v_searcher_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2492_; 
v_currPos_2462_ = lean_ctor_get(v_a_2452_, 0);
v_searcher_2463_ = lean_ctor_get(v_a_2452_, 1);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_a_2452_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2465_ = v_a_2452_;
v_isShared_2466_ = v_isSharedCheck_2492_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_searcher_2463_);
lean_inc(v_currPos_2462_);
lean_dec(v_a_2452_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2492_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v_str_2467_; lean_object* v_startInclusive_2468_; lean_object* v_endExclusive_2469_; lean_object* v___x_2470_; uint8_t v_decide_2471_; 
v_str_2467_ = lean_ctor_get(v___x_2450_, 0);
v_startInclusive_2468_ = lean_ctor_get(v___x_2450_, 1);
v_endExclusive_2469_ = lean_ctor_get(v___x_2450_, 2);
v___x_2470_ = lean_nat_sub(v_endExclusive_2469_, v_startInclusive_2468_);
v_decide_2471_ = lean_nat_dec_eq(v_searcher_2463_, v___x_2470_);
lean_dec(v___x_2470_);
if (v_decide_2471_ == 0)
{
lean_object* v___x_2472_; uint32_t v___x_2473_; uint32_t v___x_2474_; uint8_t v___x_2475_; 
v___x_2472_ = lean_nat_add(v_startInclusive_2468_, v_searcher_2463_);
v___x_2473_ = lean_string_utf8_get_fast(v_str_2467_, v___x_2472_);
v___x_2474_ = 10;
v___x_2475_ = lean_uint32_dec_eq(v___x_2473_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
lean_dec(v_searcher_2463_);
v___x_2476_ = lean_string_utf8_next_fast(v_str_2467_, v___x_2472_);
lean_dec(v___x_2472_);
v___x_2477_ = lean_nat_sub(v___x_2476_, v_startInclusive_2468_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 1, v___x_2477_);
v___x_2479_ = v___x_2465_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_currPos_2462_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; 
v___x_2480_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2449_, v___x_2450_, v___x_2451_, v___x_2479_, v_b_2453_);
return v___x_2480_;
}
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_slice_2485_; lean_object* v_nextIt_2487_; 
v___x_2482_ = lean_string_utf8_next_fast(v_str_2467_, v___x_2472_);
v___x_2483_ = lean_nat_sub(v___x_2482_, v___x_2472_);
lean_dec(v___x_2472_);
v___x_2484_ = lean_nat_add(v_searcher_2463_, v___x_2483_);
lean_dec(v___x_2483_);
v_slice_2485_ = l_String_Slice_subslice_x21(v___x_2450_, v_currPos_2462_, v_searcher_2463_);
lean_inc(v___x_2484_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 1, v___x_2484_);
lean_ctor_set(v___x_2465_, 0, v___x_2484_);
v_nextIt_2487_ = v___x_2465_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2484_);
v_nextIt_2487_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v_startInclusive_2488_; lean_object* v_endExclusive_2489_; 
v_startInclusive_2488_ = lean_ctor_get(v_slice_2485_, 0);
lean_inc(v_startInclusive_2488_);
v_endExclusive_2489_ = lean_ctor_get(v_slice_2485_, 1);
lean_inc(v_endExclusive_2489_);
lean_dec_ref(v_slice_2485_);
v_it_2455_ = v_nextIt_2487_;
v_startInclusive_2456_ = v_startInclusive_2488_;
v_endExclusive_2457_ = v_endExclusive_2489_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v___x_2491_; 
lean_del_object(v___x_2465_);
lean_dec(v_searcher_2463_);
v___x_2491_ = lean_box(1);
lean_inc(v___x_2451_);
v_it_2455_ = v___x_2491_;
v_startInclusive_2456_ = v_currPos_2462_;
v_endExclusive_2457_ = v___x_2451_;
goto v___jp_2454_;
}
}
}
else
{
lean_dec(v___x_2451_);
lean_dec_ref(v___x_2449_);
return v_b_2453_;
}
v___jp_2454_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
lean_inc_ref(v___x_2449_);
v___x_2458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2449_);
lean_ctor_set(v___x_2458_, 1, v_startInclusive_2456_);
lean_ctor_set(v___x_2458_, 2, v_endExclusive_2457_);
v___x_2459_ = l_String_Slice_toString(v___x_2458_);
lean_dec_ref_known(v___x_2458_, 3);
v___x_2460_ = lean_array_push(v_b_2453_, v___x_2459_);
v___x_2461_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2449_, v___x_2450_, v___x_2451_, v_it_2455_, v___x_2460_);
return v___x_2461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2493_, lean_object* v___x_2494_, lean_object* v___x_2495_, lean_object* v_a_2496_, lean_object* v_b_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2493_, v___x_2494_, v___x_2495_, v_a_2496_, v_b_2497_);
lean_dec_ref(v___x_2494_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v___x_2502_; lean_object* v_infoState_2503_; uint8_t v_enabled_2504_; 
v___x_2502_ = lean_st_ref_get(v___y_2500_);
v_infoState_2503_ = lean_ctor_get(v___x_2502_, 8);
lean_inc_ref(v_infoState_2503_);
lean_dec(v___x_2502_);
v_enabled_2504_ = lean_ctor_get_uint8(v_infoState_2503_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2503_);
if (v_enabled_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec_ref(v_t_2499_);
v___x_2505_ = lean_box(0);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; lean_object* v_infoState_2508_; lean_object* v_env_2509_; lean_object* v_messages_2510_; lean_object* v_scopes_2511_; lean_object* v_usedQuotCtxts_2512_; lean_object* v_nextMacroScope_2513_; lean_object* v_maxRecDepth_2514_; lean_object* v_ngen_2515_; lean_object* v_auxDeclNGen_2516_; lean_object* v_traceState_2517_; lean_object* v_snapshotTasks_2518_; lean_object* v_prevLinterStates_2519_; lean_object* v_codeQualityEntryTasks_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2542_; 
v___x_2507_ = lean_st_ref_take(v___y_2500_);
v_infoState_2508_ = lean_ctor_get(v___x_2507_, 8);
v_env_2509_ = lean_ctor_get(v___x_2507_, 0);
v_messages_2510_ = lean_ctor_get(v___x_2507_, 1);
v_scopes_2511_ = lean_ctor_get(v___x_2507_, 2);
v_usedQuotCtxts_2512_ = lean_ctor_get(v___x_2507_, 3);
v_nextMacroScope_2513_ = lean_ctor_get(v___x_2507_, 4);
v_maxRecDepth_2514_ = lean_ctor_get(v___x_2507_, 5);
v_ngen_2515_ = lean_ctor_get(v___x_2507_, 6);
v_auxDeclNGen_2516_ = lean_ctor_get(v___x_2507_, 7);
v_traceState_2517_ = lean_ctor_get(v___x_2507_, 9);
v_snapshotTasks_2518_ = lean_ctor_get(v___x_2507_, 10);
v_prevLinterStates_2519_ = lean_ctor_get(v___x_2507_, 11);
v_codeQualityEntryTasks_2520_ = lean_ctor_get(v___x_2507_, 12);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2522_ = v___x_2507_;
v_isShared_2523_ = v_isSharedCheck_2542_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2520_);
lean_inc(v_prevLinterStates_2519_);
lean_inc(v_snapshotTasks_2518_);
lean_inc(v_traceState_2517_);
lean_inc(v_infoState_2508_);
lean_inc(v_auxDeclNGen_2516_);
lean_inc(v_ngen_2515_);
lean_inc(v_maxRecDepth_2514_);
lean_inc(v_nextMacroScope_2513_);
lean_inc(v_usedQuotCtxts_2512_);
lean_inc(v_scopes_2511_);
lean_inc(v_messages_2510_);
lean_inc(v_env_2509_);
lean_dec(v___x_2507_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2542_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
uint8_t v_enabled_2524_; lean_object* v_assignment_2525_; lean_object* v_lazyAssignment_2526_; lean_object* v_trees_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2541_; 
v_enabled_2524_ = lean_ctor_get_uint8(v_infoState_2508_, sizeof(void*)*3);
v_assignment_2525_ = lean_ctor_get(v_infoState_2508_, 0);
v_lazyAssignment_2526_ = lean_ctor_get(v_infoState_2508_, 1);
v_trees_2527_ = lean_ctor_get(v_infoState_2508_, 2);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_infoState_2508_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2529_ = v_infoState_2508_;
v_isShared_2530_ = v_isSharedCheck_2541_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_trees_2527_);
lean_inc(v_lazyAssignment_2526_);
lean_inc(v_assignment_2525_);
lean_dec(v_infoState_2508_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2541_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2531_ = lean_box(0);
v___x_2532_ = l_Lean_PersistentArray_push___redArg(v_trees_2527_, v_t_2499_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 2, v___x_2532_);
v___x_2534_ = v___x_2529_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_assignment_2525_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_lazyAssignment_2526_);
lean_ctor_set(v_reuseFailAlloc_2540_, 2, v___x_2532_);
lean_ctor_set_uint8(v_reuseFailAlloc_2540_, sizeof(void*)*3, v_enabled_2524_);
v___x_2534_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2536_; 
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 8, v___x_2534_);
v___x_2536_ = v___x_2522_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_env_2509_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_messages_2510_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_scopes_2511_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_usedQuotCtxts_2512_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v_nextMacroScope_2513_);
lean_ctor_set(v_reuseFailAlloc_2539_, 5, v_maxRecDepth_2514_);
lean_ctor_set(v_reuseFailAlloc_2539_, 6, v_ngen_2515_);
lean_ctor_set(v_reuseFailAlloc_2539_, 7, v_auxDeclNGen_2516_);
lean_ctor_set(v_reuseFailAlloc_2539_, 8, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2539_, 9, v_traceState_2517_);
lean_ctor_set(v_reuseFailAlloc_2539_, 10, v_snapshotTasks_2518_);
lean_ctor_set(v_reuseFailAlloc_2539_, 11, v_prevLinterStates_2519_);
lean_ctor_set(v_reuseFailAlloc_2539_, 12, v_codeQualityEntryTasks_2520_);
v___x_2536_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_st_ref_put(v___y_2500_, v___x_2536_);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2531_);
return v___x_2538_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2543_, v___y_2544_);
lean_dec(v___y_2544_);
return v_res_2546_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = lean_unsigned_to_nat(32u);
v___x_2548_ = lean_mk_empty_array_with_capacity(v___x_2547_);
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2550_ = ((size_t)5ULL);
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = lean_unsigned_to_nat(32u);
v___x_2553_ = lean_mk_empty_array_with_capacity(v___x_2552_);
v___x_2554_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2555_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v___x_2553_);
lean_ctor_set(v___x_2555_, 2, v___x_2551_);
lean_ctor_set(v___x_2555_, 3, v___x_2551_);
lean_ctor_set_usize(v___x_2555_, 4, v___x_2550_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; lean_object* v_infoState_2561_; uint8_t v_enabled_2562_; 
v___x_2560_ = lean_st_ref_get(v___y_2558_);
v_infoState_2561_ = lean_ctor_get(v___x_2560_, 8);
lean_inc_ref(v_infoState_2561_);
lean_dec(v___x_2560_);
v_enabled_2562_ = lean_ctor_get_uint8(v_infoState_2561_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2561_);
if (v_enabled_2562_ == 0)
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_dec_ref(v_t_2556_);
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
return v___x_2564_;
}
else
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2566_, 0, v_t_2556_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2566_, v___y_2558_);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v___x_2573_, lean_object* v_edited_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_fst_2577_; lean_object* v_snd_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2602_; 
v_fst_2577_ = lean_ctor_get(v_a_2576_, 0);
v_snd_2578_ = lean_ctor_get(v_a_2576_, 1);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_a_2576_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2580_ = v_a_2576_;
v_isShared_2581_ = v_isSharedCheck_2602_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_snd_2578_);
lean_inc(v_fst_2577_);
lean_dec(v_a_2576_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2602_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
uint8_t v___x_2582_; 
v___x_2582_ = lean_nat_dec_lt(v_snd_2578_, v___x_2573_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2584_; 
if (v_isShared_2581_ == 0)
{
v___x_2584_ = v___x_2580_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_fst_2577_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_snd_2578_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2586_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2587_ = lean_array_get_borrowed(v___x_2586_, v_edited_2574_, v_snd_2578_);
v___x_2588_ = lean_string_dec_eq(v___x_2587_, v_a_2575_);
if (v___x_2588_ == 0)
{
uint8_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2589_ = 0;
v___x_2590_ = lean_box(v___x_2589_);
lean_inc(v___x_2587_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 1, v___x_2587_);
lean_ctor_set(v___x_2580_, 0, v___x_2590_);
v___x_2592_ = v___x_2580_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2587_);
v___x_2592_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2593_ = lean_array_push(v_fst_2577_, v___x_2592_);
v___x_2594_ = lean_unsigned_to_nat(1u);
v___x_2595_ = lean_nat_add(v_snd_2578_, v___x_2594_);
lean_dec(v_snd_2578_);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2593_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v_a_2576_ = v___x_2596_;
goto _start;
}
}
else
{
lean_object* v___x_2600_; 
if (v_isShared_2581_ == 0)
{
v___x_2600_ = v___x_2580_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_fst_2577_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_snd_2578_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v___x_2603_, lean_object* v_edited_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2603_, v_edited_2604_, v_a_2605_, v_a_2606_);
lean_dec_ref(v_a_2605_);
lean_dec_ref(v_edited_2604_);
lean_dec(v___x_2603_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(lean_object* v___x_2608_, lean_object* v_original_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_fst_2612_; lean_object* v_snd_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2637_; 
v_fst_2612_ = lean_ctor_get(v_a_2611_, 0);
v_snd_2613_ = lean_ctor_get(v_a_2611_, 1);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_a_2611_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2615_ = v_a_2611_;
v_isShared_2616_ = v_isSharedCheck_2637_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_snd_2613_);
lean_inc(v_fst_2612_);
lean_dec(v_a_2611_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2637_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
uint8_t v___x_2617_; 
v___x_2617_ = lean_nat_dec_lt(v_snd_2613_, v___x_2608_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2619_; 
if (v_isShared_2616_ == 0)
{
v___x_2619_ = v___x_2615_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_fst_2612_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_snd_2613_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2621_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2622_ = lean_array_get_borrowed(v___x_2621_, v_original_2609_, v_snd_2613_);
v___x_2623_ = lean_string_dec_eq(v___x_2622_, v_a_2610_);
if (v___x_2623_ == 0)
{
uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2624_ = 1;
v___x_2625_ = lean_box(v___x_2624_);
lean_inc(v___x_2622_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 1, v___x_2622_);
lean_ctor_set(v___x_2615_, 0, v___x_2625_);
v___x_2627_ = v___x_2615_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v___x_2622_);
v___x_2627_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2628_ = lean_array_push(v_fst_2612_, v___x_2627_);
v___x_2629_ = lean_unsigned_to_nat(1u);
v___x_2630_ = lean_nat_add(v_snd_2613_, v___x_2629_);
lean_dec(v_snd_2613_);
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2628_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v_a_2611_ = v___x_2631_;
goto _start;
}
}
else
{
lean_object* v___x_2635_; 
if (v_isShared_2616_ == 0)
{
v___x_2635_ = v___x_2615_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_fst_2612_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_snd_2613_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg___boxed(lean_object* v___x_2638_, lean_object* v_original_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2638_, v_original_2639_, v_a_2640_, v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec_ref(v_original_2639_);
lean_dec(v___x_2638_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v___x_2643_, lean_object* v_original_2644_, lean_object* v___x_2645_, lean_object* v_edited_2646_, lean_object* v_as_2647_, size_t v_sz_2648_, size_t v_i_2649_, lean_object* v_b_2650_){
_start:
{
uint8_t v___x_2651_; 
v___x_2651_ = lean_usize_dec_lt(v_i_2649_, v_sz_2648_);
if (v___x_2651_ == 0)
{
return v_b_2650_;
}
else
{
lean_object* v_snd_2652_; lean_object* v_fst_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2700_; 
v_snd_2652_ = lean_ctor_get(v_b_2650_, 1);
v_fst_2653_ = lean_ctor_get(v_b_2650_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_b_2650_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2655_ = v_b_2650_;
v_isShared_2656_ = v_isSharedCheck_2700_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_snd_2652_);
lean_inc(v_fst_2653_);
lean_dec(v_b_2650_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2700_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_fst_2657_; lean_object* v_snd_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2699_; 
v_fst_2657_ = lean_ctor_get(v_snd_2652_, 0);
v_snd_2658_ = lean_ctor_get(v_snd_2652_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_snd_2652_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2660_ = v_snd_2652_;
v_isShared_2661_ = v_isSharedCheck_2699_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2658_);
lean_inc(v_fst_2657_);
lean_dec(v_snd_2652_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2699_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v_a_2662_; lean_object* v___x_2664_; 
v_a_2662_ = lean_array_uget_borrowed(v_as_2647_, v_i_2649_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v_fst_2657_);
lean_ctor_set(v___x_2660_, 0, v_fst_2653_);
v___x_2664_ = v___x_2660_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_fst_2653_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_fst_2657_);
v___x_2664_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v_fst_2666_; lean_object* v_snd_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2697_; 
v___x_2665_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2643_, v_original_2644_, v_a_2662_, v___x_2664_);
v_fst_2666_ = lean_ctor_get(v___x_2665_, 0);
v_snd_2667_ = lean_ctor_get(v___x_2665_, 1);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2669_ = v___x_2665_;
v_isShared_2670_ = v_isSharedCheck_2697_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_snd_2667_);
lean_inc(v_fst_2666_);
lean_dec(v___x_2665_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2697_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 1, v_snd_2658_);
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_fst_2666_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_snd_2658_);
v___x_2672_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; lean_object* v_fst_2674_; lean_object* v_snd_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2695_; 
v___x_2673_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2645_, v_edited_2646_, v_a_2662_, v___x_2672_);
v_fst_2674_ = lean_ctor_get(v___x_2673_, 0);
v_snd_2675_ = lean_ctor_get(v___x_2673_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2677_ = v___x_2673_;
v_isShared_2678_ = v_isSharedCheck_2695_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_snd_2675_);
lean_inc(v_fst_2674_);
lean_dec(v___x_2673_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2695_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
uint8_t v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2679_ = 2;
v___x_2680_ = lean_box(v___x_2679_);
lean_inc(v_a_2662_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 1, v_a_2662_);
lean_ctor_set(v___x_2677_, 0, v___x_2680_);
v___x_2682_ = v___x_2677_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_a_2662_);
v___x_2682_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2683_ = lean_array_push(v_fst_2674_, v___x_2682_);
v___x_2684_ = lean_unsigned_to_nat(1u);
v___x_2685_ = lean_nat_add(v_snd_2667_, v___x_2684_);
lean_dec(v_snd_2667_);
v___x_2686_ = lean_nat_add(v_snd_2675_, v___x_2684_);
lean_dec(v_snd_2675_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___x_2686_);
lean_ctor_set(v___x_2655_, 0, v___x_2685_);
v___x_2688_ = v___x_2655_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; size_t v___x_2690_; size_t v___x_2691_; 
v___x_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2683_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = ((size_t)1ULL);
v___x_2691_ = lean_usize_add(v_i_2649_, v___x_2690_);
v_i_2649_ = v___x_2691_;
v_b_2650_ = v___x_2689_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v___x_2701_, lean_object* v_original_2702_, lean_object* v___x_2703_, lean_object* v_edited_2704_, lean_object* v_as_2705_, lean_object* v_sz_2706_, lean_object* v_i_2707_, lean_object* v_b_2708_){
_start:
{
size_t v_sz_boxed_2709_; size_t v_i_boxed_2710_; lean_object* v_res_2711_; 
v_sz_boxed_2709_ = lean_unbox_usize(v_sz_2706_);
lean_dec(v_sz_2706_);
v_i_boxed_2710_ = lean_unbox_usize(v_i_2707_);
lean_dec(v_i_2707_);
v_res_2711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2701_, v_original_2702_, v___x_2703_, v_edited_2704_, v_as_2705_, v_sz_boxed_2709_, v_i_boxed_2710_, v_b_2708_);
lean_dec_ref(v_as_2705_);
lean_dec_ref(v_edited_2704_);
lean_dec(v___x_2703_);
lean_dec_ref(v_original_2702_);
lean_dec(v___x_2701_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v___x_2712_, lean_object* v_edited_2713_, lean_object* v___x_2714_, lean_object* v_original_2715_, lean_object* v_as_2716_, size_t v_sz_2717_, size_t v_i_2718_, lean_object* v_b_2719_){
_start:
{
uint8_t v___x_2720_; 
v___x_2720_ = lean_usize_dec_lt(v_i_2718_, v_sz_2717_);
if (v___x_2720_ == 0)
{
return v_b_2719_;
}
else
{
lean_object* v_snd_2721_; lean_object* v_fst_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2769_; 
v_snd_2721_ = lean_ctor_get(v_b_2719_, 1);
v_fst_2722_ = lean_ctor_get(v_b_2719_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_b_2719_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2724_ = v_b_2719_;
v_isShared_2725_ = v_isSharedCheck_2769_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_snd_2721_);
lean_inc(v_fst_2722_);
lean_dec(v_b_2719_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2769_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_fst_2726_; lean_object* v_snd_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2768_; 
v_fst_2726_ = lean_ctor_get(v_snd_2721_, 0);
v_snd_2727_ = lean_ctor_get(v_snd_2721_, 1);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_snd_2721_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2729_ = v_snd_2721_;
v_isShared_2730_ = v_isSharedCheck_2768_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_snd_2727_);
lean_inc(v_fst_2726_);
lean_dec(v_snd_2721_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2768_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v_a_2731_; lean_object* v___x_2733_; 
v_a_2731_ = lean_array_uget_borrowed(v_as_2716_, v_i_2718_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 1, v_fst_2726_);
lean_ctor_set(v___x_2729_, 0, v_fst_2722_);
v___x_2733_ = v___x_2729_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_fst_2722_);
lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_fst_2726_);
v___x_2733_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2734_; lean_object* v_fst_2735_; lean_object* v_snd_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2766_; 
v___x_2734_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2714_, v_original_2715_, v_a_2731_, v___x_2733_);
v_fst_2735_ = lean_ctor_get(v___x_2734_, 0);
v_snd_2736_ = lean_ctor_get(v___x_2734_, 1);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2738_ = v___x_2734_;
v_isShared_2739_ = v_isSharedCheck_2766_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_snd_2736_);
lean_inc(v_fst_2735_);
lean_dec(v___x_2734_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2766_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 1, v_snd_2727_);
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_fst_2735_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_snd_2727_);
v___x_2741_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
lean_object* v___x_2742_; lean_object* v_fst_2743_; lean_object* v_snd_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2764_; 
v___x_2742_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2712_, v_edited_2713_, v_a_2731_, v___x_2741_);
v_fst_2743_ = lean_ctor_get(v___x_2742_, 0);
v_snd_2744_ = lean_ctor_get(v___x_2742_, 1);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2746_ = v___x_2742_;
v_isShared_2747_ = v_isSharedCheck_2764_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_snd_2744_);
lean_inc(v_fst_2743_);
lean_dec(v___x_2742_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2764_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2748_ = 2;
v___x_2749_ = lean_box(v___x_2748_);
lean_inc(v_a_2731_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 1, v_a_2731_);
lean_ctor_set(v___x_2746_, 0, v___x_2749_);
v___x_2751_ = v___x_2746_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_a_2731_);
v___x_2751_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2752_ = lean_array_push(v_fst_2743_, v___x_2751_);
v___x_2753_ = lean_unsigned_to_nat(1u);
v___x_2754_ = lean_nat_add(v_snd_2736_, v___x_2753_);
lean_dec(v_snd_2736_);
v___x_2755_ = lean_nat_add(v_snd_2744_, v___x_2753_);
lean_dec(v_snd_2744_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 1, v___x_2755_);
lean_ctor_set(v___x_2724_, 0, v___x_2754_);
v___x_2757_ = v___x_2724_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2758_; size_t v___x_2759_; size_t v___x_2760_; lean_object* v___x_2761_; 
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2752_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = ((size_t)1ULL);
v___x_2760_ = lean_usize_add(v_i_2718_, v___x_2759_);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2714_, v_original_2715_, v___x_2712_, v_edited_2713_, v_as_2716_, v_sz_2717_, v___x_2760_, v___x_2758_);
return v___x_2761_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v___x_2770_, lean_object* v_edited_2771_, lean_object* v___x_2772_, lean_object* v_original_2773_, lean_object* v_as_2774_, lean_object* v_sz_2775_, lean_object* v_i_2776_, lean_object* v_b_2777_){
_start:
{
size_t v_sz_boxed_2778_; size_t v_i_boxed_2779_; lean_object* v_res_2780_; 
v_sz_boxed_2778_ = lean_unbox_usize(v_sz_2775_);
lean_dec(v_sz_2775_);
v_i_boxed_2779_ = lean_unbox_usize(v_i_2776_);
lean_dec(v_i_2776_);
v_res_2780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_2770_, v_edited_2771_, v___x_2772_, v_original_2773_, v_as_2774_, v_sz_boxed_2778_, v_i_boxed_2779_, v_b_2777_);
lean_dec_ref(v_as_2774_);
lean_dec_ref(v_original_2773_);
lean_dec(v___x_2772_);
lean_dec_ref(v_edited_2771_);
lean_dec(v___x_2770_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_2781_, lean_object* v_original_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_fst_2784_; lean_object* v_snd_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2804_; 
v_fst_2784_ = lean_ctor_get(v_a_2783_, 0);
v_snd_2785_ = lean_ctor_get(v_a_2783_, 1);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_a_2783_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2787_ = v_a_2783_;
v_isShared_2788_ = v_isSharedCheck_2804_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_snd_2785_);
lean_inc(v_fst_2784_);
lean_dec(v_a_2783_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2804_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
uint8_t v___x_2789_; 
v___x_2789_ = lean_nat_dec_lt(v_snd_2785_, v___x_2781_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2791_; 
if (v_isShared_2788_ == 0)
{
v___x_2791_ = v___x_2787_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_fst_2784_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_snd_2785_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
else
{
uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2793_ = 1;
v___x_2794_ = lean_array_fget_borrowed(v_original_2782_, v_snd_2785_);
v___x_2795_ = lean_box(v___x_2793_);
lean_inc(v___x_2794_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 1, v___x_2794_);
lean_ctor_set(v___x_2787_, 0, v___x_2795_);
v___x_2797_ = v___x_2787_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v___x_2794_);
v___x_2797_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2798_ = lean_array_push(v_fst_2784_, v___x_2797_);
v___x_2799_ = lean_unsigned_to_nat(1u);
v___x_2800_ = lean_nat_add(v_snd_2785_, v___x_2799_);
lean_dec(v_snd_2785_);
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2798_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v_a_2783_ = v___x_2801_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_2805_, lean_object* v_original_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_2805_, v_original_2806_, v_a_2807_);
lean_dec_ref(v_original_2806_);
lean_dec(v___x_2805_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_2809_, size_t v_i_2810_, lean_object* v_bs_2811_){
_start:
{
uint8_t v___x_2812_; 
v___x_2812_ = lean_usize_dec_lt(v_i_2810_, v_sz_2809_);
if (v___x_2812_ == 0)
{
return v_bs_2811_;
}
else
{
lean_object* v_v_2813_; lean_object* v___x_2814_; lean_object* v_bs_x27_2815_; uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; size_t v___x_2819_; size_t v___x_2820_; lean_object* v___x_2821_; 
v_v_2813_ = lean_array_uget(v_bs_2811_, v_i_2810_);
v___x_2814_ = lean_unsigned_to_nat(0u);
v_bs_x27_2815_ = lean_array_uset(v_bs_2811_, v_i_2810_, v___x_2814_);
v___x_2816_ = 0;
v___x_2817_ = lean_box(v___x_2816_);
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
lean_ctor_set(v___x_2818_, 1, v_v_2813_);
v___x_2819_ = ((size_t)1ULL);
v___x_2820_ = lean_usize_add(v_i_2810_, v___x_2819_);
v___x_2821_ = lean_array_uset(v_bs_x27_2815_, v_i_2810_, v___x_2818_);
v_i_2810_ = v___x_2820_;
v_bs_2811_ = v___x_2821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_2823_, lean_object* v_i_2824_, lean_object* v_bs_2825_){
_start:
{
size_t v_sz_boxed_2826_; size_t v_i_boxed_2827_; lean_object* v_res_2828_; 
v_sz_boxed_2826_ = lean_unbox_usize(v_sz_2823_);
lean_dec(v_sz_2823_);
v_i_boxed_2827_ = lean_unbox_usize(v_i_2824_);
lean_dec(v_i_2824_);
v_res_2828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_2826_, v_i_boxed_2827_, v_bs_2825_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_2829_, lean_object* v_edited_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_fst_2832_; lean_object* v_snd_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2852_; 
v_fst_2832_ = lean_ctor_get(v_a_2831_, 0);
v_snd_2833_ = lean_ctor_get(v_a_2831_, 1);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_a_2831_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2835_ = v_a_2831_;
v_isShared_2836_ = v_isSharedCheck_2852_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_snd_2833_);
lean_inc(v_fst_2832_);
lean_dec(v_a_2831_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2852_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
uint8_t v___x_2837_; 
v___x_2837_ = lean_nat_dec_lt(v_snd_2833_, v___x_2829_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2839_; 
if (v_isShared_2836_ == 0)
{
v___x_2839_ = v___x_2835_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_fst_2832_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_snd_2833_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
else
{
uint8_t v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2841_ = 0;
v___x_2842_ = lean_array_fget_borrowed(v_edited_2830_, v_snd_2833_);
v___x_2843_ = lean_box(v___x_2841_);
lean_inc(v___x_2842_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 1, v___x_2842_);
lean_ctor_set(v___x_2835_, 0, v___x_2843_);
v___x_2845_ = v___x_2835_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v___x_2842_);
v___x_2845_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2846_ = lean_array_push(v_fst_2832_, v___x_2845_);
v___x_2847_ = lean_unsigned_to_nat(1u);
v___x_2848_ = lean_nat_add(v_snd_2833_, v___x_2847_);
lean_dec(v_snd_2833_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2846_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v_a_2831_ = v___x_2849_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_2853_, lean_object* v_edited_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_2853_, v_edited_2854_, v_a_2855_);
lean_dec_ref(v_edited_2854_);
lean_dec(v___x_2853_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(lean_object* v_x_2857_, lean_object* v_x_2858_){
_start:
{
if (lean_obj_tag(v_x_2858_) == 0)
{
lean_inc(v_x_2857_);
return v_x_2857_;
}
else
{
lean_object* v_key_2859_; lean_object* v_value_2860_; lean_object* v_tail_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_key_2859_ = lean_ctor_get(v_x_2858_, 0);
v_value_2860_ = lean_ctor_get(v_x_2858_, 1);
v_tail_2861_ = lean_ctor_get(v_x_2858_, 2);
v___x_2862_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2857_, v_tail_2861_);
lean_inc(v_value_2860_);
lean_inc(v_key_2859_);
v___x_2863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2863_, 0, v_key_2859_);
lean_ctor_set(v___x_2863_, 1, v_value_2860_);
v___x_2864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set(v___x_2864_, 1, v___x_2862_);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17___boxed(lean_object* v_x_2865_, lean_object* v_x_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2865_, v_x_2866_);
lean_dec(v_x_2866_);
lean_dec(v_x_2865_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(lean_object* v_as_2868_, size_t v_i_2869_, size_t v_stop_2870_, lean_object* v_b_2871_){
_start:
{
uint8_t v___x_2872_; 
v___x_2872_ = lean_usize_dec_eq(v_i_2869_, v_stop_2870_);
if (v___x_2872_ == 0)
{
size_t v___x_2873_; size_t v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2873_ = ((size_t)1ULL);
v___x_2874_ = lean_usize_sub(v_i_2869_, v___x_2873_);
v___x_2875_ = lean_array_uget_borrowed(v_as_2868_, v___x_2874_);
v___x_2876_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_b_2871_, v___x_2875_);
lean_dec(v_b_2871_);
v_i_2869_ = v___x_2874_;
v_b_2871_ = v___x_2876_;
goto _start;
}
else
{
return v_b_2871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18___boxed(lean_object* v_as_2878_, lean_object* v_i_2879_, lean_object* v_stop_2880_, lean_object* v_b_2881_){
_start:
{
size_t v_i_boxed_2882_; size_t v_stop_boxed_2883_; lean_object* v_res_2884_; 
v_i_boxed_2882_ = lean_unbox_usize(v_i_2879_);
lean_dec(v_i_2879_);
v_stop_boxed_2883_ = lean_unbox_usize(v_stop_2880_);
lean_dec(v_stop_2880_);
v_res_2884_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_as_2878_, v_i_boxed_2882_, v_stop_boxed_2883_, v_b_2881_);
lean_dec_ref(v_as_2878_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(lean_object* v_left_2885_, lean_object* v_right_2886_, lean_object* v_pref_2887_){
_start:
{
lean_object* v_start_2888_; lean_object* v_stop_2889_; lean_object* v_i_2890_; lean_object* v___x_2896_; uint8_t v___x_2897_; 
v_start_2888_ = lean_ctor_get(v_left_2885_, 1);
v_stop_2889_ = lean_ctor_get(v_left_2885_, 2);
v_i_2890_ = lean_array_get_size(v_pref_2887_);
v___x_2896_ = lean_nat_sub(v_stop_2889_, v_start_2888_);
v___x_2897_ = lean_nat_dec_lt(v_i_2890_, v___x_2896_);
lean_dec(v___x_2896_);
if (v___x_2897_ == 0)
{
goto v___jp_2891_;
}
else
{
lean_object* v_start_2898_; lean_object* v_stop_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; 
v_start_2898_ = lean_ctor_get(v_right_2886_, 1);
v_stop_2899_ = lean_ctor_get(v_right_2886_, 2);
v___x_2900_ = lean_nat_sub(v_stop_2899_, v_start_2898_);
v___x_2901_ = lean_nat_dec_lt(v_i_2890_, v___x_2900_);
lean_dec(v___x_2900_);
if (v___x_2901_ == 0)
{
goto v___jp_2891_;
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; 
v___x_2902_ = l_Subarray_get___redArg(v_left_2885_, v_i_2890_);
v___x_2903_ = l_Subarray_get___redArg(v_right_2886_, v_i_2890_);
v___x_2904_ = lean_string_dec_eq(v___x_2902_, v___x_2903_);
lean_dec(v___x_2903_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
lean_dec(v___x_2902_);
v___x_2905_ = l_Subarray_drop___redArg(v_left_2885_, v_i_2890_);
v___x_2906_ = l_Subarray_drop___redArg(v_right_2886_, v_i_2890_);
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_pref_2887_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
return v___x_2908_;
}
else
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_array_push(v_pref_2887_, v___x_2902_);
v_pref_2887_ = v___x_2909_;
goto _start;
}
}
}
v___jp_2891_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2892_ = l_Subarray_drop___redArg(v_left_2885_, v_i_2890_);
v___x_2893_ = l_Subarray_drop___redArg(v_right_2886_, v_i_2890_);
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v_pref_2887_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(lean_object* v_left_2913_, lean_object* v_right_2914_){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_2916_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(v_left_2913_, v_right_2914_, v___x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(lean_object* v_a_2917_, lean_object* v_b_2918_, lean_object* v_x_2919_){
_start:
{
if (lean_obj_tag(v_x_2919_) == 0)
{
lean_dec(v_b_2918_);
lean_dec_ref(v_a_2917_);
return v_x_2919_;
}
else
{
lean_object* v_key_2920_; lean_object* v_value_2921_; lean_object* v_tail_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2934_; 
v_key_2920_ = lean_ctor_get(v_x_2919_, 0);
v_value_2921_ = lean_ctor_get(v_x_2919_, 1);
v_tail_2922_ = lean_ctor_get(v_x_2919_, 2);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_x_2919_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2924_ = v_x_2919_;
v_isShared_2925_ = v_isSharedCheck_2934_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_tail_2922_);
lean_inc(v_value_2921_);
lean_inc(v_key_2920_);
lean_dec(v_x_2919_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2934_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
uint8_t v___x_2926_; 
v___x_2926_ = lean_string_dec_eq(v_key_2920_, v_a_2917_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2927_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_2917_, v_b_2918_, v_tail_2922_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 2, v___x_2927_);
v___x_2929_ = v___x_2924_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_key_2920_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_value_2921_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
else
{
lean_object* v___x_2932_; 
lean_dec(v_value_2921_);
lean_dec(v_key_2920_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 1, v_b_2918_);
lean_ctor_set(v___x_2924_, 0, v_a_2917_);
v___x_2932_ = v___x_2924_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2917_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_b_2918_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v_tail_2922_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2935_, lean_object* v_x_2936_){
_start:
{
if (lean_obj_tag(v_x_2936_) == 0)
{
return v_x_2935_;
}
else
{
lean_object* v_key_2937_; lean_object* v_value_2938_; lean_object* v_tail_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2962_; 
v_key_2937_ = lean_ctor_get(v_x_2936_, 0);
v_value_2938_ = lean_ctor_get(v_x_2936_, 1);
v_tail_2939_ = lean_ctor_get(v_x_2936_, 2);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_x_2936_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2941_ = v_x_2936_;
v_isShared_2942_ = v_isSharedCheck_2962_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_tail_2939_);
lean_inc(v_value_2938_);
lean_inc(v_key_2937_);
lean_dec(v_x_2936_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2962_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; uint64_t v___x_2944_; uint64_t v___x_2945_; uint64_t v___x_2946_; uint64_t v_fold_2947_; uint64_t v___x_2948_; uint64_t v___x_2949_; uint64_t v___x_2950_; size_t v___x_2951_; size_t v___x_2952_; size_t v___x_2953_; size_t v___x_2954_; size_t v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2943_ = lean_array_get_size(v_x_2935_);
v___x_2944_ = lean_string_hash(v_key_2937_);
v___x_2945_ = 32ULL;
v___x_2946_ = lean_uint64_shift_right(v___x_2944_, v___x_2945_);
v_fold_2947_ = lean_uint64_xor(v___x_2944_, v___x_2946_);
v___x_2948_ = 16ULL;
v___x_2949_ = lean_uint64_shift_right(v_fold_2947_, v___x_2948_);
v___x_2950_ = lean_uint64_xor(v_fold_2947_, v___x_2949_);
v___x_2951_ = lean_uint64_to_usize(v___x_2950_);
v___x_2952_ = lean_usize_of_nat(v___x_2943_);
v___x_2953_ = ((size_t)1ULL);
v___x_2954_ = lean_usize_sub(v___x_2952_, v___x_2953_);
v___x_2955_ = lean_usize_land(v___x_2951_, v___x_2954_);
v___x_2956_ = lean_array_uget_borrowed(v_x_2935_, v___x_2955_);
lean_inc(v___x_2956_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 2, v___x_2956_);
v___x_2958_ = v___x_2941_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_key_2937_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_value_2938_);
lean_ctor_set(v_reuseFailAlloc_2961_, 2, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; 
v___x_2959_ = lean_array_uset(v_x_2935_, v___x_2955_, v___x_2958_);
v_x_2935_ = v___x_2959_;
v_x_2936_ = v_tail_2939_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(lean_object* v_i_2963_, lean_object* v_source_2964_, lean_object* v_target_2965_){
_start:
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = lean_array_get_size(v_source_2964_);
v___x_2967_ = lean_nat_dec_lt(v_i_2963_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_dec_ref(v_source_2964_);
lean_dec(v_i_2963_);
return v_target_2965_;
}
else
{
lean_object* v_es_2968_; lean_object* v___x_2969_; lean_object* v_source_2970_; lean_object* v_target_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v_es_2968_ = lean_array_fget(v_source_2964_, v_i_2963_);
v___x_2969_ = lean_box(0);
v_source_2970_ = lean_array_fset(v_source_2964_, v_i_2963_, v___x_2969_);
v_target_2971_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_target_2965_, v_es_2968_);
v___x_2972_ = lean_unsigned_to_nat(1u);
v___x_2973_ = lean_nat_add(v_i_2963_, v___x_2972_);
lean_dec(v_i_2963_);
v_i_2963_ = v___x_2973_;
v_source_2964_ = v_source_2970_;
v_target_2965_ = v_target_2971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(lean_object* v_data_2975_){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v_nbuckets_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2976_ = lean_array_get_size(v_data_2975_);
v___x_2977_ = lean_unsigned_to_nat(2u);
v_nbuckets_2978_ = lean_nat_mul(v___x_2976_, v___x_2977_);
v___x_2979_ = lean_unsigned_to_nat(0u);
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_mk_array(v_nbuckets_2978_, v___x_2980_);
v___x_2982_ = lean_array_propagate_mark(v_data_2975_, v___x_2981_);
v___x_2983_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v___x_2979_, v_data_2975_, v___x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(lean_object* v_a_2984_, lean_object* v_x_2985_){
_start:
{
if (lean_obj_tag(v_x_2985_) == 0)
{
uint8_t v___x_2986_; 
v___x_2986_ = 0;
return v___x_2986_;
}
else
{
lean_object* v_key_2987_; lean_object* v_tail_2988_; uint8_t v___x_2989_; 
v_key_2987_ = lean_ctor_get(v_x_2985_, 0);
v_tail_2988_ = lean_ctor_get(v_x_2985_, 2);
v___x_2989_ = lean_string_dec_eq(v_key_2987_, v_a_2984_);
if (v___x_2989_ == 0)
{
v_x_2985_ = v_tail_2988_;
goto _start;
}
else
{
return v___x_2989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg___boxed(lean_object* v_a_2991_, lean_object* v_x_2992_){
_start:
{
uint8_t v_res_2993_; lean_object* v_r_2994_; 
v_res_2993_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_2991_, v_x_2992_);
lean_dec(v_x_2992_);
lean_dec_ref(v_a_2991_);
v_r_2994_ = lean_box(v_res_2993_);
return v_r_2994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(lean_object* v_m_2995_, lean_object* v_a_2996_, lean_object* v_b_2997_){
_start:
{
lean_object* v_size_2998_; lean_object* v_buckets_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3042_; 
v_size_2998_ = lean_ctor_get(v_m_2995_, 0);
v_buckets_2999_ = lean_ctor_get(v_m_2995_, 1);
v_isSharedCheck_3042_ = !lean_is_exclusive(v_m_2995_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3001_ = v_m_2995_;
v_isShared_3002_ = v_isSharedCheck_3042_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_buckets_2999_);
lean_inc(v_size_2998_);
lean_dec(v_m_2995_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3042_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; uint64_t v___x_3004_; uint64_t v___x_3005_; uint64_t v___x_3006_; uint64_t v_fold_3007_; uint64_t v___x_3008_; uint64_t v___x_3009_; uint64_t v___x_3010_; size_t v___x_3011_; size_t v___x_3012_; size_t v___x_3013_; size_t v___x_3014_; size_t v___x_3015_; lean_object* v_bkt_3016_; uint8_t v___x_3017_; 
v___x_3003_ = lean_array_get_size(v_buckets_2999_);
v___x_3004_ = lean_string_hash(v_a_2996_);
v___x_3005_ = 32ULL;
v___x_3006_ = lean_uint64_shift_right(v___x_3004_, v___x_3005_);
v_fold_3007_ = lean_uint64_xor(v___x_3004_, v___x_3006_);
v___x_3008_ = 16ULL;
v___x_3009_ = lean_uint64_shift_right(v_fold_3007_, v___x_3008_);
v___x_3010_ = lean_uint64_xor(v_fold_3007_, v___x_3009_);
v___x_3011_ = lean_uint64_to_usize(v___x_3010_);
v___x_3012_ = lean_usize_of_nat(v___x_3003_);
v___x_3013_ = ((size_t)1ULL);
v___x_3014_ = lean_usize_sub(v___x_3012_, v___x_3013_);
v___x_3015_ = lean_usize_land(v___x_3011_, v___x_3014_);
v_bkt_3016_ = lean_array_uget_borrowed(v_buckets_2999_, v___x_3015_);
v___x_3017_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_2996_, v_bkt_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; lean_object* v_size_x27_3019_; lean_object* v___x_3020_; lean_object* v_buckets_x27_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; 
v___x_3018_ = lean_unsigned_to_nat(1u);
v_size_x27_3019_ = lean_nat_add(v_size_2998_, v___x_3018_);
lean_dec(v_size_2998_);
lean_inc(v_bkt_3016_);
v___x_3020_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3020_, 0, v_a_2996_);
lean_ctor_set(v___x_3020_, 1, v_b_2997_);
lean_ctor_set(v___x_3020_, 2, v_bkt_3016_);
v_buckets_x27_3021_ = lean_array_uset(v_buckets_2999_, v___x_3015_, v___x_3020_);
v___x_3022_ = lean_unsigned_to_nat(4u);
v___x_3023_ = lean_nat_mul(v_size_x27_3019_, v___x_3022_);
v___x_3024_ = lean_unsigned_to_nat(3u);
v___x_3025_ = lean_nat_div(v___x_3023_, v___x_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_array_get_size(v_buckets_x27_3021_);
v___x_3027_ = lean_nat_dec_le(v___x_3025_, v___x_3026_);
lean_dec(v___x_3025_);
if (v___x_3027_ == 0)
{
lean_object* v_val_3028_; lean_object* v___x_3030_; 
v_val_3028_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_buckets_x27_3021_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v_val_3028_);
lean_ctor_set(v___x_3001_, 0, v_size_x27_3019_);
v___x_3030_ = v___x_3001_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_size_x27_3019_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_val_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
else
{
lean_object* v___x_3033_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v_buckets_x27_3021_);
lean_ctor_set(v___x_3001_, 0, v_size_x27_3019_);
v___x_3033_ = v___x_3001_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_size_x27_3019_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_buckets_x27_3021_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
else
{
lean_object* v___x_3035_; lean_object* v_buckets_x27_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_inc(v_bkt_3016_);
v___x_3035_ = lean_box(0);
v_buckets_x27_3036_ = lean_array_uset(v_buckets_2999_, v___x_3015_, v___x_3035_);
v___x_3037_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_2996_, v_b_2997_, v_bkt_3016_);
v___x_3038_ = lean_array_uset(v_buckets_x27_3036_, v___x_3015_, v___x_3037_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v___x_3038_);
v___x_3040_ = v___x_3001_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_size_2998_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(lean_object* v_a_3043_, lean_object* v_x_3044_){
_start:
{
if (lean_obj_tag(v_x_3044_) == 0)
{
lean_object* v___x_3045_; 
v___x_3045_ = lean_box(0);
return v___x_3045_;
}
else
{
lean_object* v_key_3046_; lean_object* v_value_3047_; lean_object* v_tail_3048_; uint8_t v___x_3049_; 
v_key_3046_ = lean_ctor_get(v_x_3044_, 0);
v_value_3047_ = lean_ctor_get(v_x_3044_, 1);
v_tail_3048_ = lean_ctor_get(v_x_3044_, 2);
v___x_3049_ = lean_string_dec_eq(v_key_3046_, v_a_3043_);
if (v___x_3049_ == 0)
{
v_x_3044_ = v_tail_3048_;
goto _start;
}
else
{
lean_object* v___x_3051_; 
lean_inc(v_value_3047_);
v___x_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3051_, 0, v_value_3047_);
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg___boxed(lean_object* v_a_3052_, lean_object* v_x_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3052_, v_x_3053_);
lean_dec(v_x_3053_);
lean_dec_ref(v_a_3052_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(lean_object* v_m_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_buckets_3057_; lean_object* v___x_3058_; uint64_t v___x_3059_; uint64_t v___x_3060_; uint64_t v___x_3061_; uint64_t v_fold_3062_; uint64_t v___x_3063_; uint64_t v___x_3064_; uint64_t v___x_3065_; size_t v___x_3066_; size_t v___x_3067_; size_t v___x_3068_; size_t v___x_3069_; size_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_buckets_3057_ = lean_ctor_get(v_m_3055_, 1);
v___x_3058_ = lean_array_get_size(v_buckets_3057_);
v___x_3059_ = lean_string_hash(v_a_3056_);
v___x_3060_ = 32ULL;
v___x_3061_ = lean_uint64_shift_right(v___x_3059_, v___x_3060_);
v_fold_3062_ = lean_uint64_xor(v___x_3059_, v___x_3061_);
v___x_3063_ = 16ULL;
v___x_3064_ = lean_uint64_shift_right(v_fold_3062_, v___x_3063_);
v___x_3065_ = lean_uint64_xor(v_fold_3062_, v___x_3064_);
v___x_3066_ = lean_uint64_to_usize(v___x_3065_);
v___x_3067_ = lean_usize_of_nat(v___x_3058_);
v___x_3068_ = ((size_t)1ULL);
v___x_3069_ = lean_usize_sub(v___x_3067_, v___x_3068_);
v___x_3070_ = lean_usize_land(v___x_3066_, v___x_3069_);
v___x_3071_ = lean_array_uget_borrowed(v_buckets_3057_, v___x_3070_);
v___x_3072_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3056_, v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg___boxed(lean_object* v_m_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_3073_, v_a_3074_);
lean_dec_ref(v_a_3074_);
lean_dec_ref(v_m_3073_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(lean_object* v_histogram_3076_, lean_object* v_index_3077_, lean_object* v_val_3078_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3076_, v_val_3078_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3080_ = lean_unsigned_to_nat(1u);
v___x_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3081_, 0, v_index_3077_);
v___x_3082_ = lean_unsigned_to_nat(0u);
v___x_3083_ = lean_box(0);
v___x_3084_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3080_);
lean_ctor_set(v___x_3084_, 1, v___x_3081_);
lean_ctor_set(v___x_3084_, 2, v___x_3082_);
lean_ctor_set(v___x_3084_, 3, v___x_3083_);
v___x_3085_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3076_, v_val_3078_, v___x_3084_);
return v___x_3085_;
}
else
{
lean_object* v_val_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3107_; 
v_val_3086_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3088_ = v___x_3079_;
v_isShared_3089_ = v_isSharedCheck_3107_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_val_3086_);
lean_dec(v___x_3079_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3107_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v_leftCount_3090_; lean_object* v_rightCount_3091_; lean_object* v_rightIndex_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3105_; 
v_leftCount_3090_ = lean_ctor_get(v_val_3086_, 0);
v_rightCount_3091_ = lean_ctor_get(v_val_3086_, 2);
v_rightIndex_3092_ = lean_ctor_get(v_val_3086_, 3);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_val_3086_);
if (v_isSharedCheck_3105_ == 0)
{
lean_object* v_unused_3106_; 
v_unused_3106_ = lean_ctor_get(v_val_3086_, 1);
lean_dec(v_unused_3106_);
v___x_3094_ = v_val_3086_;
v_isShared_3095_ = v_isSharedCheck_3105_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_rightIndex_3092_);
lean_inc(v_rightCount_3091_);
lean_inc(v_leftCount_3090_);
lean_dec(v_val_3086_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3105_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3096_ = lean_unsigned_to_nat(1u);
v___x_3097_ = lean_nat_add(v_leftCount_3090_, v___x_3096_);
lean_dec(v_leftCount_3090_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v_index_3077_);
v___x_3099_ = v___x_3088_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_index_3077_);
v___x_3099_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_object* v___x_3101_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 1, v___x_3099_);
lean_ctor_set(v___x_3094_, 0, v___x_3097_);
v___x_3101_ = v___x_3094_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3097_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3103_, 2, v_rightCount_3091_);
lean_ctor_set(v_reuseFailAlloc_3103_, 3, v_rightIndex_3092_);
v___x_3101_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3076_, v_val_3078_, v___x_3101_);
return v___x_3102_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(lean_object* v_upperBound_3108_, lean_object* v_fst_3109_, lean_object* v___x_3110_, lean_object* v_fst_3111_, lean_object* v_a_3112_, lean_object* v_b_3113_){
_start:
{
uint8_t v___x_3114_; 
v___x_3114_ = lean_nat_dec_lt(v_a_3112_, v_upperBound_3108_);
if (v___x_3114_ == 0)
{
lean_dec(v_a_3112_);
return v_b_3113_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3115_ = l_Subarray_get___redArg(v_fst_3111_, v_a_3112_);
lean_inc(v_a_3112_);
v___x_3116_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_b_3113_, v_a_3112_, v___x_3115_);
v___x_3117_ = lean_unsigned_to_nat(1u);
v___x_3118_ = lean_nat_add(v_a_3112_, v___x_3117_);
lean_dec(v_a_3112_);
v_a_3112_ = v___x_3118_;
v_b_3113_ = v___x_3116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_upperBound_3120_, lean_object* v_fst_3121_, lean_object* v___x_3122_, lean_object* v_fst_3123_, lean_object* v_a_3124_, lean_object* v_b_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3120_, v_fst_3121_, v___x_3122_, v_fst_3123_, v_a_3124_, v_b_3125_);
lean_dec_ref(v_fst_3123_);
lean_dec(v___x_3122_);
lean_dec_ref(v_fst_3121_);
lean_dec(v_upperBound_3120_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(lean_object* v_as_x27_3127_, lean_object* v_b_3128_){
_start:
{
if (lean_obj_tag(v_as_x27_3127_) == 0)
{
return v_b_3128_;
}
else
{
lean_object* v_head_3129_; lean_object* v_snd_3130_; lean_object* v_leftIndex_3131_; 
v_head_3129_ = lean_ctor_get(v_as_x27_3127_, 0);
v_snd_3130_ = lean_ctor_get(v_head_3129_, 1);
v_leftIndex_3131_ = lean_ctor_get(v_snd_3130_, 1);
if (lean_obj_tag(v_leftIndex_3131_) == 1)
{
lean_object* v_rightIndex_3132_; 
v_rightIndex_3132_ = lean_ctor_get(v_snd_3130_, 3);
if (lean_obj_tag(v_rightIndex_3132_) == 1)
{
if (lean_obj_tag(v_b_3128_) == 0)
{
lean_object* v_tail_3133_; lean_object* v_fst_3134_; lean_object* v_leftCount_3135_; lean_object* v_rightCount_3136_; lean_object* v_val_3137_; lean_object* v_val_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v_tail_3133_ = lean_ctor_get(v_as_x27_3127_, 1);
v_fst_3134_ = lean_ctor_get(v_head_3129_, 0);
v_leftCount_3135_ = lean_ctor_get(v_snd_3130_, 0);
v_rightCount_3136_ = lean_ctor_get(v_snd_3130_, 2);
v_val_3137_ = lean_ctor_get(v_leftIndex_3131_, 0);
v_val_3138_ = lean_ctor_get(v_rightIndex_3132_, 0);
v___x_3139_ = lean_nat_add(v_leftCount_3135_, v_rightCount_3136_);
lean_inc(v_val_3138_);
lean_inc(v_val_3137_);
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v_val_3137_);
lean_ctor_set(v___x_3140_, 1, v_val_3138_);
lean_inc(v_fst_3134_);
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v_fst_3134_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3139_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
v_as_x27_3127_ = v_tail_3133_;
v_b_3128_ = v___x_3143_;
goto _start;
}
else
{
lean_object* v_val_3145_; lean_object* v_tail_3146_; lean_object* v_fst_3147_; lean_object* v_leftCount_3148_; lean_object* v_rightCount_3149_; lean_object* v_val_3150_; lean_object* v_val_3151_; lean_object* v_fst_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3173_; 
v_val_3145_ = lean_ctor_get(v_b_3128_, 0);
lean_inc(v_val_3145_);
v_tail_3146_ = lean_ctor_get(v_as_x27_3127_, 1);
v_fst_3147_ = lean_ctor_get(v_head_3129_, 0);
v_leftCount_3148_ = lean_ctor_get(v_snd_3130_, 0);
v_rightCount_3149_ = lean_ctor_get(v_snd_3130_, 2);
v_val_3150_ = lean_ctor_get(v_leftIndex_3131_, 0);
v_val_3151_ = lean_ctor_get(v_rightIndex_3132_, 0);
v_fst_3152_ = lean_ctor_get(v_val_3145_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_val_3145_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v_val_3145_, 1);
lean_dec(v_unused_3174_);
v___x_3154_ = v_val_3145_;
v_isShared_3155_ = v_isSharedCheck_3173_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_fst_3152_);
lean_dec(v_val_3145_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3173_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3156_ = lean_nat_add(v_leftCount_3148_, v_rightCount_3149_);
v___x_3157_ = lean_nat_dec_lt(v___x_3156_, v_fst_3152_);
lean_dec(v_fst_3152_);
if (v___x_3157_ == 0)
{
lean_dec(v___x_3156_);
lean_del_object(v___x_3154_);
v_as_x27_3127_ = v_tail_3146_;
goto _start;
}
else
{
lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3171_; 
v_isSharedCheck_3171_ = !lean_is_exclusive(v_b_3128_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v_b_3128_, 0);
lean_dec(v_unused_3172_);
v___x_3160_ = v_b_3128_;
v_isShared_3161_ = v_isSharedCheck_3171_;
goto v_resetjp_3159_;
}
else
{
lean_dec(v_b_3128_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3171_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
lean_inc(v_val_3151_);
lean_inc(v_val_3150_);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 1, v_val_3151_);
lean_ctor_set(v___x_3154_, 0, v_val_3150_);
v___x_3163_ = v___x_3154_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_val_3150_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_val_3151_);
v___x_3163_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3167_; 
lean_inc(v_fst_3147_);
v___x_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3164_, 0, v_fst_3147_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3156_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3165_);
v___x_3167_ = v___x_3160_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
v_as_x27_3127_ = v_tail_3146_;
v_b_3128_ = v___x_3167_;
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
lean_object* v_tail_3175_; 
v_tail_3175_ = lean_ctor_get(v_as_x27_3127_, 1);
v_as_x27_3127_ = v_tail_3175_;
goto _start;
}
}
else
{
lean_object* v_tail_3177_; 
v_tail_3177_ = lean_ctor_get(v_as_x27_3127_, 1);
v_as_x27_3127_ = v_tail_3177_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg___boxed(lean_object* v_as_x27_3179_, lean_object* v_b_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3179_, v_b_3180_);
lean_dec(v_as_x27_3179_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(lean_object* v_histogram_3182_, lean_object* v_index_3183_, lean_object* v_val_3184_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3182_, v_val_3184_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3186_ = lean_unsigned_to_nat(0u);
v___x_3187_ = lean_box(0);
v___x_3188_ = lean_unsigned_to_nat(1u);
v___x_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3189_, 0, v_index_3183_);
v___x_3190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3186_);
lean_ctor_set(v___x_3190_, 1, v___x_3187_);
lean_ctor_set(v___x_3190_, 2, v___x_3188_);
lean_ctor_set(v___x_3190_, 3, v___x_3189_);
v___x_3191_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3182_, v_val_3184_, v___x_3190_);
return v___x_3191_;
}
else
{
lean_object* v_val_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3213_; 
v_val_3192_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3194_ = v___x_3185_;
v_isShared_3195_ = v_isSharedCheck_3213_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_val_3192_);
lean_dec(v___x_3185_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3213_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v_leftCount_3196_; lean_object* v_leftIndex_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3210_; 
v_leftCount_3196_ = lean_ctor_get(v_val_3192_, 0);
v_leftIndex_3197_ = lean_ctor_get(v_val_3192_, 1);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_val_3192_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; lean_object* v_unused_3212_; 
v_unused_3211_ = lean_ctor_get(v_val_3192_, 3);
lean_dec(v_unused_3211_);
v_unused_3212_ = lean_ctor_get(v_val_3192_, 2);
lean_dec(v_unused_3212_);
v___x_3199_ = v_val_3192_;
v_isShared_3200_ = v_isSharedCheck_3210_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_leftIndex_3197_);
lean_inc(v_leftCount_3196_);
lean_dec(v_val_3192_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3210_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3201_ = lean_unsigned_to_nat(1u);
v___x_3202_ = lean_nat_add(v_leftCount_3196_, v___x_3201_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v_index_3183_);
v___x_3204_ = v___x_3194_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_index_3183_);
v___x_3204_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3206_; 
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 3, v___x_3204_);
lean_ctor_set(v___x_3199_, 2, v___x_3202_);
v___x_3206_ = v___x_3199_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_leftCount_3196_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_leftIndex_3197_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3208_, 3, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3182_, v_val_3184_, v___x_3206_);
return v___x_3207_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(lean_object* v_upperBound_3214_, lean_object* v___x_3215_, lean_object* v_fst_3216_, lean_object* v___x_3217_, lean_object* v_a_3218_, lean_object* v_b_3219_){
_start:
{
uint8_t v___x_3220_; 
v___x_3220_ = lean_nat_dec_lt(v_a_3218_, v_upperBound_3214_);
if (v___x_3220_ == 0)
{
lean_dec(v_a_3218_);
return v_b_3219_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3221_ = l_Subarray_get___redArg(v_fst_3216_, v_a_3218_);
lean_inc(v_a_3218_);
v___x_3222_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_b_3219_, v_a_3218_, v___x_3221_);
v___x_3223_ = lean_unsigned_to_nat(1u);
v___x_3224_ = lean_nat_add(v_a_3218_, v___x_3223_);
lean_dec(v_a_3218_);
v_a_3218_ = v___x_3224_;
v_b_3219_ = v___x_3222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg___boxed(lean_object* v_upperBound_3226_, lean_object* v___x_3227_, lean_object* v_fst_3228_, lean_object* v___x_3229_, lean_object* v_a_3230_, lean_object* v_b_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3226_, v___x_3227_, v_fst_3228_, v___x_3229_, v_a_3230_, v_b_3231_);
lean_dec(v___x_3229_);
lean_dec_ref(v_fst_3228_);
lean_dec(v___x_3227_);
lean_dec(v_upperBound_3226_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(lean_object* v_a_3233_, lean_object* v_b_3234_){
_start:
{
lean_object* v_array_3235_; lean_object* v_start_3236_; lean_object* v_stop_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3250_; 
v_array_3235_ = lean_ctor_get(v_a_3233_, 0);
v_start_3236_ = lean_ctor_get(v_a_3233_, 1);
v_stop_3237_ = lean_ctor_get(v_a_3233_, 2);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_a_3233_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3239_ = v_a_3233_;
v_isShared_3240_ = v_isSharedCheck_3250_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_stop_3237_);
lean_inc(v_start_3236_);
lean_inc(v_array_3235_);
lean_dec(v_a_3233_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3250_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
uint8_t v___x_3241_; 
v___x_3241_ = lean_nat_dec_lt(v_start_3236_, v_stop_3237_);
if (v___x_3241_ == 0)
{
lean_del_object(v___x_3239_);
lean_dec(v_stop_3237_);
lean_dec(v_start_3236_);
lean_dec_ref(v_array_3235_);
return v_b_3234_;
}
else
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3242_ = lean_unsigned_to_nat(1u);
v___x_3243_ = lean_nat_add(v_start_3236_, v___x_3242_);
lean_inc_ref(v_array_3235_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 1, v___x_3243_);
v___x_3245_ = v___x_3239_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_array_3235_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3249_, 2, v_stop_3237_);
v___x_3245_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = lean_array_fget(v_array_3235_, v_start_3236_);
lean_dec(v_start_3236_);
lean_dec_ref(v_array_3235_);
v___x_3247_ = lean_array_push(v_b_3234_, v___x_3246_);
v_a_3233_ = v___x_3245_;
v_b_3234_ = v___x_3247_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(lean_object* v_left_3251_, lean_object* v_right_3252_, lean_object* v_i_3253_){
_start:
{
lean_object* v_start_3254_; lean_object* v_stop_3255_; lean_object* v___x_3256_; uint8_t v___x_3270_; 
v_start_3254_ = lean_ctor_get(v_left_3251_, 1);
v_stop_3255_ = lean_ctor_get(v_left_3251_, 2);
v___x_3256_ = lean_nat_sub(v_stop_3255_, v_start_3254_);
v___x_3270_ = lean_nat_dec_lt(v_i_3253_, v___x_3256_);
if (v___x_3270_ == 0)
{
goto v___jp_3257_;
}
else
{
lean_object* v_start_3271_; lean_object* v_stop_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v_start_3271_ = lean_ctor_get(v_right_3252_, 1);
v_stop_3272_ = lean_ctor_get(v_right_3252_, 2);
v___x_3273_ = lean_nat_sub(v_stop_3272_, v_start_3271_);
v___x_3274_ = lean_nat_dec_lt(v_i_3253_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_dec(v___x_3273_);
goto v___jp_3257_;
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3275_ = lean_nat_sub(v___x_3256_, v_i_3253_);
lean_dec(v___x_3256_);
v___x_3276_ = lean_unsigned_to_nat(1u);
v___x_3277_ = lean_nat_sub(v___x_3275_, v___x_3276_);
v___x_3278_ = l_Subarray_get___redArg(v_left_3251_, v___x_3277_);
lean_dec(v___x_3277_);
v___x_3279_ = lean_nat_sub(v___x_3273_, v_i_3253_);
lean_dec(v___x_3273_);
v___x_3280_ = lean_nat_sub(v___x_3279_, v___x_3276_);
v___x_3281_ = l_Subarray_get___redArg(v_right_3252_, v___x_3280_);
lean_dec(v___x_3280_);
v___x_3282_ = lean_string_dec_eq(v___x_3278_, v___x_3281_);
lean_dec(v___x_3281_);
lean_dec(v___x_3278_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
lean_dec(v_i_3253_);
lean_inc_ref(v_left_3251_);
v___x_3283_ = l_Subarray_take___redArg(v_left_3251_, v___x_3275_);
v___x_3284_ = l_Subarray_take___redArg(v_right_3252_, v___x_3279_);
lean_dec(v___x_3279_);
v___x_3285_ = l_Subarray_drop___redArg(v_left_3251_, v___x_3275_);
lean_dec(v___x_3275_);
v___x_3286_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3287_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3285_, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3284_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3283_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
return v___x_3289_;
}
else
{
lean_object* v___x_3290_; 
lean_dec(v___x_3279_);
lean_dec(v___x_3275_);
v___x_3290_ = lean_nat_add(v_i_3253_, v___x_3276_);
lean_dec(v_i_3253_);
v_i_3253_ = v___x_3290_;
goto _start;
}
}
}
v___jp_3257_:
{
lean_object* v_start_3258_; lean_object* v_stop_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v_start_3258_ = lean_ctor_get(v_right_3252_, 1);
v_stop_3259_ = lean_ctor_get(v_right_3252_, 2);
v___x_3260_ = lean_nat_sub(v___x_3256_, v_i_3253_);
lean_dec(v___x_3256_);
lean_inc_ref(v_left_3251_);
v___x_3261_ = l_Subarray_take___redArg(v_left_3251_, v___x_3260_);
v___x_3262_ = lean_nat_sub(v_stop_3259_, v_start_3258_);
v___x_3263_ = lean_nat_sub(v___x_3262_, v_i_3253_);
lean_dec(v_i_3253_);
lean_dec(v___x_3262_);
v___x_3264_ = l_Subarray_take___redArg(v_right_3252_, v___x_3263_);
lean_dec(v___x_3263_);
v___x_3265_ = l_Subarray_drop___redArg(v_left_3251_, v___x_3260_);
lean_dec(v___x_3260_);
v___x_3266_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3267_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3265_, v___x_3266_);
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3264_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3261_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
return v___x_3269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(lean_object* v_left_3292_, lean_object* v_right_3293_){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = lean_unsigned_to_nat(0u);
v___x_3295_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(v_left_3292_, v_right_3293_, v___x_3294_);
return v___x_3295_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = lean_box(0);
v___x_3297_ = lean_unsigned_to_nat(16u);
v___x_3298_ = lean_mk_array(v___x_3297_, v___x_3296_);
return v___x_3298_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v_hist_3301_; 
v___x_3299_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0);
v___x_3300_ = lean_unsigned_to_nat(0u);
v_hist_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3301_, 0, v___x_3300_);
lean_ctor_set(v_hist_3301_, 1, v___x_3299_);
return v_hist_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_left_3302_, lean_object* v_right_3303_){
_start:
{
lean_object* v___x_3304_; lean_object* v_snd_3305_; lean_object* v_fst_3306_; lean_object* v_fst_3307_; lean_object* v_snd_3308_; lean_object* v___x_3309_; lean_object* v_snd_3310_; lean_object* v_fst_3311_; lean_object* v_fst_3312_; lean_object* v_snd_3313_; lean_object* v_start_3314_; lean_object* v_stop_3315_; lean_object* v___x_3316_; lean_object* v_hist_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v_start_3320_; lean_object* v_stop_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v_buckets_3324_; lean_object* v___x_3325_; lean_object* v___y_3327_; lean_object* v___x_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v___x_3304_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(v_left_3302_, v_right_3303_);
v_snd_3305_ = lean_ctor_get(v___x_3304_, 1);
lean_inc(v_snd_3305_);
v_fst_3306_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_fst_3306_);
lean_dec_ref(v___x_3304_);
v_fst_3307_ = lean_ctor_get(v_snd_3305_, 0);
lean_inc(v_fst_3307_);
v_snd_3308_ = lean_ctor_get(v_snd_3305_, 1);
lean_inc(v_snd_3308_);
lean_dec(v_snd_3305_);
v___x_3309_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(v_fst_3307_, v_snd_3308_);
v_snd_3310_ = lean_ctor_get(v___x_3309_, 1);
lean_inc(v_snd_3310_);
v_fst_3311_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_fst_3311_);
lean_dec_ref(v___x_3309_);
v_fst_3312_ = lean_ctor_get(v_snd_3310_, 0);
lean_inc(v_fst_3312_);
v_snd_3313_ = lean_ctor_get(v_snd_3310_, 1);
lean_inc(v_snd_3313_);
lean_dec(v_snd_3310_);
v_start_3314_ = lean_ctor_get(v_fst_3311_, 1);
v_stop_3315_ = lean_ctor_get(v_fst_3311_, 2);
v___x_3316_ = lean_unsigned_to_nat(0u);
v_hist_3317_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1);
v___x_3318_ = lean_nat_sub(v_stop_3315_, v_start_3314_);
v___x_3319_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v___x_3318_, v_fst_3312_, v___x_3318_, v_fst_3311_, v___x_3316_, v_hist_3317_);
v_start_3320_ = lean_ctor_get(v_fst_3312_, 1);
v_stop_3321_ = lean_ctor_get(v_fst_3312_, 2);
v___x_3322_ = lean_nat_sub(v_stop_3321_, v_start_3320_);
v___x_3323_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v___x_3322_, v___x_3322_, v_fst_3312_, v___x_3318_, v___x_3316_, v___x_3319_);
lean_dec(v___x_3318_);
lean_dec(v___x_3322_);
v_buckets_3324_ = lean_ctor_get(v___x_3323_, 1);
lean_inc_ref(v_buckets_3324_);
lean_dec_ref(v___x_3323_);
v___x_3325_ = lean_box(0);
v___x_3353_ = lean_box(0);
v___x_3354_ = lean_array_get_size(v_buckets_3324_);
v___x_3355_ = lean_nat_dec_lt(v___x_3316_, v___x_3354_);
if (v___x_3355_ == 0)
{
lean_dec_ref(v_buckets_3324_);
v___y_3327_ = v___x_3353_;
goto v___jp_3326_;
}
else
{
size_t v___x_3356_; size_t v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = lean_usize_of_nat(v___x_3354_);
v___x_3357_ = ((size_t)0ULL);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_buckets_3324_, v___x_3356_, v___x_3357_, v___x_3353_);
lean_dec_ref(v_buckets_3324_);
v___y_3327_ = v___x_3358_;
goto v___jp_3326_;
}
v___jp_3326_:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v___y_3327_, v___x_3325_);
lean_dec(v___y_3327_);
if (lean_obj_tag(v___x_3328_) == 1)
{
lean_object* v_val_3329_; lean_object* v_snd_3330_; lean_object* v_snd_3331_; lean_object* v_fst_3332_; lean_object* v_fst_3333_; lean_object* v_snd_3334_; lean_object* v___x_3335_; lean_object* v_fst_3336_; lean_object* v_snd_3337_; lean_object* v___x_3338_; lean_object* v_fst_3339_; lean_object* v_snd_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v_val_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_val_3329_);
lean_dec_ref_known(v___x_3328_, 1);
v_snd_3330_ = lean_ctor_get(v_val_3329_, 1);
lean_inc(v_snd_3330_);
lean_dec(v_val_3329_);
v_snd_3331_ = lean_ctor_get(v_snd_3330_, 1);
lean_inc(v_snd_3331_);
v_fst_3332_ = lean_ctor_get(v_snd_3330_, 0);
lean_inc(v_fst_3332_);
lean_dec(v_snd_3330_);
v_fst_3333_ = lean_ctor_get(v_snd_3331_, 0);
lean_inc(v_fst_3333_);
v_snd_3334_ = lean_ctor_get(v_snd_3331_, 1);
lean_inc(v_snd_3334_);
lean_dec(v_snd_3331_);
v___x_3335_ = l_Subarray_split___redArg(v_fst_3311_, v_fst_3333_);
lean_dec(v_fst_3333_);
v_fst_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_fst_3336_);
v_snd_3337_ = lean_ctor_get(v___x_3335_, 1);
lean_inc(v_snd_3337_);
lean_dec_ref(v___x_3335_);
v___x_3338_ = l_Subarray_split___redArg(v_fst_3312_, v_snd_3334_);
lean_dec(v_snd_3334_);
v_fst_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_fst_3339_);
v_snd_3340_ = lean_ctor_get(v___x_3338_, 1);
lean_inc(v_snd_3340_);
lean_dec_ref(v___x_3338_);
v___x_3341_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_fst_3336_, v_fst_3339_);
v___x_3342_ = l_Array_append___redArg(v_fst_3306_, v___x_3341_);
lean_dec_ref(v___x_3341_);
v___x_3343_ = lean_unsigned_to_nat(1u);
v___x_3344_ = lean_mk_empty_array_with_capacity(v___x_3343_);
v___x_3345_ = lean_array_push(v___x_3344_, v_fst_3332_);
v___x_3346_ = l_Array_append___redArg(v___x_3342_, v___x_3345_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = l_Subarray_drop___redArg(v_snd_3337_, v___x_3343_);
v___x_3348_ = l_Subarray_drop___redArg(v_snd_3340_, v___x_3343_);
v___x_3349_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3347_, v___x_3348_);
v___x_3350_ = l_Array_append___redArg(v___x_3346_, v___x_3349_);
lean_dec_ref(v___x_3349_);
v___x_3351_ = l_Array_append___redArg(v___x_3350_, v_snd_3313_);
lean_dec(v_snd_3313_);
return v___x_3351_;
}
else
{
lean_object* v___x_3352_; 
lean_dec(v___x_3328_);
lean_dec(v_fst_3312_);
lean_dec(v_fst_3311_);
v___x_3352_ = l_Array_append___redArg(v_fst_3306_, v_snd_3313_);
lean_dec(v_snd_3313_);
return v___x_3352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3359_, size_t v_i_3360_, lean_object* v_bs_3361_){
_start:
{
uint8_t v___x_3362_; 
v___x_3362_ = lean_usize_dec_lt(v_i_3360_, v_sz_3359_);
if (v___x_3362_ == 0)
{
return v_bs_3361_;
}
else
{
lean_object* v_v_3363_; lean_object* v___x_3364_; lean_object* v_bs_x27_3365_; uint8_t v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; size_t v___x_3369_; size_t v___x_3370_; lean_object* v___x_3371_; 
v_v_3363_ = lean_array_uget(v_bs_3361_, v_i_3360_);
v___x_3364_ = lean_unsigned_to_nat(0u);
v_bs_x27_3365_ = lean_array_uset(v_bs_3361_, v_i_3360_, v___x_3364_);
v___x_3366_ = 1;
v___x_3367_ = lean_box(v___x_3366_);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
lean_ctor_set(v___x_3368_, 1, v_v_3363_);
v___x_3369_ = ((size_t)1ULL);
v___x_3370_ = lean_usize_add(v_i_3360_, v___x_3369_);
v___x_3371_ = lean_array_uset(v_bs_x27_3365_, v_i_3360_, v___x_3368_);
v_i_3360_ = v___x_3370_;
v_bs_3361_ = v___x_3371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3373_, lean_object* v_i_3374_, lean_object* v_bs_3375_){
_start:
{
size_t v_sz_boxed_3376_; size_t v_i_boxed_3377_; lean_object* v_res_3378_; 
v_sz_boxed_3376_ = lean_unbox_usize(v_sz_3373_);
lean_dec(v_sz_3373_);
v_i_boxed_3377_ = lean_unbox_usize(v_i_3374_);
lean_dec(v_i_3374_);
v_res_3378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3376_, v_i_boxed_3377_, v_bs_3375_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3386_, lean_object* v_edited_3387_){
_start:
{
lean_object* v_i_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v_i_3388_ = lean_unsigned_to_nat(0u);
v___x_3389_ = lean_array_get_size(v_original_3386_);
v___x_3390_ = lean_nat_dec_lt(v_i_3388_, v___x_3389_);
if (v___x_3390_ == 0)
{
size_t v_sz_3391_; size_t v___x_3392_; lean_object* v___x_3393_; 
lean_dec_ref(v_original_3386_);
v_sz_3391_ = lean_array_size(v_edited_3387_);
v___x_3392_ = ((size_t)0ULL);
v___x_3393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3391_, v___x_3392_, v_edited_3387_);
return v___x_3393_;
}
else
{
lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3394_ = lean_array_get_size(v_edited_3387_);
v___x_3395_ = lean_nat_dec_lt(v_i_3388_, v___x_3394_);
if (v___x_3395_ == 0)
{
size_t v_sz_3396_; size_t v___x_3397_; lean_object* v___x_3398_; 
lean_dec_ref(v_edited_3387_);
v_sz_3396_ = lean_array_size(v_original_3386_);
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3396_, v___x_3397_, v_original_3386_);
return v___x_3398_;
}
else
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v_ds_3401_; lean_object* v___x_3402_; size_t v_sz_3403_; size_t v___x_3404_; lean_object* v___x_3405_; lean_object* v_snd_3406_; lean_object* v_fst_3407_; lean_object* v_fst_3408_; lean_object* v_snd_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3428_; 
lean_inc_ref(v_original_3386_);
v___x_3399_ = l_Array_toSubarray___redArg(v_original_3386_, v_i_3388_, v___x_3389_);
lean_inc_ref(v_edited_3387_);
v___x_3400_ = l_Array_toSubarray___redArg(v_edited_3387_, v_i_3388_, v___x_3394_);
v_ds_3401_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3399_, v___x_3400_);
v___x_3402_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3403_ = lean_array_size(v_ds_3401_);
v___x_3404_ = ((size_t)0ULL);
v___x_3405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_3394_, v_edited_3387_, v___x_3389_, v_original_3386_, v_ds_3401_, v_sz_3403_, v___x_3404_, v___x_3402_);
lean_dec_ref(v_ds_3401_);
v_snd_3406_ = lean_ctor_get(v___x_3405_, 1);
lean_inc(v_snd_3406_);
v_fst_3407_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_fst_3407_);
lean_dec_ref(v___x_3405_);
v_fst_3408_ = lean_ctor_get(v_snd_3406_, 0);
v_snd_3409_ = lean_ctor_get(v_snd_3406_, 1);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_snd_3406_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3411_ = v_snd_3406_;
v_isShared_3412_ = v_isSharedCheck_3428_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_snd_3409_);
lean_inc(v_fst_3408_);
lean_dec(v_snd_3406_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3428_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 1, v_fst_3408_);
lean_ctor_set(v___x_3411_, 0, v_fst_3407_);
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_fst_3407_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_fst_3408_);
v___x_3414_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3415_; lean_object* v_fst_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3425_; 
v___x_3415_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3389_, v_original_3386_, v___x_3414_);
lean_dec_ref(v_original_3386_);
v_fst_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; 
v_unused_3426_ = lean_ctor_get(v___x_3415_, 1);
lean_dec(v_unused_3426_);
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3425_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_fst_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3425_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 1, v_snd_3409_);
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_fst_3416_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_snd_3409_);
v___x_3421_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3422_; lean_object* v_fst_3423_; 
v___x_3422_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3394_, v_edited_3387_, v___x_3421_);
lean_dec_ref(v_edited_3387_);
v_fst_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_fst_3423_);
lean_dec_ref(v___x_3422_);
return v_fst_3423_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3429_, lean_object* v_x_3430_, lean_object* v_x_3431_){
_start:
{
if (lean_obj_tag(v_x_3430_) == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = l_List_reverse___redArg(v_x_3431_);
v___x_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
return v___x_3434_;
}
else
{
lean_object* v_head_3435_; lean_object* v_tail_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3445_; 
v_head_3435_ = lean_ctor_get(v_x_3430_, 0);
v_tail_3436_ = lean_ctor_get(v_x_3430_, 1);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_x_3430_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3438_ = v_x_3430_;
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_tail_3436_);
lean_inc(v_head_3435_);
lean_dec(v_x_3430_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3440_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3435_, v___y_3429_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v_x_3431_);
lean_ctor_set(v___x_3438_, 0, v___x_3440_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_x_3431_);
v___x_3442_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
v_x_3430_ = v_tail_3436_;
v_x_3431_ = v___x_3442_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3446_, lean_object* v_x_3447_, lean_object* v_x_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3446_, v_x_3447_, v_x_3448_);
lean_dec(v___y_3446_);
return v_res_3450_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3456_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3457_ = l_Lean_stringToMessageData(v___x_3456_);
return v___x_3457_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5(void){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = l_Lean_MessageLog_empty;
v___x_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v___x_3471_; uint8_t v___x_3472_; 
v___x_3471_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
lean_inc(v_x_3467_);
v___x_3472_ = l_Lean_Syntax_isOfKind(v_x_3467_, v___x_3471_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; 
lean_dec(v_x_3467_);
v___x_3473_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3473_;
}
else
{
lean_object* v___x_3474_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; uint8_t v___y_3515_; lean_object* v___y_3580_; uint8_t v___y_3581_; uint8_t v___y_3582_; lean_object* v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v_dc_x3f_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___x_3723_; lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3474_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3723_ = lean_unsigned_to_nat(0u);
v___x_3724_ = l_Lean_Syntax_getArg(v_x_3467_, v___x_3723_);
v___x_3725_ = l_Lean_Syntax_isNone(v___x_3724_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; uint8_t v___x_3727_; 
v___x_3726_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3724_);
v___x_3727_ = l_Lean_Syntax_matchesNull(v___x_3724_, v___x_3726_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; 
lean_dec(v___x_3724_);
lean_dec(v_x_3467_);
v___x_3728_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3728_;
}
else
{
lean_object* v_dc_x3f_3729_; lean_object* v___x_3730_; uint8_t v___x_3731_; 
v_dc_x3f_3729_ = l_Lean_Syntax_getArg(v___x_3724_, v___x_3723_);
lean_dec(v___x_3724_);
v___x_3730_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3729_);
v___x_3731_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3729_, v___x_3730_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; 
lean_dec(v_dc_x3f_3729_);
lean_dec(v_x_3467_);
v___x_3732_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3732_;
}
else
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3733_, 0, v_dc_x3f_3729_);
v_dc_x3f_3704_ = v___x_3733_;
v___y_3705_ = v_a_3468_;
v___y_3706_ = v_a_3469_;
goto v___jp_3703_;
}
}
}
else
{
lean_object* v___x_3734_; 
lean_dec(v___x_3724_);
v___x_3734_ = lean_box(0);
v_dc_x3f_3704_ = v___x_3734_;
v___y_3705_ = v_a_3468_;
v___y_3706_ = v_a_3469_;
goto v___jp_3703_;
}
v___jp_3475_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3481_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3482_ = l_Lean_stringToMessageData(v___y_3480_);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3479_, v___x_3483_, v___y_3477_, v___y_3476_);
lean_dec(v___y_3479_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3504_; 
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3504_ == 0)
{
lean_object* v_unused_3505_; 
v_unused_3505_ = lean_ctor_get(v___x_3484_, 0);
lean_dec(v_unused_3505_);
v___x_3486_ = v___x_3484_;
v_isShared_3487_ = v_isSharedCheck_3504_;
goto v_resetjp_3485_;
}
else
{
lean_dec(v___x_3484_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3504_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_Elab_Command_getRef___redArg(v___y_3477_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3493_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3474_);
lean_ctor_set(v___x_3490_, 1, v___y_3478_);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v_a_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set_tag(v___x_3486_, 10);
lean_ctor_set(v___x_3486_, 0, v___x_3491_);
v___x_3493_ = v___x_3486_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3493_, v___y_3477_, v___y_3476_);
return v___x_3494_;
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_del_object(v___x_3486_);
lean_dec_ref(v___y_3478_);
v_a_3496_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3488_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3488_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3478_);
return v___x_3484_;
}
}
v___jp_3506_:
{
if (v___y_3515_ == 0)
{
lean_object* v___x_3516_; lean_object* v_env_3517_; lean_object* v_scopes_3518_; lean_object* v_usedQuotCtxts_3519_; lean_object* v_nextMacroScope_3520_; lean_object* v_maxRecDepth_3521_; lean_object* v_ngen_3522_; lean_object* v_auxDeclNGen_3523_; lean_object* v_infoState_3524_; lean_object* v_traceState_3525_; lean_object* v_snapshotTasks_3526_; lean_object* v_prevLinterStates_3527_; lean_object* v_codeQualityEntryTasks_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3553_; 
lean_dec(v___y_3513_);
v___x_3516_ = lean_st_ref_take(v___y_3507_);
v_env_3517_ = lean_ctor_get(v___x_3516_, 0);
v_scopes_3518_ = lean_ctor_get(v___x_3516_, 2);
v_usedQuotCtxts_3519_ = lean_ctor_get(v___x_3516_, 3);
v_nextMacroScope_3520_ = lean_ctor_get(v___x_3516_, 4);
v_maxRecDepth_3521_ = lean_ctor_get(v___x_3516_, 5);
v_ngen_3522_ = lean_ctor_get(v___x_3516_, 6);
v_auxDeclNGen_3523_ = lean_ctor_get(v___x_3516_, 7);
v_infoState_3524_ = lean_ctor_get(v___x_3516_, 8);
v_traceState_3525_ = lean_ctor_get(v___x_3516_, 9);
v_snapshotTasks_3526_ = lean_ctor_get(v___x_3516_, 10);
v_prevLinterStates_3527_ = lean_ctor_get(v___x_3516_, 11);
v_codeQualityEntryTasks_3528_ = lean_ctor_get(v___x_3516_, 12);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; 
v_unused_3554_ = lean_ctor_get(v___x_3516_, 1);
lean_dec(v_unused_3554_);
v___x_3530_ = v___x_3516_;
v_isShared_3531_ = v_isSharedCheck_3553_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3528_);
lean_inc(v_prevLinterStates_3527_);
lean_inc(v_snapshotTasks_3526_);
lean_inc(v_traceState_3525_);
lean_inc(v_infoState_3524_);
lean_inc(v_auxDeclNGen_3523_);
lean_inc(v_ngen_3522_);
lean_inc(v_maxRecDepth_3521_);
lean_inc(v_nextMacroScope_3520_);
lean_inc(v_usedQuotCtxts_3519_);
lean_inc(v_scopes_3518_);
lean_inc(v_env_3517_);
lean_dec(v___x_3516_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3553_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 1, v___y_3511_);
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_env_3517_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v___y_3511_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_scopes_3518_);
lean_ctor_set(v_reuseFailAlloc_3552_, 3, v_usedQuotCtxts_3519_);
lean_ctor_set(v_reuseFailAlloc_3552_, 4, v_nextMacroScope_3520_);
lean_ctor_set(v_reuseFailAlloc_3552_, 5, v_maxRecDepth_3521_);
lean_ctor_set(v_reuseFailAlloc_3552_, 6, v_ngen_3522_);
lean_ctor_set(v_reuseFailAlloc_3552_, 7, v_auxDeclNGen_3523_);
lean_ctor_set(v_reuseFailAlloc_3552_, 8, v_infoState_3524_);
lean_ctor_set(v_reuseFailAlloc_3552_, 9, v_traceState_3525_);
lean_ctor_set(v_reuseFailAlloc_3552_, 10, v_snapshotTasks_3526_);
lean_ctor_set(v_reuseFailAlloc_3552_, 11, v_prevLinterStates_3527_);
lean_ctor_set(v_reuseFailAlloc_3552_, 12, v_codeQualityEntryTasks_3528_);
v___x_3533_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v_scopes_3537_; lean_object* v___x_3538_; lean_object* v_opts_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
v___x_3534_ = lean_st_ref_put(v___y_3507_, v___x_3533_);
v___x_3535_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3536_ = lean_st_ref_get(v___y_3507_);
v_scopes_3537_ = lean_ctor_get(v___x_3536_, 2);
lean_inc(v_scopes_3537_);
lean_dec(v___x_3536_);
v___x_3538_ = l_List_head_x21___redArg(v___x_3535_, v_scopes_3537_);
lean_dec(v_scopes_3537_);
v_opts_3539_ = lean_ctor_get(v___x_3538_, 1);
lean_inc_ref(v_opts_3539_);
lean_dec(v___x_3538_);
v___x_3540_ = l_Lean_guard__msgs_diff;
v___x_3541_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3539_, v___x_3540_);
lean_dec_ref(v_opts_3539_);
if (v___x_3541_ == 0)
{
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3509_);
lean_inc_ref(v___y_3510_);
v___y_3476_ = v___y_3507_;
v___y_3477_ = v___y_3508_;
v___y_3478_ = v___y_3510_;
v___y_3479_ = v___y_3514_;
v___y_3480_ = v___y_3510_;
goto v___jp_3475_;
}
else
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3542_ = lean_string_utf8_byte_size(v___y_3512_);
lean_inc(v___y_3509_);
lean_inc_ref(v___y_3512_);
v___x_3543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3543_, 0, v___y_3512_);
lean_ctor_set(v___x_3543_, 1, v___y_3509_);
lean_ctor_set(v___x_3543_, 2, v___x_3542_);
v___x_3544_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
v___x_3545_ = lean_mk_empty_array_with_capacity(v___y_3509_);
lean_inc_ref(v___x_3545_);
v___x_3546_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3512_, v___x_3543_, v___x_3542_, v___x_3544_, v___x_3545_);
lean_dec_ref_known(v___x_3543_, 3);
v___x_3547_ = lean_string_utf8_byte_size(v___y_3510_);
lean_inc_ref_n(v___y_3510_, 2);
v___x_3548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3548_, 0, v___y_3510_);
lean_ctor_set(v___x_3548_, 1, v___y_3509_);
lean_ctor_set(v___x_3548_, 2, v___x_3547_);
v___x_3549_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3510_, v___x_3548_, v___x_3547_, v___x_3544_, v___x_3545_);
lean_dec_ref_known(v___x_3548_, 3);
v___x_3550_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3546_, v___x_3549_);
v___x_3551_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3550_);
lean_dec_ref(v___x_3550_);
v___y_3476_ = v___y_3507_;
v___y_3477_ = v___y_3508_;
v___y_3478_ = v___y_3510_;
v___y_3479_ = v___y_3514_;
v___y_3480_ = v___x_3551_;
goto v___jp_3475_;
}
}
}
}
else
{
lean_object* v___x_3555_; lean_object* v_env_3556_; lean_object* v_scopes_3557_; lean_object* v_usedQuotCtxts_3558_; lean_object* v_nextMacroScope_3559_; lean_object* v_maxRecDepth_3560_; lean_object* v_ngen_3561_; lean_object* v_auxDeclNGen_3562_; lean_object* v_infoState_3563_; lean_object* v_traceState_3564_; lean_object* v_snapshotTasks_3565_; lean_object* v_prevLinterStates_3566_; lean_object* v_codeQualityEntryTasks_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3577_; 
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
v___x_3555_ = lean_st_ref_take(v___y_3507_);
v_env_3556_ = lean_ctor_get(v___x_3555_, 0);
v_scopes_3557_ = lean_ctor_get(v___x_3555_, 2);
v_usedQuotCtxts_3558_ = lean_ctor_get(v___x_3555_, 3);
v_nextMacroScope_3559_ = lean_ctor_get(v___x_3555_, 4);
v_maxRecDepth_3560_ = lean_ctor_get(v___x_3555_, 5);
v_ngen_3561_ = lean_ctor_get(v___x_3555_, 6);
v_auxDeclNGen_3562_ = lean_ctor_get(v___x_3555_, 7);
v_infoState_3563_ = lean_ctor_get(v___x_3555_, 8);
v_traceState_3564_ = lean_ctor_get(v___x_3555_, 9);
v_snapshotTasks_3565_ = lean_ctor_get(v___x_3555_, 10);
v_prevLinterStates_3566_ = lean_ctor_get(v___x_3555_, 11);
v_codeQualityEntryTasks_3567_ = lean_ctor_get(v___x_3555_, 12);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; 
v_unused_3578_ = lean_ctor_get(v___x_3555_, 1);
lean_dec(v_unused_3578_);
v___x_3569_ = v___x_3555_;
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3567_);
lean_inc(v_prevLinterStates_3566_);
lean_inc(v_snapshotTasks_3565_);
lean_inc(v_traceState_3564_);
lean_inc(v_infoState_3563_);
lean_inc(v_auxDeclNGen_3562_);
lean_inc(v_ngen_3561_);
lean_inc(v_maxRecDepth_3560_);
lean_inc(v_nextMacroScope_3559_);
lean_inc(v_usedQuotCtxts_3558_);
lean_inc(v_scopes_3557_);
lean_inc(v_env_3556_);
lean_dec(v___x_3555_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; lean_object* v___x_3573_; 
v___x_3571_ = lean_box(0);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v___y_3513_);
v___x_3573_ = v___x_3569_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_env_3556_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v___y_3513_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v_scopes_3557_);
lean_ctor_set(v_reuseFailAlloc_3576_, 3, v_usedQuotCtxts_3558_);
lean_ctor_set(v_reuseFailAlloc_3576_, 4, v_nextMacroScope_3559_);
lean_ctor_set(v_reuseFailAlloc_3576_, 5, v_maxRecDepth_3560_);
lean_ctor_set(v_reuseFailAlloc_3576_, 6, v_ngen_3561_);
lean_ctor_set(v_reuseFailAlloc_3576_, 7, v_auxDeclNGen_3562_);
lean_ctor_set(v_reuseFailAlloc_3576_, 8, v_infoState_3563_);
lean_ctor_set(v_reuseFailAlloc_3576_, 9, v_traceState_3564_);
lean_ctor_set(v_reuseFailAlloc_3576_, 10, v_snapshotTasks_3565_);
lean_ctor_set(v_reuseFailAlloc_3576_, 11, v_prevLinterStates_3566_);
lean_ctor_set(v_reuseFailAlloc_3576_, 12, v_codeQualityEntryTasks_3567_);
v___x_3573_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = lean_st_ref_put(v___y_3507_, v___x_3573_);
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3571_);
return v___x_3575_;
}
}
}
}
v___jp_3579_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v_a_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v_str_3602_; lean_object* v_startInclusive_3603_; lean_object* v_endExclusive_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3619_; 
v___x_3592_ = l_Lean_MessageLog_toList(v___y_3589_);
lean_dec(v___y_3589_);
v___x_3593_ = lean_box(0);
v___x_3594_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3591_, v___x_3592_, v___x_3593_);
lean_dec(v___y_3591_);
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref(v___x_3594_);
v___x_3596_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3584_, v_a_3595_);
v___x_3597_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4));
v___x_3598_ = l_String_intercalate(v___x_3597_, v___x_3596_);
v___x_3599_ = lean_string_utf8_byte_size(v___x_3598_);
lean_inc(v___y_3585_);
v___x_3600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3598_);
lean_ctor_set(v___x_3600_, 1, v___y_3585_);
lean_ctor_set(v___x_3600_, 2, v___x_3599_);
v___x_3601_ = l_String_Slice_trimAscii(v___x_3600_);
v_str_3602_ = lean_ctor_get(v___x_3601_, 0);
v_startInclusive_3603_ = lean_ctor_get(v___x_3601_, 1);
v_endExclusive_3604_ = lean_ctor_get(v___x_3601_, 2);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3606_ = v___x_3601_;
v_isShared_3607_ = v_isSharedCheck_3619_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_endExclusive_3604_);
lean_inc(v_startInclusive_3603_);
lean_inc(v_str_3602_);
lean_dec(v___x_3601_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3619_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; 
v___x_3608_ = lean_string_utf8_extract_fast(v_str_3602_, v_startInclusive_3603_, v_endExclusive_3604_);
lean_dec(v_endExclusive_3604_);
lean_dec(v_startInclusive_3603_);
lean_dec_ref(v_str_3602_);
if (v___y_3582_ == 0)
{
lean_object* v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
lean_del_object(v___x_3606_);
lean_inc_ref(v___y_3587_);
v___x_3609_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3581_, v___y_3587_);
lean_inc_ref(v___x_3608_);
v___x_3610_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3581_, v___x_3608_);
v___x_3611_ = lean_string_dec_eq(v___x_3609_, v___x_3610_);
lean_dec_ref(v___x_3610_);
lean_dec_ref(v___x_3609_);
v___y_3507_ = v___y_3580_;
v___y_3508_ = v___y_3583_;
v___y_3509_ = v___y_3585_;
v___y_3510_ = v___x_3608_;
v___y_3511_ = v___y_3586_;
v___y_3512_ = v___y_3587_;
v___y_3513_ = v___y_3588_;
v___y_3514_ = v___y_3590_;
v___y_3515_ = v___x_3611_;
goto v___jp_3506_;
}
else
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3616_; 
lean_inc_ref(v___x_3608_);
v___x_3612_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3581_, v___x_3608_);
lean_inc_ref(v___y_3587_);
v___x_3613_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3581_, v___y_3587_);
v___x_3614_ = lean_string_utf8_byte_size(v___x_3612_);
lean_inc(v___y_3585_);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 2, v___x_3614_);
lean_ctor_set(v___x_3606_, 1, v___y_3585_);
lean_ctor_set(v___x_3606_, 0, v___x_3612_);
v___x_3616_ = v___x_3606_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v___y_3585_);
lean_ctor_set(v_reuseFailAlloc_3618_, 2, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
uint8_t v___x_3617_; 
v___x_3617_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3613_, v___x_3616_);
lean_dec_ref(v___x_3616_);
v___y_3507_ = v___y_3580_;
v___y_3508_ = v___y_3583_;
v___y_3509_ = v___y_3585_;
v___y_3510_ = v___x_3608_;
v___y_3511_ = v___y_3586_;
v___y_3512_ = v___y_3587_;
v___y_3513_ = v___y_3588_;
v___y_3514_ = v___y_3590_;
v___y_3515_ = v___x_3617_;
goto v___jp_3506_;
}
}
}
}
v___jp_3620_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v_str_3631_; lean_object* v_startInclusive_3632_; lean_object* v_endExclusive_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = lean_string_utf8_byte_size(v___y_3626_);
v___x_3629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3629_, 0, v___y_3626_);
lean_ctor_set(v___x_3629_, 1, v___x_3627_);
lean_ctor_set(v___x_3629_, 2, v___x_3628_);
v___x_3630_ = l_String_Slice_trimAscii(v___x_3629_);
v_str_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc_ref(v_str_3631_);
v_startInclusive_3632_ = lean_ctor_get(v___x_3630_, 1);
lean_inc(v_startInclusive_3632_);
v_endExclusive_3633_ = lean_ctor_get(v___x_3630_, 2);
lean_inc(v_endExclusive_3633_);
lean_dec_ref(v___x_3630_);
v___x_3634_ = lean_string_utf8_extract_fast(v_str_3631_, v_startInclusive_3632_, v_endExclusive_3633_);
lean_dec(v_endExclusive_3633_);
lean_dec(v_startInclusive_3632_);
lean_dec_ref(v_str_3631_);
v___x_3635_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3634_);
v___x_3636_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3623_, v___y_3622_, v___y_3621_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v_filterFn_3638_; uint8_t v_whitespace_3639_; uint8_t v_ordering_3640_; uint8_t v_reportPositions_3641_; uint8_t v_substring_3642_; lean_object* v___x_3643_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v_filterFn_3638_ = lean_ctor_get(v_a_3637_, 0);
lean_inc_ref(v_filterFn_3638_);
v_whitespace_3639_ = lean_ctor_get_uint8(v_a_3637_, sizeof(void*)*1);
v_ordering_3640_ = lean_ctor_get_uint8(v_a_3637_, sizeof(void*)*1 + 1);
v_reportPositions_3641_ = lean_ctor_get_uint8(v_a_3637_, sizeof(void*)*1 + 2);
v_substring_3642_ = lean_ctor_get_uint8(v_a_3637_, sizeof(void*)*1 + 3);
lean_dec(v_a_3637_);
v___x_3643_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3625_, v___y_3622_, v___y_3621_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v_a_3648_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3643_, 1);
v___x_3645_ = l_Lean_MessageLog_toList(v_a_3644_);
v___x_3646_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5);
v___x_3647_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3638_, v___x_3645_, v___x_3646_);
lean_dec(v___x_3645_);
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
lean_inc(v_a_3648_);
lean_dec_ref(v___x_3647_);
if (v_reportPositions_3641_ == 0)
{
lean_object* v_fst_3649_; lean_object* v_snd_3650_; lean_object* v___x_3651_; 
v_fst_3649_ = lean_ctor_get(v_a_3648_, 0);
lean_inc(v_fst_3649_);
v_snd_3650_ = lean_ctor_get(v_a_3648_, 1);
lean_inc(v_snd_3650_);
lean_dec(v_a_3648_);
v___x_3651_ = lean_box(0);
v___y_3580_ = v___y_3621_;
v___y_3581_ = v_whitespace_3639_;
v___y_3582_ = v_substring_3642_;
v___y_3583_ = v___y_3622_;
v___y_3584_ = v_ordering_3640_;
v___y_3585_ = v___x_3627_;
v___y_3586_ = v_a_3644_;
v___y_3587_ = v___x_3635_;
v___y_3588_ = v_snd_3650_;
v___y_3589_ = v_fst_3649_;
v___y_3590_ = v___y_3624_;
v___y_3591_ = v___x_3651_;
goto v___jp_3579_;
}
else
{
lean_object* v_fst_3652_; lean_object* v_snd_3653_; uint8_t v___x_3654_; lean_object* v___x_3655_; 
v_fst_3652_ = lean_ctor_get(v_a_3648_, 0);
lean_inc(v_fst_3652_);
v_snd_3653_ = lean_ctor_get(v_a_3648_, 1);
lean_inc(v_snd_3653_);
lean_dec(v_a_3648_);
v___x_3654_ = 0;
v___x_3655_ = l_Lean_Syntax_getPos_x3f(v___y_3624_, v___x_3654_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_box(0);
v___y_3580_ = v___y_3621_;
v___y_3581_ = v_whitespace_3639_;
v___y_3582_ = v_substring_3642_;
v___y_3583_ = v___y_3622_;
v___y_3584_ = v_ordering_3640_;
v___y_3585_ = v___x_3627_;
v___y_3586_ = v_a_3644_;
v___y_3587_ = v___x_3635_;
v___y_3588_ = v_snd_3653_;
v___y_3589_ = v_fst_3652_;
v___y_3590_ = v___y_3624_;
v___y_3591_ = v___x_3656_;
goto v___jp_3579_;
}
else
{
lean_object* v_val_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3667_; 
v_val_3657_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3659_ = v___x_3655_;
v_isShared_3660_ = v_isSharedCheck_3667_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_val_3657_);
lean_dec(v___x_3655_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3667_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v_fileMap_3661_; lean_object* v___x_3662_; lean_object* v_line_3663_; lean_object* v___x_3665_; 
v_fileMap_3661_ = lean_ctor_get(v___y_3622_, 1);
lean_inc_ref(v_fileMap_3661_);
v___x_3662_ = l_Lean_FileMap_toPosition(v_fileMap_3661_, v_val_3657_);
lean_dec(v_val_3657_);
v_line_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_line_3663_);
lean_dec_ref(v___x_3662_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 0, v_line_3663_);
v___x_3665_ = v___x_3659_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_line_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
v___y_3580_ = v___y_3621_;
v___y_3581_ = v_whitespace_3639_;
v___y_3582_ = v_substring_3642_;
v___y_3583_ = v___y_3622_;
v___y_3584_ = v_ordering_3640_;
v___y_3585_ = v___x_3627_;
v___y_3586_ = v_a_3644_;
v___y_3587_ = v___x_3635_;
v___y_3588_ = v_snd_3653_;
v___y_3589_ = v_fst_3652_;
v___y_3590_ = v___y_3624_;
v___y_3591_ = v___x_3665_;
goto v___jp_3579_;
}
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec_ref(v_filterFn_3638_);
lean_dec_ref(v___x_3635_);
lean_dec(v___y_3624_);
v_a_3668_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3643_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3643_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec_ref(v___x_3635_);
lean_dec(v___y_3625_);
lean_dec(v___y_3624_);
v_a_3676_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3636_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3636_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
v___jp_3684_:
{
if (lean_obj_tag(v___y_3687_) == 0)
{
lean_object* v___x_3691_; 
v___x_3691_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_3621_ = v___y_3685_;
v___y_3622_ = v___y_3686_;
v___y_3623_ = v___y_3690_;
v___y_3624_ = v___y_3688_;
v___y_3625_ = v___y_3689_;
v___y_3626_ = v___x_3691_;
goto v___jp_3620_;
}
else
{
lean_object* v_val_3692_; lean_object* v___x_3693_; 
v_val_3692_ = lean_ctor_get(v___y_3687_, 0);
lean_inc(v_val_3692_);
lean_dec_ref_known(v___y_3687_, 1);
v___x_3693_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3692_, v___y_3686_, v___y_3685_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
v___y_3621_ = v___y_3685_;
v___y_3622_ = v___y_3686_;
v___y_3623_ = v___y_3690_;
v___y_3624_ = v___y_3688_;
v___y_3625_ = v___y_3689_;
v___y_3626_ = v_a_3694_;
goto v___jp_3620_;
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec(v___y_3688_);
v_a_3695_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3693_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3693_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
v___jp_3703_:
{
lean_object* v___x_3707_; lean_object* v_tk_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3707_ = lean_unsigned_to_nat(1u);
v_tk_3708_ = l_Lean_Syntax_getArg(v_x_3467_, v___x_3707_);
v___x_3709_ = lean_unsigned_to_nat(2u);
v___x_3710_ = l_Lean_Syntax_getArg(v_x_3467_, v___x_3709_);
v___x_3711_ = lean_unsigned_to_nat(4u);
v___x_3712_ = l_Lean_Syntax_getArg(v_x_3467_, v___x_3711_);
lean_dec(v_x_3467_);
v___x_3713_ = l_Lean_Syntax_getOptional_x3f(v___x_3710_);
lean_dec(v___x_3710_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_box(0);
v___y_3685_ = v___y_3706_;
v___y_3686_ = v___y_3705_;
v___y_3687_ = v_dc_x3f_3704_;
v___y_3688_ = v_tk_3708_;
v___y_3689_ = v___x_3712_;
v___y_3690_ = v___x_3714_;
goto v___jp_3684_;
}
else
{
lean_object* v_val_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
v_val_3715_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3713_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_val_3715_);
lean_dec(v___x_3713_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_val_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
v___y_3685_ = v___y_3706_;
v___y_3686_ = v___y_3705_;
v___y_3687_ = v_dc_x3f_3704_;
v___y_3688_ = v_tk_3708_;
v___y_3689_ = v___x_3712_;
v___y_3690_ = v___x_3720_;
goto v___jp_3684_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3735_, v_a_3736_, v_a_3737_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3740_, lean_object* v_as_3741_, lean_object* v_as_x27_3742_, lean_object* v_b_3743_, lean_object* v_a_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3740_, v_as_x27_3742_, v_b_3743_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3749_, lean_object* v_as_3750_, lean_object* v_as_x27_3751_, lean_object* v_b_3752_, lean_object* v_a_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3749_, v_as_3750_, v_as_x27_3751_, v_b_3752_, v_a_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v_as_x27_3751_);
lean_dec(v_as_3750_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3758_, lean_object* v_x_3759_, lean_object* v_x_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3758_, v_x_3759_, v_x_3760_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3765_, lean_object* v_x_3766_, lean_object* v_x_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3765_, v_x_3766_, v_x_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3765_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3772_, v___y_3774_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3782_, lean_object* v___x_3783_, lean_object* v___x_3784_, lean_object* v_inst_3785_, lean_object* v_R_3786_, lean_object* v_a_3787_, lean_object* v_b_3788_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3782_, v___x_3783_, v___x_3784_, v_a_3787_, v_b_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3790_, lean_object* v___x_3791_, lean_object* v___x_3792_, lean_object* v_inst_3793_, lean_object* v_R_3794_, lean_object* v_a_3795_, lean_object* v_b_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3790_, v___x_3791_, v___x_3792_, v_inst_3793_, v_R_3794_, v_a_3795_, v_b_3796_);
lean_dec_ref(v___x_3791_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3798_, v___y_3800_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3808_, lean_object* v___x_3809_, lean_object* v___x_3810_, lean_object* v_inst_3811_, lean_object* v_R_3812_, lean_object* v_a_3813_, lean_object* v_b_3814_){
_start:
{
lean_object* v___x_3815_; 
v___x_3815_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3808_, v___x_3809_, v___x_3810_, v_a_3813_, v_b_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3816_, lean_object* v___x_3817_, lean_object* v___x_3818_, lean_object* v_inst_3819_, lean_object* v_R_3820_, lean_object* v_a_3821_, lean_object* v_b_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3816_, v___x_3817_, v___x_3818_, v_inst_3819_, v_R_3820_, v_a_3821_, v_b_3822_);
lean_dec_ref(v___x_3817_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v___x_3824_, lean_object* v_original_3825_, lean_object* v_a_3826_, lean_object* v_inst_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_3824_, v_original_3825_, v_a_3826_, v_a_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___boxed(lean_object* v___x_3830_, lean_object* v_original_3831_, lean_object* v_a_3832_, lean_object* v_inst_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3830_, v_original_3831_, v_a_3832_, v_inst_3833_, v_a_3834_);
lean_dec_ref(v_a_3832_);
lean_dec_ref(v_original_3831_);
lean_dec(v___x_3830_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v___x_3836_, lean_object* v_edited_3837_, lean_object* v_a_3838_, lean_object* v_inst_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_3836_, v_edited_3837_, v_a_3838_, v_a_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v___x_3842_, lean_object* v_edited_3843_, lean_object* v_a_3844_, lean_object* v_inst_3845_, lean_object* v_a_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v___x_3842_, v_edited_3843_, v_a_3844_, v_inst_3845_, v_a_3846_);
lean_dec_ref(v_a_3844_);
lean_dec_ref(v_edited_3843_);
lean_dec(v___x_3842_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3848_, lean_object* v_original_3849_, lean_object* v_inst_3850_, lean_object* v_a_3851_){
_start:
{
lean_object* v___x_3852_; 
v___x_3852_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3848_, v_original_3849_, v_a_3851_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3853_, lean_object* v_original_3854_, lean_object* v_inst_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3853_, v_original_3854_, v_inst_3855_, v_a_3856_);
lean_dec_ref(v_original_3854_);
lean_dec(v___x_3853_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3858_, lean_object* v_edited_3859_, lean_object* v_inst_3860_, lean_object* v_a_3861_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3858_, v_edited_3859_, v_a_3861_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3863_, lean_object* v_edited_3864_, lean_object* v_inst_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3863_, v_edited_3864_, v_inst_3865_, v_a_3866_);
lean_dec_ref(v_edited_3864_);
lean_dec(v___x_3863_);
return v_res_3867_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3868_, lean_object* v_inst_3869_, lean_object* v_R_3870_, lean_object* v_a_3871_, uint8_t v_b_3872_, lean_object* v_c_3873_){
_start:
{
uint8_t v___x_3874_; 
v___x_3874_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3868_, v_a_3871_, v_b_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3875_, lean_object* v_inst_3876_, lean_object* v_R_3877_, lean_object* v_a_3878_, lean_object* v_b_3879_, lean_object* v_c_3880_){
_start:
{
uint8_t v_b_boxed_3881_; uint8_t v_res_3882_; lean_object* v_r_3883_; 
v_b_boxed_3881_ = lean_unbox(v_b_3879_);
v_res_3882_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3875_, v_inst_3876_, v_R_3877_, v_a_3878_, v_b_boxed_3881_, v_c_3880_);
lean_dec_ref(v_s_3875_);
v_r_3883_ = lean_box(v_res_3882_);
return v_r_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3884_, lean_object* v_ref_3885_, lean_object* v_msg_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3885_, v_msg_3886_, v___y_3887_, v___y_3888_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3891_, lean_object* v_ref_3892_, lean_object* v_msg_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3891_, v_ref_3892_, v_msg_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v_ref_3892_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(lean_object* v_as_3898_, lean_object* v_as_x27_3899_, lean_object* v_b_3900_, lean_object* v_a_3901_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3899_, v_b_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___boxed(lean_object* v_as_3903_, lean_object* v_as_x27_3904_, lean_object* v_b_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(v_as_3903_, v_as_x27_3904_, v_b_3905_, v_a_3906_);
lean_dec(v_as_x27_3904_);
lean_dec(v_as_3903_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(lean_object* v_lsize_3908_, lean_object* v_rsize_3909_, lean_object* v_histogram_3910_, lean_object* v_index_3911_, lean_object* v_val_3912_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_histogram_3910_, v_index_3911_, v_val_3912_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___boxed(lean_object* v_lsize_3914_, lean_object* v_rsize_3915_, lean_object* v_histogram_3916_, lean_object* v_index_3917_, lean_object* v_val_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(v_lsize_3914_, v_rsize_3915_, v_histogram_3916_, v_index_3917_, v_val_3918_);
lean_dec(v_rsize_3915_);
lean_dec(v_lsize_3914_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(lean_object* v_upperBound_3920_, lean_object* v___x_3921_, lean_object* v_fst_3922_, lean_object* v___x_3923_, lean_object* v_inst_3924_, lean_object* v_R_3925_, lean_object* v_a_3926_, lean_object* v_b_3927_, lean_object* v_c_3928_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3920_, v___x_3921_, v_fst_3922_, v___x_3923_, v_a_3926_, v_b_3927_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___boxed(lean_object* v_upperBound_3930_, lean_object* v___x_3931_, lean_object* v_fst_3932_, lean_object* v___x_3933_, lean_object* v_inst_3934_, lean_object* v_R_3935_, lean_object* v_a_3936_, lean_object* v_b_3937_, lean_object* v_c_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(v_upperBound_3930_, v___x_3931_, v_fst_3932_, v___x_3933_, v_inst_3934_, v_R_3935_, v_a_3936_, v_b_3937_, v_c_3938_);
lean_dec(v___x_3933_);
lean_dec_ref(v_fst_3932_);
lean_dec(v___x_3931_);
lean_dec(v_upperBound_3930_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(lean_object* v_lsize_3940_, lean_object* v_rsize_3941_, lean_object* v_histogram_3942_, lean_object* v_index_3943_, lean_object* v_val_3944_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_histogram_3942_, v_index_3943_, v_val_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___boxed(lean_object* v_lsize_3946_, lean_object* v_rsize_3947_, lean_object* v_histogram_3948_, lean_object* v_index_3949_, lean_object* v_val_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(v_lsize_3946_, v_rsize_3947_, v_histogram_3948_, v_index_3949_, v_val_3950_);
lean_dec(v_rsize_3947_);
lean_dec(v_lsize_3946_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(lean_object* v_upperBound_3952_, lean_object* v_fst_3953_, lean_object* v___x_3954_, lean_object* v_fst_3955_, lean_object* v_inst_3956_, lean_object* v_R_3957_, lean_object* v_a_3958_, lean_object* v_b_3959_, lean_object* v_c_3960_){
_start:
{
lean_object* v___x_3961_; 
v___x_3961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3952_, v_fst_3953_, v___x_3954_, v_fst_3955_, v_a_3958_, v_b_3959_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___boxed(lean_object* v_upperBound_3962_, lean_object* v_fst_3963_, lean_object* v___x_3964_, lean_object* v_fst_3965_, lean_object* v_inst_3966_, lean_object* v_R_3967_, lean_object* v_a_3968_, lean_object* v_b_3969_, lean_object* v_c_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(v_upperBound_3962_, v_fst_3963_, v___x_3964_, v_fst_3965_, v_inst_3966_, v_R_3967_, v_a_3968_, v_b_3969_, v_c_3970_);
lean_dec_ref(v_fst_3965_);
lean_dec(v___x_3964_);
lean_dec_ref(v_fst_3963_);
lean_dec(v_upperBound_3962_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_3972_, lean_object* v_msg_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v___x_3977_; 
v___x_3977_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_3973_, v___y_3974_, v___y_3975_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_3978_, lean_object* v_msg_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_3978_, v_msg_3979_, v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(lean_object* v_00_u03b2_3984_, lean_object* v_m_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_3985_, v_a_3986_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3988_, lean_object* v_m_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(v_00_u03b2_3988_, v_m_3989_, v_a_3990_);
lean_dec_ref(v_a_3990_);
lean_dec_ref(v_m_3989_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26(lean_object* v_00_u03b2_3992_, lean_object* v_m_3993_, lean_object* v_a_3994_, lean_object* v_b_3995_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_m_3993_, v_a_3994_, v_b_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_3997_, lean_object* v_macroStack_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_3997_, v_macroStack_3998_, v___y_4000_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4003_, lean_object* v_macroStack_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4003_, v_macroStack_4004_, v___y_4005_, v___y_4006_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29(lean_object* v_inst_4009_, lean_object* v_R_4010_, lean_object* v_a_4011_, lean_object* v_b_4012_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v_a_4011_, v_b_4012_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(lean_object* v_00_u03b2_4014_, lean_object* v_a_4015_, lean_object* v_x_4016_){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_4015_, v_x_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___boxed(lean_object* v_00_u03b2_4018_, lean_object* v_a_4019_, lean_object* v_x_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(v_00_u03b2_4018_, v_a_4019_, v_x_4020_);
lean_dec(v_x_4020_);
lean_dec_ref(v_a_4019_);
return v_res_4021_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(lean_object* v_00_u03b2_4022_, lean_object* v_a_4023_, lean_object* v_x_4024_){
_start:
{
uint8_t v___x_4025_; 
v___x_4025_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_4023_, v_x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___boxed(lean_object* v_00_u03b2_4026_, lean_object* v_a_4027_, lean_object* v_x_4028_){
_start:
{
uint8_t v_res_4029_; lean_object* v_r_4030_; 
v_res_4029_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(v_00_u03b2_4026_, v_a_4027_, v_x_4028_);
lean_dec(v_x_4028_);
lean_dec_ref(v_a_4027_);
v_r_4030_ = lean_box(v_res_4029_);
return v_r_4030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38(lean_object* v_00_u03b2_4031_, lean_object* v_data_4032_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_data_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39(lean_object* v_00_u03b2_4034_, lean_object* v_a_4035_, lean_object* v_b_4036_, lean_object* v_x_4037_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_4035_, v_b_4036_, v_x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44(lean_object* v_00_u03b2_4039_, lean_object* v_i_4040_, lean_object* v_source_4041_, lean_object* v_target_4042_){
_start:
{
lean_object* v___x_4043_; 
v___x_4043_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v_i_4040_, v_source_4041_, v_target_4042_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4044_, lean_object* v_x_4045_, lean_object* v_x_4046_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_x_4045_, v_x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4056_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4057_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
v___x_4058_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4059_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4060_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4056_, v___x_4057_, v___x_4058_, v___x_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4089_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4090_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4091_ = l_Lean_addBuiltinDeclarationRanges(v___x_4089_, v___x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4094_){
_start:
{
lean_object* v_doc_4096_; lean_object* v___x_4097_; 
v_doc_4096_ = lean_ctor_get(v___y_4094_, 1);
lean_inc_ref(v_doc_4096_);
v___x_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4097_, 0, v_doc_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4098_);
lean_dec_ref(v___y_4098_);
return v_res_4100_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4101_, lean_object* v_a_4102_, uint8_t v_b_4103_){
_start:
{
lean_object* v_str_4104_; lean_object* v_startInclusive_4105_; lean_object* v_endExclusive_4106_; lean_object* v___x_4107_; uint8_t v_decide_4108_; 
v_str_4104_ = lean_ctor_get(v_s_4101_, 0);
v_startInclusive_4105_ = lean_ctor_get(v_s_4101_, 1);
v_endExclusive_4106_ = lean_ctor_get(v_s_4101_, 2);
v___x_4107_ = lean_nat_sub(v_endExclusive_4106_, v_startInclusive_4105_);
v_decide_4108_ = lean_nat_dec_eq(v_a_4102_, v___x_4107_);
lean_dec(v___x_4107_);
if (v_decide_4108_ == 0)
{
lean_object* v___x_4109_; uint32_t v___x_4110_; uint32_t v___x_4111_; uint8_t v___x_4112_; 
v___x_4109_ = lean_nat_add(v_startInclusive_4105_, v_a_4102_);
lean_dec(v_a_4102_);
v___x_4110_ = lean_string_utf8_get_fast(v_str_4104_, v___x_4109_);
v___x_4111_ = 10;
v___x_4112_ = lean_uint32_dec_eq(v___x_4110_, v___x_4111_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = lean_string_utf8_next_fast(v_str_4104_, v___x_4109_);
lean_dec(v___x_4109_);
v___x_4114_ = lean_nat_sub(v___x_4113_, v_startInclusive_4105_);
v_a_4102_ = v___x_4114_;
v_b_4103_ = v___x_4112_;
goto _start;
}
else
{
lean_dec(v___x_4109_);
return v___x_4112_;
}
}
else
{
lean_dec(v_a_4102_);
return v_b_4103_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4116_, lean_object* v_a_4117_, lean_object* v_b_4118_){
_start:
{
uint8_t v_b_boxed_4119_; uint8_t v_res_4120_; lean_object* v_r_4121_; 
v_b_boxed_4119_ = lean_unbox(v_b_4118_);
v_res_4120_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4116_, v_a_4117_, v_b_boxed_4119_);
lean_dec_ref(v_s_4116_);
v_r_4121_ = lean_box(v_res_4120_);
return v_r_4121_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4122_){
_start:
{
lean_object* v_searcher_4123_; uint8_t v___x_4124_; uint8_t v___x_4125_; 
v_searcher_4123_ = lean_unsigned_to_nat(0u);
v___x_4124_ = 0;
v___x_4125_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4122_, v_searcher_4123_, v___x_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4126_){
_start:
{
uint8_t v_res_4127_; lean_object* v_r_4128_; 
v_res_4127_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4126_);
lean_dec_ref(v_s_4126_);
v_r_4128_ = lean_box(v_res_4127_);
return v_r_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4140_, lean_object* v_fst_4141_, uint8_t v___x_4142_, lean_object* v_a_4143_, lean_object* v___x_4144_, lean_object* v___x_4145_, lean_object* v___x_4146_, lean_object* v___x_4147_, lean_object* v___x_4148_, lean_object* v___x_4149_, lean_object* v___x_4150_, lean_object* v___x_4151_, lean_object* v_snd_4152_, lean_object* v___x_4153_){
_start:
{
if (lean_obj_tag(v___x_4140_) == 1)
{
lean_object* v_val_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4216_; 
v_val_4155_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4157_ = v___x_4140_;
v_isShared_4158_ = v_isSharedCheck_4216_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_val_4155_);
lean_dec(v___x_4140_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4216_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4159_ = lean_unsigned_to_nat(0u);
v___x_4160_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4161_ = l_Lean_Syntax_setArg(v_fst_4141_, v___x_4159_, v___x_4160_);
v___x_4162_ = l_Lean_Syntax_getPos_x3f(v___x_4161_, v___x_4142_);
lean_dec(v___x_4161_);
if (lean_obj_tag(v___x_4162_) == 1)
{
lean_object* v_val_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4212_; 
lean_dec_ref(v___x_4153_);
v_val_4163_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4165_ = v___x_4162_;
v_isShared_4166_ = v_isSharedCheck_4212_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_val_4163_);
lean_dec(v___x_4162_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4212_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___y_4168_; lean_object* v___x_4194_; lean_object* v___x_4200_; uint8_t v___x_4201_; 
v___x_4194_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4152_);
v___x_4200_ = lean_string_utf8_byte_size(v___x_4194_);
v___x_4201_ = lean_nat_dec_eq(v___x_4200_, v___x_4159_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4202_; lean_object* v___x_4203_; uint8_t v___x_4204_; 
v___x_4202_ = lean_string_length(v___x_4194_);
v___x_4203_ = lean_unsigned_to_nat(93u);
v___x_4204_ = lean_nat_dec_le(v___x_4202_, v___x_4203_);
if (v___x_4204_ == 0)
{
goto v___jp_4195_;
}
else
{
lean_object* v___x_4205_; uint8_t v___x_4206_; 
lean_inc_ref(v___x_4194_);
v___x_4205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4194_);
lean_ctor_set(v___x_4205_, 1, v___x_4159_);
lean_ctor_set(v___x_4205_, 2, v___x_4200_);
v___x_4206_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4205_);
lean_dec_ref_known(v___x_4205_, 3);
if (v___x_4206_ == 0)
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4207_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4208_ = lean_string_append(v___x_4207_, v___x_4194_);
lean_dec_ref(v___x_4194_);
v___x_4209_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4210_ = lean_string_append(v___x_4208_, v___x_4209_);
v___y_4168_ = v___x_4210_;
goto v___jp_4167_;
}
else
{
goto v___jp_4195_;
}
}
}
else
{
lean_object* v___x_4211_; 
lean_dec_ref(v___x_4194_);
v___x_4211_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_4168_ = v___x_4211_;
goto v___jp_4167_;
}
v___jp_4167_:
{
lean_object* v_toEditableDocumentCore_4169_; lean_object* v_meta_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4190_; 
v_toEditableDocumentCore_4169_ = lean_ctor_get(v_a_4143_, 0);
lean_inc_ref(v_toEditableDocumentCore_4169_);
v_meta_4170_ = lean_ctor_get(v_toEditableDocumentCore_4169_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_toEditableDocumentCore_4169_);
if (v_isSharedCheck_4190_ == 0)
{
lean_object* v_unused_4191_; lean_object* v_unused_4192_; lean_object* v_unused_4193_; 
v_unused_4191_ = lean_ctor_get(v_toEditableDocumentCore_4169_, 3);
lean_dec(v_unused_4191_);
v_unused_4192_ = lean_ctor_get(v_toEditableDocumentCore_4169_, 2);
lean_dec(v_unused_4192_);
v_unused_4193_ = lean_ctor_get(v_toEditableDocumentCore_4169_, 1);
lean_dec(v_unused_4193_);
v___x_4172_ = v_toEditableDocumentCore_4169_;
v_isShared_4173_ = v_isSharedCheck_4190_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_meta_4170_);
lean_dec(v_toEditableDocumentCore_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4190_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v_text_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4180_; 
v_text_4174_ = lean_ctor_get(v_meta_4170_, 3);
lean_inc_ref(v_text_4174_);
lean_dec_ref(v_meta_4170_);
v___x_4175_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4143_);
v___x_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4176_, 0, v_val_4155_);
lean_ctor_set(v___x_4176_, 1, v_val_4163_);
v___x_4177_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4174_, v___x_4176_);
v___x_4178_ = lean_box(0);
lean_inc(v___x_4144_);
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 3, v___x_4144_);
lean_ctor_set(v___x_4172_, 2, v___x_4178_);
lean_ctor_set(v___x_4172_, 1, v___y_4168_);
lean_ctor_set(v___x_4172_, 0, v___x_4177_);
v___x_4180_ = v___x_4172_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4189_, 1, v___y_4168_);
lean_ctor_set(v_reuseFailAlloc_4189_, 2, v___x_4178_);
lean_ctor_set(v_reuseFailAlloc_4189_, 3, v___x_4144_);
v___x_4180_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4181_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4175_, v___x_4180_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4181_);
v___x_4183_ = v___x_4165_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4184_; lean_object* v___x_4186_; 
lean_inc(v___x_4144_);
v___x_4184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4144_);
lean_ctor_set(v___x_4184_, 1, v___x_4144_);
lean_ctor_set(v___x_4184_, 2, v___x_4145_);
lean_ctor_set(v___x_4184_, 3, v___x_4146_);
lean_ctor_set(v___x_4184_, 4, v___x_4147_);
lean_ctor_set(v___x_4184_, 5, v___x_4148_);
lean_ctor_set(v___x_4184_, 6, v___x_4149_);
lean_ctor_set(v___x_4184_, 7, v___x_4183_);
lean_ctor_set(v___x_4184_, 8, v___x_4150_);
lean_ctor_set(v___x_4184_, 9, v___x_4151_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set_tag(v___x_4157_, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4184_);
v___x_4186_ = v___x_4157_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4184_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
v___jp_4195_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4196_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4197_ = lean_string_append(v___x_4196_, v___x_4194_);
lean_dec_ref(v___x_4194_);
v___x_4198_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4199_ = lean_string_append(v___x_4197_, v___x_4198_);
v___y_4168_ = v___x_4199_;
goto v___jp_4167_;
}
}
}
else
{
lean_object* v___x_4214_; 
lean_dec(v___x_4162_);
lean_dec(v_val_4155_);
lean_dec_ref(v_snd_4152_);
lean_dec(v___x_4151_);
lean_dec(v___x_4150_);
lean_dec(v___x_4149_);
lean_dec(v___x_4148_);
lean_dec(v___x_4147_);
lean_dec(v___x_4146_);
lean_dec_ref(v___x_4145_);
lean_dec(v___x_4144_);
lean_dec_ref(v_a_4143_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set_tag(v___x_4157_, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4153_);
v___x_4214_ = v___x_4157_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v___x_4153_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
else
{
lean_object* v___x_4217_; 
lean_dec_ref(v_snd_4152_);
lean_dec(v___x_4151_);
lean_dec(v___x_4150_);
lean_dec(v___x_4149_);
lean_dec(v___x_4148_);
lean_dec(v___x_4147_);
lean_dec(v___x_4146_);
lean_dec_ref(v___x_4145_);
lean_dec(v___x_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_fst_4141_);
lean_dec(v___x_4140_);
v___x_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4153_);
return v___x_4217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4218_, lean_object* v_fst_4219_, lean_object* v___x_4220_, lean_object* v_a_4221_, lean_object* v___x_4222_, lean_object* v___x_4223_, lean_object* v___x_4224_, lean_object* v___x_4225_, lean_object* v___x_4226_, lean_object* v___x_4227_, lean_object* v___x_4228_, lean_object* v___x_4229_, lean_object* v_snd_4230_, lean_object* v___x_4231_, lean_object* v___y_4232_){
_start:
{
uint8_t v___x_4482__boxed_4233_; lean_object* v_res_4234_; 
v___x_4482__boxed_4233_ = lean_unbox(v___x_4220_);
v_res_4234_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4218_, v_fst_4219_, v___x_4482__boxed_4233_, v_a_4221_, v___x_4222_, v___x_4223_, v___x_4224_, v___x_4225_, v___x_4226_, v___x_4227_, v___x_4228_, v___x_4229_, v_snd_4230_, v___x_4231_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4238_, size_t v_sz_4239_, size_t v_i_4240_, lean_object* v_b_4241_){
_start:
{
lean_object* v_a_4243_; uint8_t v___x_4247_; 
v___x_4247_ = lean_usize_dec_lt(v_i_4240_, v_sz_4239_);
if (v___x_4247_ == 0)
{
lean_inc_ref(v_b_4241_);
return v_b_4241_;
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v_a_4250_; 
v___x_4248_ = lean_box(0);
v___x_4249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4250_ = lean_array_uget(v_as_4238_, v_i_4240_);
if (lean_obj_tag(v_a_4250_) == 1)
{
lean_object* v_i_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4285_; 
v_i_4251_ = lean_ctor_get(v_a_4250_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v_a_4250_);
if (v_isSharedCheck_4285_ == 0)
{
lean_object* v_unused_4286_; 
v_unused_4286_ = lean_ctor_get(v_a_4250_, 1);
lean_dec(v_unused_4286_);
v___x_4253_ = v_a_4250_;
v_isShared_4254_ = v_isSharedCheck_4285_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_i_4251_);
lean_dec(v_a_4250_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4285_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
if (lean_obj_tag(v_i_4251_) == 10)
{
lean_object* v_i_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4284_; 
v_i_4255_ = lean_ctor_get(v_i_4251_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v_i_4251_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4257_ = v_i_4251_;
v_isShared_4258_ = v_isSharedCheck_4284_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_i_4255_);
lean_dec(v_i_4251_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4284_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v_stx_4259_; lean_object* v_value_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4283_; 
v_stx_4259_ = lean_ctor_get(v_i_4255_, 0);
v_value_4260_ = lean_ctor_get(v_i_4255_, 1);
v_isSharedCheck_4283_ = !lean_is_exclusive(v_i_4255_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4262_ = v_i_4255_;
v_isShared_4263_ = v_isSharedCheck_4283_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_value_4260_);
lean_inc(v_stx_4259_);
lean_dec(v_i_4255_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4283_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4264_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4265_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4260_, v___x_4264_);
lean_dec(v_value_4260_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_del_object(v___x_4262_);
lean_dec(v_stx_4259_);
lean_del_object(v___x_4257_);
lean_del_object(v___x_4253_);
v_a_4243_ = v___x_4249_;
goto v___jp_4242_;
}
else
{
lean_object* v_val_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4282_; 
v_val_4266_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4268_ = v___x_4265_;
v_isShared_4269_ = v_isSharedCheck_4282_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_val_4266_);
lean_dec(v___x_4265_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4282_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 1, v_val_4266_);
v___x_4271_ = v___x_4262_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_stx_4259_);
lean_ctor_set(v_reuseFailAlloc_4281_, 1, v_val_4266_);
v___x_4271_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
lean_object* v___x_4273_; 
if (v_isShared_4269_ == 0)
{
lean_ctor_set(v___x_4268_, 0, v___x_4271_);
v___x_4273_ = v___x_4268_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4271_);
v___x_4273_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
lean_object* v___x_4275_; 
if (v_isShared_4258_ == 0)
{
lean_ctor_set_tag(v___x_4257_, 1);
lean_ctor_set(v___x_4257_, 0, v___x_4273_);
v___x_4275_ = v___x_4257_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4273_);
v___x_4275_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
lean_object* v___x_4277_; 
if (v_isShared_4254_ == 0)
{
lean_ctor_set_tag(v___x_4253_, 0);
lean_ctor_set(v___x_4253_, 1, v___x_4248_);
lean_ctor_set(v___x_4253_, 0, v___x_4275_);
v___x_4277_ = v___x_4253_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4275_);
lean_ctor_set(v_reuseFailAlloc_4278_, 1, v___x_4248_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
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
lean_del_object(v___x_4253_);
lean_dec_ref(v_i_4251_);
v_a_4243_ = v___x_4249_;
goto v___jp_4242_;
}
}
}
else
{
lean_dec(v_a_4250_);
v_a_4243_ = v___x_4249_;
goto v___jp_4242_;
}
}
v___jp_4242_:
{
size_t v___x_4244_; size_t v___x_4245_; 
v___x_4244_ = ((size_t)1ULL);
v___x_4245_ = lean_usize_add(v_i_4240_, v___x_4244_);
v_i_4240_ = v___x_4245_;
v_b_4241_ = v_a_4243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4287_, lean_object* v_sz_4288_, lean_object* v_i_4289_, lean_object* v_b_4290_){
_start:
{
size_t v_sz_boxed_4291_; size_t v_i_boxed_4292_; lean_object* v_res_4293_; 
v_sz_boxed_4291_ = lean_unbox_usize(v_sz_4288_);
lean_dec(v_sz_4288_);
v_i_boxed_4292_ = lean_unbox_usize(v_i_4289_);
lean_dec(v_i_4289_);
v_res_4293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4287_, v_sz_boxed_4291_, v_i_boxed_4292_, v_b_4290_);
lean_dec_ref(v_b_4290_);
lean_dec_ref(v_as_4287_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4294_, size_t v_sz_4295_, size_t v_i_4296_, lean_object* v_b_4297_){
_start:
{
lean_object* v_a_4299_; uint8_t v___x_4303_; 
v___x_4303_ = lean_usize_dec_lt(v_i_4296_, v_sz_4295_);
if (v___x_4303_ == 0)
{
lean_inc_ref(v_b_4297_);
return v_b_4297_;
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v_a_4306_; 
v___x_4304_ = lean_box(0);
v___x_4305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4306_ = lean_array_uget(v_as_4294_, v_i_4296_);
if (lean_obj_tag(v_a_4306_) == 1)
{
lean_object* v_i_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4341_; 
v_i_4307_ = lean_ctor_get(v_a_4306_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v_a_4306_);
if (v_isSharedCheck_4341_ == 0)
{
lean_object* v_unused_4342_; 
v_unused_4342_ = lean_ctor_get(v_a_4306_, 1);
lean_dec(v_unused_4342_);
v___x_4309_ = v_a_4306_;
v_isShared_4310_ = v_isSharedCheck_4341_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_i_4307_);
lean_dec(v_a_4306_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4341_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
if (lean_obj_tag(v_i_4307_) == 10)
{
lean_object* v_i_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4340_; 
v_i_4311_ = lean_ctor_get(v_i_4307_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_i_4307_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4313_ = v_i_4307_;
v_isShared_4314_ = v_isSharedCheck_4340_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_i_4311_);
lean_dec(v_i_4307_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4340_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v_stx_4315_; lean_object* v_value_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4339_; 
v_stx_4315_ = lean_ctor_get(v_i_4311_, 0);
v_value_4316_ = lean_ctor_get(v_i_4311_, 1);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_i_4311_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4318_ = v_i_4311_;
v_isShared_4319_ = v_isSharedCheck_4339_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_value_4316_);
lean_inc(v_stx_4315_);
lean_dec(v_i_4311_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4339_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4320_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4321_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4316_, v___x_4320_);
lean_dec(v_value_4316_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_del_object(v___x_4318_);
lean_dec(v_stx_4315_);
lean_del_object(v___x_4313_);
lean_del_object(v___x_4309_);
v_a_4299_ = v___x_4305_;
goto v___jp_4298_;
}
else
{
lean_object* v_val_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4338_; 
v_val_4322_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4324_ = v___x_4321_;
v_isShared_4325_ = v_isSharedCheck_4338_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_val_4322_);
lean_dec(v___x_4321_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4338_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 1, v_val_4322_);
v___x_4327_ = v___x_4318_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_stx_4315_);
lean_ctor_set(v_reuseFailAlloc_4337_, 1, v_val_4322_);
v___x_4327_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
lean_object* v___x_4329_; 
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 0, v___x_4327_);
v___x_4329_ = v___x_4324_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4327_);
v___x_4329_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4331_; 
if (v_isShared_4314_ == 0)
{
lean_ctor_set_tag(v___x_4313_, 1);
lean_ctor_set(v___x_4313_, 0, v___x_4329_);
v___x_4331_ = v___x_4313_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4329_);
v___x_4331_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
lean_object* v___x_4333_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set_tag(v___x_4309_, 0);
lean_ctor_set(v___x_4309_, 1, v___x_4304_);
lean_ctor_set(v___x_4309_, 0, v___x_4331_);
v___x_4333_ = v___x_4309_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4331_);
lean_ctor_set(v_reuseFailAlloc_4334_, 1, v___x_4304_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
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
lean_del_object(v___x_4309_);
lean_dec_ref(v_i_4307_);
v_a_4299_ = v___x_4305_;
goto v___jp_4298_;
}
}
}
else
{
lean_dec(v_a_4306_);
v_a_4299_ = v___x_4305_;
goto v___jp_4298_;
}
}
v___jp_4298_:
{
size_t v___x_4300_; size_t v___x_4301_; lean_object* v___x_4302_; 
v___x_4300_ = ((size_t)1ULL);
v___x_4301_ = lean_usize_add(v_i_4296_, v___x_4300_);
v___x_4302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4294_, v_sz_4295_, v___x_4301_, v_a_4299_);
return v___x_4302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4343_, lean_object* v_sz_4344_, lean_object* v_i_4345_, lean_object* v_b_4346_){
_start:
{
size_t v_sz_boxed_4347_; size_t v_i_boxed_4348_; lean_object* v_res_4349_; 
v_sz_boxed_4347_ = lean_unbox_usize(v_sz_4344_);
lean_dec(v_sz_4344_);
v_i_boxed_4348_ = lean_unbox_usize(v_i_4345_);
lean_dec(v_i_4345_);
v_res_4349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4343_, v_sz_boxed_4347_, v_i_boxed_4348_, v_b_4346_);
lean_dec_ref(v_b_4346_);
lean_dec_ref(v_as_4343_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4350_){
_start:
{
if (lean_obj_tag(v_x_4350_) == 0)
{
lean_object* v_cs_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; size_t v_sz_4354_; size_t v___x_4355_; lean_object* v___x_4356_; lean_object* v_fst_4357_; 
v_cs_4351_ = lean_ctor_get(v_x_4350_, 0);
v___x_4352_ = lean_box(0);
v___x_4353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4354_ = lean_array_size(v_cs_4351_);
v___x_4355_ = ((size_t)0ULL);
v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4351_, v_sz_4354_, v___x_4355_, v___x_4353_);
v_fst_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_fst_4357_);
lean_dec_ref(v___x_4356_);
if (lean_obj_tag(v_fst_4357_) == 0)
{
return v___x_4352_;
}
else
{
lean_object* v_val_4358_; 
v_val_4358_ = lean_ctor_get(v_fst_4357_, 0);
lean_inc(v_val_4358_);
lean_dec_ref_known(v_fst_4357_, 1);
return v_val_4358_;
}
}
else
{
lean_object* v_vs_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; size_t v_sz_4362_; size_t v___x_4363_; lean_object* v___x_4364_; lean_object* v_fst_4365_; 
v_vs_4359_ = lean_ctor_get(v_x_4350_, 0);
v___x_4360_ = lean_box(0);
v___x_4361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4362_ = lean_array_size(v_vs_4359_);
v___x_4363_ = ((size_t)0ULL);
v___x_4364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4359_, v_sz_4362_, v___x_4363_, v___x_4361_);
v_fst_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc(v_fst_4365_);
lean_dec_ref(v___x_4364_);
if (lean_obj_tag(v_fst_4365_) == 0)
{
return v___x_4360_;
}
else
{
lean_object* v_val_4366_; 
v_val_4366_ = lean_ctor_get(v_fst_4365_, 0);
lean_inc(v_val_4366_);
lean_dec_ref_known(v_fst_4365_, 1);
return v_val_4366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4367_, size_t v_sz_4368_, size_t v_i_4369_, lean_object* v_b_4370_){
_start:
{
uint8_t v___x_4371_; 
v___x_4371_ = lean_usize_dec_lt(v_i_4369_, v_sz_4368_);
if (v___x_4371_ == 0)
{
lean_inc_ref(v_b_4370_);
return v_b_4370_;
}
else
{
lean_object* v___x_4372_; lean_object* v_a_4373_; lean_object* v___x_4374_; 
v___x_4372_ = lean_box(0);
v_a_4373_ = lean_array_uget_borrowed(v_as_4367_, v_i_4369_);
v___x_4374_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4373_);
if (lean_obj_tag(v___x_4374_) == 1)
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4374_);
v___x_4376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
lean_ctor_set(v___x_4376_, 1, v___x_4372_);
return v___x_4376_;
}
else
{
lean_object* v___x_4377_; size_t v___x_4378_; size_t v___x_4379_; 
lean_dec(v___x_4374_);
v___x_4377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4378_ = ((size_t)1ULL);
v___x_4379_ = lean_usize_add(v_i_4369_, v___x_4378_);
v_i_4369_ = v___x_4379_;
v_b_4370_ = v___x_4377_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4381_, lean_object* v_sz_4382_, lean_object* v_i_4383_, lean_object* v_b_4384_){
_start:
{
size_t v_sz_boxed_4385_; size_t v_i_boxed_4386_; lean_object* v_res_4387_; 
v_sz_boxed_4385_ = lean_unbox_usize(v_sz_4382_);
lean_dec(v_sz_4382_);
v_i_boxed_4386_ = lean_unbox_usize(v_i_4383_);
lean_dec(v_i_4383_);
v_res_4387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4381_, v_sz_boxed_4385_, v_i_boxed_4386_, v_b_4384_);
lean_dec_ref(v_b_4384_);
lean_dec_ref(v_as_4381_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4388_);
lean_dec_ref(v_x_4388_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4390_){
_start:
{
lean_object* v_root_4391_; lean_object* v_tail_4392_; lean_object* v___x_4393_; 
v_root_4391_ = lean_ctor_get(v_t_4390_, 0);
v_tail_4392_ = lean_ctor_get(v_t_4390_, 1);
v___x_4393_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4391_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v___x_4394_; size_t v_sz_4395_; size_t v___x_4396_; lean_object* v___x_4397_; lean_object* v_fst_4398_; 
v___x_4394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4395_ = lean_array_size(v_tail_4392_);
v___x_4396_ = ((size_t)0ULL);
v___x_4397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4392_, v_sz_4395_, v___x_4396_, v___x_4394_);
v_fst_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_fst_4398_);
lean_dec_ref(v___x_4397_);
if (lean_obj_tag(v_fst_4398_) == 0)
{
return v___x_4393_;
}
else
{
lean_object* v_val_4399_; 
v_val_4399_ = lean_ctor_get(v_fst_4398_, 0);
lean_inc(v_val_4399_);
lean_dec_ref_known(v_fst_4398_, 1);
return v_val_4399_;
}
}
else
{
return v___x_4393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4400_);
lean_dec_ref(v_t_4400_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4416_, lean_object* v_a_4417_){
_start:
{
if (lean_obj_tag(v_node_4416_) == 1)
{
lean_object* v_children_4419_; lean_object* v_res_4420_; 
v_children_4419_ = lean_ctor_get(v_node_4416_, 1);
v_res_4420_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4419_);
if (lean_obj_tag(v_res_4420_) == 1)
{
lean_object* v_val_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4458_; 
v_val_4421_ = lean_ctor_get(v_res_4420_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v_res_4420_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4423_ = v_res_4420_;
v_isShared_4424_ = v_isSharedCheck_4458_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_val_4421_);
lean_dec(v_res_4420_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4458_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v_fst_4425_; lean_object* v_snd_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4457_; 
v_fst_4425_ = lean_ctor_get(v_val_4421_, 0);
v_snd_4426_ = lean_ctor_get(v_val_4421_, 1);
v_isSharedCheck_4457_ = !lean_is_exclusive(v_val_4421_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4428_ = v_val_4421_;
v_isShared_4429_ = v_isSharedCheck_4457_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_snd_4426_);
lean_inc(v_fst_4425_);
lean_dec(v_val_4421_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4457_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4456_; 
v___x_4430_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4417_);
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4433_ = v___x_4430_;
v_isShared_4434_ = v_isSharedCheck_4456_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4430_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4456_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; uint8_t v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___y_4443_; lean_object* v___x_4445_; 
v___x_4435_ = lean_box(0);
v___x_4436_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4437_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4438_ = 1;
v___x_4439_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4440_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4441_ = l_Lean_Syntax_getPos_x3f(v_fst_4425_, v___x_4438_);
v___x_4442_ = lean_box(v___x_4438_);
v___y_4443_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4443_, 0, v___x_4441_);
lean_closure_set(v___y_4443_, 1, v_fst_4425_);
lean_closure_set(v___y_4443_, 2, v___x_4442_);
lean_closure_set(v___y_4443_, 3, v_a_4431_);
lean_closure_set(v___y_4443_, 4, v___x_4435_);
lean_closure_set(v___y_4443_, 5, v___x_4436_);
lean_closure_set(v___y_4443_, 6, v___x_4437_);
lean_closure_set(v___y_4443_, 7, v___x_4435_);
lean_closure_set(v___y_4443_, 8, v___x_4439_);
lean_closure_set(v___y_4443_, 9, v___x_4435_);
lean_closure_set(v___y_4443_, 10, v___x_4435_);
lean_closure_set(v___y_4443_, 11, v___x_4435_);
lean_closure_set(v___y_4443_, 12, v_snd_4426_);
lean_closure_set(v___y_4443_, 13, v___x_4440_);
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 0, v___y_4443_);
v___x_4445_ = v___x_4423_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___y_4443_);
v___x_4445_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v___x_4447_; 
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 1, v___x_4445_);
lean_ctor_set(v___x_4428_, 0, v___x_4440_);
v___x_4447_ = v___x_4428_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4440_);
lean_ctor_set(v_reuseFailAlloc_4454_, 1, v___x_4445_);
v___x_4447_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4452_; 
v___x_4448_ = lean_unsigned_to_nat(1u);
v___x_4449_ = lean_mk_empty_array_with_capacity(v___x_4448_);
v___x_4450_ = lean_array_push(v___x_4449_, v___x_4447_);
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 0, v___x_4450_);
v___x_4452_ = v___x_4433_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4459_; lean_object* v___x_4460_; 
lean_dec(v_res_4420_);
v___x_4459_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4459_);
return v___x_4460_;
}
}
else
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4461_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
return v___x_4462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4463_, v_a_4464_);
lean_dec_ref(v_a_4464_);
lean_dec_ref(v_node_4463_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4467_, lean_object* v_x_4468_, lean_object* v_x_4469_, lean_object* v_node_4470_, lean_object* v_a_4471_){
_start:
{
lean_object* v___x_4473_; 
v___x_4473_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4470_, v_a_4471_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4474_, lean_object* v_x_4475_, lean_object* v_x_4476_, lean_object* v_node_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4474_, v_x_4475_, v_x_4476_, v_node_4477_, v_a_4478_);
lean_dec_ref(v_a_4478_);
lean_dec_ref(v_node_4477_);
lean_dec_ref(v_x_4476_);
lean_dec_ref(v_x_4475_);
lean_dec_ref(v_x_4474_);
return v_res_4480_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4481_, lean_object* v_inst_4482_, lean_object* v_R_4483_, lean_object* v_a_4484_, uint8_t v_b_4485_, lean_object* v_c_4486_){
_start:
{
uint8_t v___x_4487_; 
v___x_4487_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4481_, v_a_4484_, v_b_4485_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4488_, lean_object* v_inst_4489_, lean_object* v_R_4490_, lean_object* v_a_4491_, lean_object* v_b_4492_, lean_object* v_c_4493_){
_start:
{
uint8_t v_b_boxed_4494_; uint8_t v_res_4495_; lean_object* v_r_4496_; 
v_b_boxed_4494_ = lean_unbox(v_b_4492_);
v_res_4495_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4488_, v_inst_4489_, v_R_4490_, v_a_4491_, v_b_boxed_4494_, v_c_4493_);
lean_dec_ref(v_s_4488_);
v_r_4496_ = lean_box(v_res_4495_);
return v_r_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_(){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4502_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_));
v___x_4503_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4504_ = l_Lean_CodeAction_insertBuiltin(v___x_4502_, v___x_4503_);
return v___x_4504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354____boxed(lean_object* v_a_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_();
return v_res_4506_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4512_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4513_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4512_);
return v___x_4513_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4514_ = lean_unsigned_to_nat(0u);
v___x_4515_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
v___x_4516_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4517_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
lean_ctor_set(v___x_4517_, 1, v___x_4515_);
lean_ctor_set(v___x_4517_, 2, v___x_4514_);
lean_ctor_set(v___x_4517_, 3, v___x_4514_);
return v___x_4517_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4518_){
_start:
{
lean_object* v___x_4519_; uint8_t v___x_4520_; uint8_t v___x_4521_; 
v___x_4519_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4520_ = 0;
v___x_4521_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4518_, v___x_4519_, v___x_4520_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4522_){
_start:
{
uint8_t v_res_4523_; lean_object* v_r_4524_; 
v_res_4523_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4522_);
lean_dec_ref(v_s_4522_);
v_r_4524_ = lean_box(v_res_4523_);
return v_r_4524_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4525_, lean_object* v_as_x27_4526_, uint8_t v_b_4527_){
_start:
{
if (lean_obj_tag(v_as_x27_4526_) == 0)
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4529_ = lean_box(v_b_4527_);
v___x_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
return v___x_4530_;
}
else
{
lean_object* v_head_4531_; uint8_t v_isSilent_4532_; 
v_head_4531_ = lean_ctor_get(v_as_x27_4526_, 0);
v_isSilent_4532_ = lean_ctor_get_uint8(v_head_4531_, sizeof(void*)*5 + 2);
if (v_isSilent_4532_ == 0)
{
lean_object* v_tail_4533_; lean_object* v_data_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v_tail_4533_ = lean_ctor_get(v_as_x27_4526_, 1);
v_data_4534_ = lean_ctor_get(v_head_4531_, 4);
lean_inc(v_data_4534_);
v___x_4535_ = l_Lean_MessageData_toString(v_data_4534_);
v___x_4536_ = lean_unsigned_to_nat(0u);
v___x_4537_ = lean_string_utf8_byte_size(v___x_4535_);
v___x_4538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4535_);
lean_ctor_set(v___x_4538_, 1, v___x_4536_);
lean_ctor_set(v___x_4538_, 2, v___x_4537_);
v___x_4539_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4538_);
lean_dec_ref_known(v___x_4538_, 3);
if (v___x_4539_ == 0)
{
v_as_x27_4526_ = v_tail_4533_;
goto _start;
}
else
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = lean_box(v_foundPanic_4525_);
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
else
{
lean_object* v_tail_4543_; 
v_tail_4543_ = lean_ctor_get(v_as_x27_4526_, 1);
v_as_x27_4526_ = v_tail_4543_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4545_, lean_object* v_as_x27_4546_, lean_object* v_b_4547_, lean_object* v___y_4548_){
_start:
{
uint8_t v_foundPanic_boxed_4549_; uint8_t v_b_boxed_4550_; lean_object* v_res_4551_; 
v_foundPanic_boxed_4549_ = lean_unbox(v_foundPanic_4545_);
v_b_boxed_4550_ = lean_unbox(v_b_4547_);
v_res_4551_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4549_, v_as_x27_4546_, v_b_boxed_4550_);
lean_dec(v_as_x27_4546_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4552_, uint8_t v_severity_4553_, uint8_t v_isSilent_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
lean_object* v___x_4558_; 
v___x_4558_ = l_Lean_Elab_Command_getRef___redArg(v___y_4555_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_a_4559_; lean_object* v___x_4560_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_a_4559_);
lean_dec_ref_known(v___x_4558_, 1);
v___x_4560_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4559_, v_msgData_4552_, v_severity_4553_, v_isSilent_4554_, v___y_4555_, v___y_4556_);
lean_dec(v_a_4559_);
return v___x_4560_;
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_dec_ref(v_msgData_4552_);
v_a_4561_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4558_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4558_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4569_, lean_object* v_severity_4570_, lean_object* v_isSilent_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
uint8_t v_severity_boxed_4575_; uint8_t v_isSilent_boxed_4576_; lean_object* v_res_4577_; 
v_severity_boxed_4575_ = lean_unbox(v_severity_4570_);
v_isSilent_boxed_4576_ = lean_unbox(v_isSilent_4571_);
v_res_4577_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4569_, v_severity_boxed_4575_, v_isSilent_boxed_4576_, v___y_4572_, v___y_4573_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
uint8_t v___x_4582_; uint8_t v___x_4583_; lean_object* v___x_4584_; 
v___x_4582_ = 2;
v___x_4583_ = 0;
v___x_4584_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4578_, v___x_4582_, v___x_4583_, v___y_4579_, v___y_4580_);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4585_, v___y_4586_, v___y_4587_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
return v_res_4589_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4597_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4598_ = l_Lean_MessageData_ofFormat(v___x_4597_);
return v___x_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v___x_4603_; uint8_t v_foundPanic_4604_; 
v___x_4603_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4599_);
v_foundPanic_4604_ = l_Lean_Syntax_isOfKind(v_x_4599_, v___x_4603_);
if (v_foundPanic_4604_ == 0)
{
lean_object* v___x_4605_; 
lean_dec(v_x_4599_);
v___x_4605_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4605_;
}
else
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4606_ = lean_unsigned_to_nat(2u);
v___x_4607_ = l_Lean_Syntax_getArg(v_x_4599_, v___x_4606_);
lean_dec(v_x_4599_);
v___x_4608_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4607_, v_a_4600_, v_a_4601_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; uint8_t v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4669_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
lean_inc(v_a_4609_);
lean_dec_ref_known(v___x_4608_, 1);
v___x_4610_ = 0;
v___x_4611_ = l_Lean_MessageLog_toList(v_a_4609_);
v___x_4612_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4604_, v___x_4611_, v___x_4610_);
lean_dec(v___x_4611_);
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4615_ = v___x_4612_;
v_isShared_4616_ = v_isSharedCheck_4669_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4669_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
uint8_t v___x_4617_; 
v___x_4617_ = lean_unbox(v_a_4613_);
lean_dec(v_a_4613_);
if (v___x_4617_ == 0)
{
lean_object* v___x_4618_; lean_object* v_env_4619_; lean_object* v_scopes_4620_; lean_object* v_usedQuotCtxts_4621_; lean_object* v_nextMacroScope_4622_; lean_object* v_maxRecDepth_4623_; lean_object* v_ngen_4624_; lean_object* v_auxDeclNGen_4625_; lean_object* v_infoState_4626_; lean_object* v_traceState_4627_; lean_object* v_snapshotTasks_4628_; lean_object* v_prevLinterStates_4629_; lean_object* v_codeQualityEntryTasks_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4640_; 
lean_del_object(v___x_4615_);
v___x_4618_ = lean_st_ref_take(v_a_4601_);
v_env_4619_ = lean_ctor_get(v___x_4618_, 0);
v_scopes_4620_ = lean_ctor_get(v___x_4618_, 2);
v_usedQuotCtxts_4621_ = lean_ctor_get(v___x_4618_, 3);
v_nextMacroScope_4622_ = lean_ctor_get(v___x_4618_, 4);
v_maxRecDepth_4623_ = lean_ctor_get(v___x_4618_, 5);
v_ngen_4624_ = lean_ctor_get(v___x_4618_, 6);
v_auxDeclNGen_4625_ = lean_ctor_get(v___x_4618_, 7);
v_infoState_4626_ = lean_ctor_get(v___x_4618_, 8);
v_traceState_4627_ = lean_ctor_get(v___x_4618_, 9);
v_snapshotTasks_4628_ = lean_ctor_get(v___x_4618_, 10);
v_prevLinterStates_4629_ = lean_ctor_get(v___x_4618_, 11);
v_codeQualityEntryTasks_4630_ = lean_ctor_get(v___x_4618_, 12);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4640_ == 0)
{
lean_object* v_unused_4641_; 
v_unused_4641_ = lean_ctor_get(v___x_4618_, 1);
lean_dec(v_unused_4641_);
v___x_4632_ = v___x_4618_;
v_isShared_4633_ = v_isSharedCheck_4640_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4630_);
lean_inc(v_prevLinterStates_4629_);
lean_inc(v_snapshotTasks_4628_);
lean_inc(v_traceState_4627_);
lean_inc(v_infoState_4626_);
lean_inc(v_auxDeclNGen_4625_);
lean_inc(v_ngen_4624_);
lean_inc(v_maxRecDepth_4623_);
lean_inc(v_nextMacroScope_4622_);
lean_inc(v_usedQuotCtxts_4621_);
lean_inc(v_scopes_4620_);
lean_inc(v_env_4619_);
lean_dec(v___x_4618_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4640_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
lean_ctor_set(v___x_4632_, 1, v_a_4609_);
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_env_4619_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_a_4609_);
lean_ctor_set(v_reuseFailAlloc_4639_, 2, v_scopes_4620_);
lean_ctor_set(v_reuseFailAlloc_4639_, 3, v_usedQuotCtxts_4621_);
lean_ctor_set(v_reuseFailAlloc_4639_, 4, v_nextMacroScope_4622_);
lean_ctor_set(v_reuseFailAlloc_4639_, 5, v_maxRecDepth_4623_);
lean_ctor_set(v_reuseFailAlloc_4639_, 6, v_ngen_4624_);
lean_ctor_set(v_reuseFailAlloc_4639_, 7, v_auxDeclNGen_4625_);
lean_ctor_set(v_reuseFailAlloc_4639_, 8, v_infoState_4626_);
lean_ctor_set(v_reuseFailAlloc_4639_, 9, v_traceState_4627_);
lean_ctor_set(v_reuseFailAlloc_4639_, 10, v_snapshotTasks_4628_);
lean_ctor_set(v_reuseFailAlloc_4639_, 11, v_prevLinterStates_4629_);
lean_ctor_set(v_reuseFailAlloc_4639_, 12, v_codeQualityEntryTasks_4630_);
v___x_4635_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4636_ = lean_st_ref_put(v_a_4601_, v___x_4635_);
v___x_4637_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4638_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4637_, v_a_4600_, v_a_4601_);
return v___x_4638_;
}
}
}
else
{
lean_object* v___x_4642_; lean_object* v_env_4643_; lean_object* v_scopes_4644_; lean_object* v_usedQuotCtxts_4645_; lean_object* v_nextMacroScope_4646_; lean_object* v_maxRecDepth_4647_; lean_object* v_ngen_4648_; lean_object* v_auxDeclNGen_4649_; lean_object* v_infoState_4650_; lean_object* v_traceState_4651_; lean_object* v_snapshotTasks_4652_; lean_object* v_prevLinterStates_4653_; lean_object* v_codeQualityEntryTasks_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4667_; 
lean_dec(v_a_4609_);
v___x_4642_ = lean_st_ref_take(v_a_4601_);
v_env_4643_ = lean_ctor_get(v___x_4642_, 0);
v_scopes_4644_ = lean_ctor_get(v___x_4642_, 2);
v_usedQuotCtxts_4645_ = lean_ctor_get(v___x_4642_, 3);
v_nextMacroScope_4646_ = lean_ctor_get(v___x_4642_, 4);
v_maxRecDepth_4647_ = lean_ctor_get(v___x_4642_, 5);
v_ngen_4648_ = lean_ctor_get(v___x_4642_, 6);
v_auxDeclNGen_4649_ = lean_ctor_get(v___x_4642_, 7);
v_infoState_4650_ = lean_ctor_get(v___x_4642_, 8);
v_traceState_4651_ = lean_ctor_get(v___x_4642_, 9);
v_snapshotTasks_4652_ = lean_ctor_get(v___x_4642_, 10);
v_prevLinterStates_4653_ = lean_ctor_get(v___x_4642_, 11);
v_codeQualityEntryTasks_4654_ = lean_ctor_get(v___x_4642_, 12);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4667_ == 0)
{
lean_object* v_unused_4668_; 
v_unused_4668_ = lean_ctor_get(v___x_4642_, 1);
lean_dec(v_unused_4668_);
v___x_4656_ = v___x_4642_;
v_isShared_4657_ = v_isSharedCheck_4667_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4654_);
lean_inc(v_prevLinterStates_4653_);
lean_inc(v_snapshotTasks_4652_);
lean_inc(v_traceState_4651_);
lean_inc(v_infoState_4650_);
lean_inc(v_auxDeclNGen_4649_);
lean_inc(v_ngen_4648_);
lean_inc(v_maxRecDepth_4647_);
lean_inc(v_nextMacroScope_4646_);
lean_inc(v_usedQuotCtxts_4645_);
lean_inc(v_scopes_4644_);
lean_inc(v_env_4643_);
lean_dec(v___x_4642_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4667_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4661_; 
v___x_4658_ = lean_box(0);
v___x_4659_ = l_Lean_MessageLog_empty;
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 1, v___x_4659_);
v___x_4661_ = v___x_4656_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_env_4643_);
lean_ctor_set(v_reuseFailAlloc_4666_, 1, v___x_4659_);
lean_ctor_set(v_reuseFailAlloc_4666_, 2, v_scopes_4644_);
lean_ctor_set(v_reuseFailAlloc_4666_, 3, v_usedQuotCtxts_4645_);
lean_ctor_set(v_reuseFailAlloc_4666_, 4, v_nextMacroScope_4646_);
lean_ctor_set(v_reuseFailAlloc_4666_, 5, v_maxRecDepth_4647_);
lean_ctor_set(v_reuseFailAlloc_4666_, 6, v_ngen_4648_);
lean_ctor_set(v_reuseFailAlloc_4666_, 7, v_auxDeclNGen_4649_);
lean_ctor_set(v_reuseFailAlloc_4666_, 8, v_infoState_4650_);
lean_ctor_set(v_reuseFailAlloc_4666_, 9, v_traceState_4651_);
lean_ctor_set(v_reuseFailAlloc_4666_, 10, v_snapshotTasks_4652_);
lean_ctor_set(v_reuseFailAlloc_4666_, 11, v_prevLinterStates_4653_);
lean_ctor_set(v_reuseFailAlloc_4666_, 12, v_codeQualityEntryTasks_4654_);
v___x_4661_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
lean_object* v___x_4662_; lean_object* v___x_4664_; 
v___x_4662_ = lean_st_ref_put(v_a_4601_, v___x_4661_);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___x_4658_);
v___x_4664_ = v___x_4615_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4658_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
}
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4677_; 
v_a_4670_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4672_ = v___x_4608_;
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4608_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4675_; 
if (v_isShared_4673_ == 0)
{
v___x_4675_ = v___x_4672_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4670_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4678_, v_a_4679_, v_a_4680_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4683_, lean_object* v_as_4684_, lean_object* v_as_x27_4685_, uint8_t v_b_4686_, lean_object* v_a_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v___x_4691_; 
v___x_4691_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4683_, v_as_x27_4685_, v_b_4686_);
return v___x_4691_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4692_, lean_object* v_as_4693_, lean_object* v_as_x27_4694_, lean_object* v_b_4695_, lean_object* v_a_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
uint8_t v_foundPanic_boxed_4700_; uint8_t v_b_boxed_4701_; lean_object* v_res_4702_; 
v_foundPanic_boxed_4700_ = lean_unbox(v_foundPanic_4692_);
v_b_boxed_4701_ = lean_unbox(v_b_4695_);
v_res_4702_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4700_, v_as_4693_, v_as_x27_4694_, v_b_boxed_4701_, v_a_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v_as_x27_4694_);
lean_dec(v_as_4693_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4711_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4712_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4713_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4714_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4715_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4711_, v___x_4712_, v___x_4713_, v___x_4714_);
return v___x_4715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4717_;
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
