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
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
lean_ctor_set(v___x_1905_, 2, v___x_1904_);
lean_ctor_set(v___x_1905_, 3, v___x_1904_);
lean_ctor_set(v___x_1905_, 4, v___x_1903_);
lean_ctor_set(v___x_1905_, 5, v___x_1903_);
lean_ctor_set(v___x_1905_, 6, v___x_1903_);
lean_ctor_set(v___x_1905_, 7, v___x_1903_);
lean_ctor_set(v___x_1905_, 8, v___x_1903_);
lean_ctor_set(v___x_1905_, 9, v___x_1903_);
lean_ctor_set(v___x_1905_, 10, v___x_1903_);
return v___x_1905_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = lean_unsigned_to_nat(32u);
v___x_1907_ = lean_mk_empty_array_with_capacity(v___x_1906_);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1909_ = ((size_t)5ULL);
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = lean_unsigned_to_nat(32u);
v___x_1912_ = lean_mk_empty_array_with_capacity(v___x_1911_);
v___x_1913_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__3);
v___x_1914_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v___x_1912_);
lean_ctor_set(v___x_1914_, 2, v___x_1910_);
lean_ctor_set(v___x_1914_, 3, v___x_1910_);
lean_ctor_set_usize(v___x_1914_, 4, v___x_1909_);
return v___x_1914_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1915_ = lean_box(1);
v___x_1916_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__4);
v___x_1917_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set(v___x_1918_, 1, v___x_1916_);
lean_ctor_set(v___x_1918_, 2, v___x_1915_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(lean_object* v_msgData_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; lean_object* v_env_1923_; uint8_t v___x_1924_; lean_object* v_env_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v_scopes_1928_; lean_object* v___x_1929_; lean_object* v_opts_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1922_ = lean_st_ref_get(v___y_1920_);
v_env_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc_ref(v_env_1923_);
lean_dec(v___x_1922_);
v___x_1924_ = 0;
v_env_1925_ = l_Lean_Environment_setRecordingDeps(v_env_1923_, v___x_1924_);
v___x_1926_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1927_ = lean_st_ref_get(v___y_1920_);
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
lean_ctor_set(v___x_1934_, 1, v_msgData_1919_);
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
lean_dec(v_pre_2027_);
lean_dec_ref_known(v_pre_2026_, 2);
lean_dec_ref_known(v_kind_2025_, 2);
lean_dec_ref_known(v___x_2024_, 3);
goto v___jp_2017_;
}
}
else
{
lean_dec_ref_known(v_kind_2025_, 2);
lean_dec(v_pre_2026_);
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
uint8_t v_suppressElabErrors_boxed_2261_; uint8_t v___y_26099__boxed_2262_; uint8_t v_res_2263_; lean_object* v_r_2264_; 
v_suppressElabErrors_boxed_2261_ = lean_unbox(v_suppressElabErrors_2258_);
v___y_26099__boxed_2262_ = lean_unbox(v___y_2259_);
v_res_2263_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v_suppressElabErrors_boxed_2261_, v___y_26099__boxed_2262_, v_x_2260_);
lean_dec(v_x_2260_);
v_r_2264_ = lean_box(v_res_2263_);
return v_r_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2265_, lean_object* v_msgData_2266_, uint8_t v_severity_2267_, uint8_t v_isSilent_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___y_2273_; uint8_t v___y_2274_; lean_object* v___y_2275_; uint8_t v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; uint8_t v___y_2338_; uint8_t v___y_2339_; uint8_t v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; uint8_t v___y_2366_; uint8_t v___y_2367_; lean_object* v___y_2368_; uint8_t v___y_2369_; lean_object* v___y_2370_; uint8_t v___y_2374_; uint8_t v___y_2375_; uint8_t v___y_2376_; uint8_t v___x_2391_; uint8_t v___y_2393_; uint8_t v___y_2394_; uint8_t v___y_2395_; uint8_t v___y_2397_; uint8_t v___x_2409_; 
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
lean_ctor_set(v___x_2291_, 1, v___y_2278_);
lean_inc_ref(v___y_2273_);
lean_inc_ref(v___y_2279_);
v___x_2292_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2292_, 0, v___y_2279_);
lean_ctor_set(v___x_2292_, 1, v___y_2275_);
lean_ctor_set(v___x_2292_, 2, v___y_2277_);
lean_ctor_set(v___x_2292_, 3, v___y_2273_);
lean_ctor_set(v___x_2292_, 4, v___x_2291_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*5, v___y_2274_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*5 + 1, v___y_2276_);
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
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2275_);
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
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2275_);
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
v___y_2273_ = v___x_2358_;
v___y_2274_ = v___y_2339_;
v___y_2275_ = v___x_2355_;
v___y_2276_ = v___y_2340_;
v___y_2277_ = v___x_2357_;
v___y_2278_ = v_a_2351_;
v___y_2279_ = v_fileName_2343_;
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
v___y_2273_ = v___x_2358_;
v___y_2274_ = v___y_2339_;
v___y_2275_ = v___x_2355_;
v___y_2276_ = v___y_2340_;
v___y_2277_ = v___x_2357_;
v___y_2278_ = v_a_2351_;
v___y_2279_ = v_fileName_2343_;
v___y_2280_ = v___y_2270_;
goto v___jp_2272_;
}
}
}
}
v___jp_2365_:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Syntax_getTailPos_x3f(v___y_2368_, v___y_2367_);
lean_dec(v___y_2368_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_inc(v___y_2370_);
v___y_2338_ = v___y_2366_;
v___y_2339_ = v___y_2367_;
v___y_2340_ = v___y_2369_;
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
v___y_2340_ = v___y_2369_;
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
v___y_2367_ = v___y_2375_;
v___y_2368_ = v_ref_2379_;
v___y_2369_ = v___y_2376_;
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
v___y_2367_ = v___y_2375_;
v___y_2368_ = v_ref_2379_;
v___y_2369_ = v___y_2376_;
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
lean_object* v_start_2924_; lean_object* v_stop_2925_; lean_object* v_i_2926_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v_start_2924_ = lean_ctor_get(v_left_2921_, 1);
v_stop_2925_ = lean_ctor_get(v_left_2921_, 2);
v_i_2926_ = lean_array_get_size(v_pref_2923_);
v___x_2932_ = lean_nat_sub(v_stop_2925_, v_start_2924_);
v___x_2933_ = lean_nat_dec_lt(v_i_2926_, v___x_2932_);
lean_dec(v___x_2932_);
if (v___x_2933_ == 0)
{
goto v___jp_2927_;
}
else
{
lean_object* v_start_2934_; lean_object* v_stop_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v_start_2934_ = lean_ctor_get(v_right_2922_, 1);
v_stop_2935_ = lean_ctor_get(v_right_2922_, 2);
v___x_2936_ = lean_nat_sub(v_stop_2935_, v_start_2934_);
v___x_2937_ = lean_nat_dec_lt(v_i_2926_, v___x_2936_);
lean_dec(v___x_2936_);
if (v___x_2937_ == 0)
{
goto v___jp_2927_;
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2938_ = l_Subarray_get___redArg(v_left_2921_, v_i_2926_);
v___x_2939_ = l_Subarray_get___redArg(v_right_2922_, v_i_2926_);
v___x_2940_ = lean_string_dec_eq(v___x_2938_, v___x_2939_);
lean_dec(v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
lean_dec(v___x_2938_);
v___x_2941_ = l_Subarray_drop___redArg(v_left_2921_, v_i_2926_);
v___x_2942_ = l_Subarray_drop___redArg(v_right_2922_, v_i_2926_);
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
v___x_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2944_, 0, v_pref_2923_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
return v___x_2944_;
}
else
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_array_push(v_pref_2923_, v___x_2938_);
v_pref_2923_ = v___x_2945_;
goto _start;
}
}
}
v___jp_2927_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2928_ = l_Subarray_drop___redArg(v_left_2921_, v_i_2926_);
v___x_2929_ = l_Subarray_drop___redArg(v_right_2922_, v_i_2926_);
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2928_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v_pref_2923_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(lean_object* v_left_2949_, lean_object* v_right_2950_){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_2952_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(v_left_2949_, v_right_2950_, v___x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(lean_object* v_a_2953_, lean_object* v_b_2954_, lean_object* v_x_2955_){
_start:
{
if (lean_obj_tag(v_x_2955_) == 0)
{
lean_dec(v_b_2954_);
lean_dec_ref(v_a_2953_);
return v_x_2955_;
}
else
{
lean_object* v_key_2956_; lean_object* v_value_2957_; lean_object* v_tail_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2970_; 
v_key_2956_ = lean_ctor_get(v_x_2955_, 0);
v_value_2957_ = lean_ctor_get(v_x_2955_, 1);
v_tail_2958_ = lean_ctor_get(v_x_2955_, 2);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_x_2955_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2960_ = v_x_2955_;
v_isShared_2961_ = v_isSharedCheck_2970_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_tail_2958_);
lean_inc(v_value_2957_);
lean_inc(v_key_2956_);
lean_dec(v_x_2955_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2970_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
uint8_t v___x_2962_; 
v___x_2962_ = lean_string_dec_eq(v_key_2956_, v_a_2953_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2963_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_2953_, v_b_2954_, v_tail_2958_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 2, v___x_2963_);
v___x_2965_ = v___x_2960_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_key_2956_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_value_2957_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
else
{
lean_object* v___x_2968_; 
lean_dec(v_value_2957_);
lean_dec(v_key_2956_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 1, v_b_2954_);
lean_ctor_set(v___x_2960_, 0, v_a_2953_);
v___x_2968_ = v___x_2960_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2953_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_b_2954_);
lean_ctor_set(v_reuseFailAlloc_2969_, 2, v_tail_2958_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2971_, lean_object* v_x_2972_){
_start:
{
if (lean_obj_tag(v_x_2972_) == 0)
{
return v_x_2971_;
}
else
{
lean_object* v_key_2973_; lean_object* v_value_2974_; lean_object* v_tail_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2998_; 
v_key_2973_ = lean_ctor_get(v_x_2972_, 0);
v_value_2974_ = lean_ctor_get(v_x_2972_, 1);
v_tail_2975_ = lean_ctor_get(v_x_2972_, 2);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_x_2972_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2977_ = v_x_2972_;
v_isShared_2978_ = v_isSharedCheck_2998_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_tail_2975_);
lean_inc(v_value_2974_);
lean_inc(v_key_2973_);
lean_dec(v_x_2972_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2998_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; uint64_t v___x_2980_; uint64_t v___x_2981_; uint64_t v___x_2982_; uint64_t v_fold_2983_; uint64_t v___x_2984_; uint64_t v___x_2985_; uint64_t v___x_2986_; size_t v___x_2987_; size_t v___x_2988_; size_t v___x_2989_; size_t v___x_2990_; size_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2979_ = lean_array_get_size(v_x_2971_);
v___x_2980_ = lean_string_hash(v_key_2973_);
v___x_2981_ = 32ULL;
v___x_2982_ = lean_uint64_shift_right(v___x_2980_, v___x_2981_);
v_fold_2983_ = lean_uint64_xor(v___x_2980_, v___x_2982_);
v___x_2984_ = 16ULL;
v___x_2985_ = lean_uint64_shift_right(v_fold_2983_, v___x_2984_);
v___x_2986_ = lean_uint64_xor(v_fold_2983_, v___x_2985_);
v___x_2987_ = lean_uint64_to_usize(v___x_2986_);
v___x_2988_ = lean_usize_of_nat(v___x_2979_);
v___x_2989_ = ((size_t)1ULL);
v___x_2990_ = lean_usize_sub(v___x_2988_, v___x_2989_);
v___x_2991_ = lean_usize_land(v___x_2987_, v___x_2990_);
v___x_2992_ = lean_array_uget_borrowed(v_x_2971_, v___x_2991_);
lean_inc(v___x_2992_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 2, v___x_2992_);
v___x_2994_ = v___x_2977_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_key_2973_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v_value_2974_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_array_uset(v_x_2971_, v___x_2991_, v___x_2994_);
v_x_2971_ = v___x_2995_;
v_x_2972_ = v_tail_2975_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(lean_object* v_i_2999_, lean_object* v_source_3000_, lean_object* v_target_3001_){
_start:
{
lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3002_ = lean_array_get_size(v_source_3000_);
v___x_3003_ = lean_nat_dec_lt(v_i_2999_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_dec_ref(v_source_3000_);
lean_dec(v_i_2999_);
return v_target_3001_;
}
else
{
lean_object* v_es_3004_; lean_object* v___x_3005_; lean_object* v_source_3006_; lean_object* v_target_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_es_3004_ = lean_array_fget(v_source_3000_, v_i_2999_);
v___x_3005_ = lean_box(0);
v_source_3006_ = lean_array_fset(v_source_3000_, v_i_2999_, v___x_3005_);
v_target_3007_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_target_3001_, v_es_3004_);
v___x_3008_ = lean_unsigned_to_nat(1u);
v___x_3009_ = lean_nat_add(v_i_2999_, v___x_3008_);
lean_dec(v_i_2999_);
v_i_2999_ = v___x_3009_;
v_source_3000_ = v_source_3006_;
v_target_3001_ = v_target_3007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(lean_object* v_data_3011_){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v_nbuckets_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3012_ = lean_array_get_size(v_data_3011_);
v___x_3013_ = lean_unsigned_to_nat(2u);
v_nbuckets_3014_ = lean_nat_mul(v___x_3012_, v___x_3013_);
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3016_ = lean_box(0);
v___x_3017_ = lean_mk_array(v_nbuckets_3014_, v___x_3016_);
v___x_3018_ = lean_array_propagate_mark(v_data_3011_, v___x_3017_);
v___x_3019_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v___x_3015_, v_data_3011_, v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(lean_object* v_a_3020_, lean_object* v_x_3021_){
_start:
{
if (lean_obj_tag(v_x_3021_) == 0)
{
uint8_t v___x_3022_; 
v___x_3022_ = 0;
return v___x_3022_;
}
else
{
lean_object* v_key_3023_; lean_object* v_tail_3024_; uint8_t v___x_3025_; 
v_key_3023_ = lean_ctor_get(v_x_3021_, 0);
v_tail_3024_ = lean_ctor_get(v_x_3021_, 2);
v___x_3025_ = lean_string_dec_eq(v_key_3023_, v_a_3020_);
if (v___x_3025_ == 0)
{
v_x_3021_ = v_tail_3024_;
goto _start;
}
else
{
return v___x_3025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg___boxed(lean_object* v_a_3027_, lean_object* v_x_3028_){
_start:
{
uint8_t v_res_3029_; lean_object* v_r_3030_; 
v_res_3029_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_3027_, v_x_3028_);
lean_dec(v_x_3028_);
lean_dec_ref(v_a_3027_);
v_r_3030_ = lean_box(v_res_3029_);
return v_r_3030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(lean_object* v_m_3031_, lean_object* v_a_3032_, lean_object* v_b_3033_){
_start:
{
lean_object* v_size_3034_; lean_object* v_buckets_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3078_; 
v_size_3034_ = lean_ctor_get(v_m_3031_, 0);
v_buckets_3035_ = lean_ctor_get(v_m_3031_, 1);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_m_3031_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3037_ = v_m_3031_;
v_isShared_3038_ = v_isSharedCheck_3078_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_buckets_3035_);
lean_inc(v_size_3034_);
lean_dec(v_m_3031_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3078_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; uint64_t v___x_3040_; uint64_t v___x_3041_; uint64_t v___x_3042_; uint64_t v_fold_3043_; uint64_t v___x_3044_; uint64_t v___x_3045_; uint64_t v___x_3046_; size_t v___x_3047_; size_t v___x_3048_; size_t v___x_3049_; size_t v___x_3050_; size_t v___x_3051_; lean_object* v_bkt_3052_; uint8_t v___x_3053_; 
v___x_3039_ = lean_array_get_size(v_buckets_3035_);
v___x_3040_ = lean_string_hash(v_a_3032_);
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
v_bkt_3052_ = lean_array_uget_borrowed(v_buckets_3035_, v___x_3051_);
v___x_3053_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_3032_, v_bkt_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v_size_x27_3055_; lean_object* v___x_3056_; lean_object* v_buckets_x27_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v___x_3054_ = lean_unsigned_to_nat(1u);
v_size_x27_3055_ = lean_nat_add(v_size_3034_, v___x_3054_);
lean_dec(v_size_3034_);
lean_inc(v_bkt_3052_);
v___x_3056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3056_, 0, v_a_3032_);
lean_ctor_set(v___x_3056_, 1, v_b_3033_);
lean_ctor_set(v___x_3056_, 2, v_bkt_3052_);
v_buckets_x27_3057_ = lean_array_uset(v_buckets_3035_, v___x_3051_, v___x_3056_);
v___x_3058_ = lean_unsigned_to_nat(4u);
v___x_3059_ = lean_nat_mul(v_size_x27_3055_, v___x_3058_);
v___x_3060_ = lean_unsigned_to_nat(3u);
v___x_3061_ = lean_nat_div(v___x_3059_, v___x_3060_);
lean_dec(v___x_3059_);
v___x_3062_ = lean_array_get_size(v_buckets_x27_3057_);
v___x_3063_ = lean_nat_dec_le(v___x_3061_, v___x_3062_);
lean_dec(v___x_3061_);
if (v___x_3063_ == 0)
{
lean_object* v_val_3064_; lean_object* v___x_3066_; 
v_val_3064_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_buckets_x27_3057_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v_val_3064_);
lean_ctor_set(v___x_3037_, 0, v_size_x27_3055_);
v___x_3066_ = v___x_3037_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_size_x27_3055_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_val_3064_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
else
{
lean_object* v___x_3069_; 
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v_buckets_x27_3057_);
lean_ctor_set(v___x_3037_, 0, v_size_x27_3055_);
v___x_3069_ = v___x_3037_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_size_x27_3055_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_buckets_x27_3057_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
else
{
lean_object* v___x_3071_; lean_object* v_buckets_x27_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3076_; 
lean_inc(v_bkt_3052_);
v___x_3071_ = lean_box(0);
v_buckets_x27_3072_ = lean_array_uset(v_buckets_3035_, v___x_3051_, v___x_3071_);
v___x_3073_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_3032_, v_b_3033_, v_bkt_3052_);
v___x_3074_ = lean_array_uset(v_buckets_x27_3072_, v___x_3051_, v___x_3073_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v___x_3074_);
v___x_3076_ = v___x_3037_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_size_3034_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(lean_object* v_a_3079_, lean_object* v_x_3080_){
_start:
{
if (lean_obj_tag(v_x_3080_) == 0)
{
lean_object* v___x_3081_; 
v___x_3081_ = lean_box(0);
return v___x_3081_;
}
else
{
lean_object* v_key_3082_; lean_object* v_value_3083_; lean_object* v_tail_3084_; uint8_t v___x_3085_; 
v_key_3082_ = lean_ctor_get(v_x_3080_, 0);
v_value_3083_ = lean_ctor_get(v_x_3080_, 1);
v_tail_3084_ = lean_ctor_get(v_x_3080_, 2);
v___x_3085_ = lean_string_dec_eq(v_key_3082_, v_a_3079_);
if (v___x_3085_ == 0)
{
v_x_3080_ = v_tail_3084_;
goto _start;
}
else
{
lean_object* v___x_3087_; 
lean_inc(v_value_3083_);
v___x_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3087_, 0, v_value_3083_);
return v___x_3087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg___boxed(lean_object* v_a_3088_, lean_object* v_x_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3088_, v_x_3089_);
lean_dec(v_x_3089_);
lean_dec_ref(v_a_3088_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(lean_object* v_m_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v_buckets_3093_; lean_object* v___x_3094_; uint64_t v___x_3095_; uint64_t v___x_3096_; uint64_t v___x_3097_; uint64_t v_fold_3098_; uint64_t v___x_3099_; uint64_t v___x_3100_; uint64_t v___x_3101_; size_t v___x_3102_; size_t v___x_3103_; size_t v___x_3104_; size_t v___x_3105_; size_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v_buckets_3093_ = lean_ctor_get(v_m_3091_, 1);
v___x_3094_ = lean_array_get_size(v_buckets_3093_);
v___x_3095_ = lean_string_hash(v_a_3092_);
v___x_3096_ = 32ULL;
v___x_3097_ = lean_uint64_shift_right(v___x_3095_, v___x_3096_);
v_fold_3098_ = lean_uint64_xor(v___x_3095_, v___x_3097_);
v___x_3099_ = 16ULL;
v___x_3100_ = lean_uint64_shift_right(v_fold_3098_, v___x_3099_);
v___x_3101_ = lean_uint64_xor(v_fold_3098_, v___x_3100_);
v___x_3102_ = lean_uint64_to_usize(v___x_3101_);
v___x_3103_ = lean_usize_of_nat(v___x_3094_);
v___x_3104_ = ((size_t)1ULL);
v___x_3105_ = lean_usize_sub(v___x_3103_, v___x_3104_);
v___x_3106_ = lean_usize_land(v___x_3102_, v___x_3105_);
v___x_3107_ = lean_array_uget_borrowed(v_buckets_3093_, v___x_3106_);
v___x_3108_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3092_, v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg___boxed(lean_object* v_m_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_3109_, v_a_3110_);
lean_dec_ref(v_a_3110_);
lean_dec_ref(v_m_3109_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(lean_object* v_histogram_3112_, lean_object* v_index_3113_, lean_object* v_val_3114_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3112_, v_val_3114_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3116_ = lean_unsigned_to_nat(1u);
v___x_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3117_, 0, v_index_3113_);
v___x_3118_ = lean_unsigned_to_nat(0u);
v___x_3119_ = lean_box(0);
v___x_3120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3116_);
lean_ctor_set(v___x_3120_, 1, v___x_3117_);
lean_ctor_set(v___x_3120_, 2, v___x_3118_);
lean_ctor_set(v___x_3120_, 3, v___x_3119_);
v___x_3121_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3112_, v_val_3114_, v___x_3120_);
return v___x_3121_;
}
else
{
lean_object* v_val_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3143_; 
v_val_3122_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3124_ = v___x_3115_;
v_isShared_3125_ = v_isSharedCheck_3143_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_val_3122_);
lean_dec(v___x_3115_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3143_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v_leftCount_3126_; lean_object* v_rightCount_3127_; lean_object* v_rightIndex_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3141_; 
v_leftCount_3126_ = lean_ctor_get(v_val_3122_, 0);
v_rightCount_3127_ = lean_ctor_get(v_val_3122_, 2);
v_rightIndex_3128_ = lean_ctor_get(v_val_3122_, 3);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_val_3122_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; 
v_unused_3142_ = lean_ctor_get(v_val_3122_, 1);
lean_dec(v_unused_3142_);
v___x_3130_ = v_val_3122_;
v_isShared_3131_ = v_isSharedCheck_3141_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_rightIndex_3128_);
lean_inc(v_rightCount_3127_);
lean_inc(v_leftCount_3126_);
lean_dec(v_val_3122_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3141_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3132_ = lean_unsigned_to_nat(1u);
v___x_3133_ = lean_nat_add(v_leftCount_3126_, v___x_3132_);
lean_dec(v_leftCount_3126_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v_index_3113_);
v___x_3135_ = v___x_3124_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_index_3113_);
v___x_3135_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3137_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 1, v___x_3135_);
lean_ctor_set(v___x_3130_, 0, v___x_3133_);
v___x_3137_ = v___x_3130_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_3135_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_rightCount_3127_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v_rightIndex_3128_);
v___x_3137_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3112_, v_val_3114_, v___x_3137_);
return v___x_3138_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(lean_object* v_upperBound_3144_, lean_object* v_fst_3145_, lean_object* v___x_3146_, lean_object* v_fst_3147_, lean_object* v_a_3148_, lean_object* v_b_3149_){
_start:
{
uint8_t v___x_3150_; 
v___x_3150_ = lean_nat_dec_lt(v_a_3148_, v_upperBound_3144_);
if (v___x_3150_ == 0)
{
lean_dec(v_a_3148_);
return v_b_3149_;
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3151_ = l_Subarray_get___redArg(v_fst_3147_, v_a_3148_);
lean_inc(v_a_3148_);
v___x_3152_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_b_3149_, v_a_3148_, v___x_3151_);
v___x_3153_ = lean_unsigned_to_nat(1u);
v___x_3154_ = lean_nat_add(v_a_3148_, v___x_3153_);
lean_dec(v_a_3148_);
v_a_3148_ = v___x_3154_;
v_b_3149_ = v___x_3152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_upperBound_3156_, lean_object* v_fst_3157_, lean_object* v___x_3158_, lean_object* v_fst_3159_, lean_object* v_a_3160_, lean_object* v_b_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3156_, v_fst_3157_, v___x_3158_, v_fst_3159_, v_a_3160_, v_b_3161_);
lean_dec_ref(v_fst_3159_);
lean_dec(v___x_3158_);
lean_dec_ref(v_fst_3157_);
lean_dec(v_upperBound_3156_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(lean_object* v_as_x27_3163_, lean_object* v_b_3164_){
_start:
{
if (lean_obj_tag(v_as_x27_3163_) == 0)
{
return v_b_3164_;
}
else
{
lean_object* v_head_3165_; lean_object* v_snd_3166_; lean_object* v_leftIndex_3167_; 
v_head_3165_ = lean_ctor_get(v_as_x27_3163_, 0);
v_snd_3166_ = lean_ctor_get(v_head_3165_, 1);
v_leftIndex_3167_ = lean_ctor_get(v_snd_3166_, 1);
if (lean_obj_tag(v_leftIndex_3167_) == 1)
{
lean_object* v_rightIndex_3168_; 
v_rightIndex_3168_ = lean_ctor_get(v_snd_3166_, 3);
if (lean_obj_tag(v_rightIndex_3168_) == 1)
{
if (lean_obj_tag(v_b_3164_) == 0)
{
lean_object* v_tail_3169_; lean_object* v_fst_3170_; lean_object* v_leftCount_3171_; lean_object* v_rightCount_3172_; lean_object* v_val_3173_; lean_object* v_val_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_tail_3169_ = lean_ctor_get(v_as_x27_3163_, 1);
v_fst_3170_ = lean_ctor_get(v_head_3165_, 0);
v_leftCount_3171_ = lean_ctor_get(v_snd_3166_, 0);
v_rightCount_3172_ = lean_ctor_get(v_snd_3166_, 2);
v_val_3173_ = lean_ctor_get(v_leftIndex_3167_, 0);
v_val_3174_ = lean_ctor_get(v_rightIndex_3168_, 0);
v___x_3175_ = lean_nat_add(v_leftCount_3171_, v_rightCount_3172_);
lean_inc(v_val_3174_);
lean_inc(v_val_3173_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v_val_3173_);
lean_ctor_set(v___x_3176_, 1, v_val_3174_);
lean_inc(v_fst_3170_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v_fst_3170_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3175_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
v_as_x27_3163_ = v_tail_3169_;
v_b_3164_ = v___x_3179_;
goto _start;
}
else
{
lean_object* v_val_3181_; lean_object* v_tail_3182_; lean_object* v_fst_3183_; lean_object* v_leftCount_3184_; lean_object* v_rightCount_3185_; lean_object* v_val_3186_; lean_object* v_val_3187_; lean_object* v_fst_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3209_; 
v_val_3181_ = lean_ctor_get(v_b_3164_, 0);
lean_inc(v_val_3181_);
v_tail_3182_ = lean_ctor_get(v_as_x27_3163_, 1);
v_fst_3183_ = lean_ctor_get(v_head_3165_, 0);
v_leftCount_3184_ = lean_ctor_get(v_snd_3166_, 0);
v_rightCount_3185_ = lean_ctor_get(v_snd_3166_, 2);
v_val_3186_ = lean_ctor_get(v_leftIndex_3167_, 0);
v_val_3187_ = lean_ctor_get(v_rightIndex_3168_, 0);
v_fst_3188_ = lean_ctor_get(v_val_3181_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_val_3181_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; 
v_unused_3210_ = lean_ctor_get(v_val_3181_, 1);
lean_dec(v_unused_3210_);
v___x_3190_ = v_val_3181_;
v_isShared_3191_ = v_isSharedCheck_3209_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_fst_3188_);
lean_dec(v_val_3181_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3209_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = lean_nat_add(v_leftCount_3184_, v_rightCount_3185_);
v___x_3193_ = lean_nat_dec_lt(v___x_3192_, v_fst_3188_);
lean_dec(v_fst_3188_);
if (v___x_3193_ == 0)
{
lean_dec(v___x_3192_);
lean_del_object(v___x_3190_);
v_as_x27_3163_ = v_tail_3182_;
goto _start;
}
else
{
lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3207_; 
v_isSharedCheck_3207_ = !lean_is_exclusive(v_b_3164_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; 
v_unused_3208_ = lean_ctor_get(v_b_3164_, 0);
lean_dec(v_unused_3208_);
v___x_3196_ = v_b_3164_;
v_isShared_3197_ = v_isSharedCheck_3207_;
goto v_resetjp_3195_;
}
else
{
lean_dec(v_b_3164_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3207_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
lean_inc(v_val_3187_);
lean_inc(v_val_3186_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 1, v_val_3187_);
lean_ctor_set(v___x_3190_, 0, v_val_3186_);
v___x_3199_ = v___x_3190_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_val_3186_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_val_3187_);
v___x_3199_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3203_; 
lean_inc(v_fst_3183_);
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v_fst_3183_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3192_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v___x_3201_);
v___x_3203_ = v___x_3196_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
v_as_x27_3163_ = v_tail_3182_;
v_b_3164_ = v___x_3203_;
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
lean_object* v_tail_3211_; 
v_tail_3211_ = lean_ctor_get(v_as_x27_3163_, 1);
v_as_x27_3163_ = v_tail_3211_;
goto _start;
}
}
else
{
lean_object* v_tail_3213_; 
v_tail_3213_ = lean_ctor_get(v_as_x27_3163_, 1);
v_as_x27_3163_ = v_tail_3213_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg___boxed(lean_object* v_as_x27_3215_, lean_object* v_b_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3215_, v_b_3216_);
lean_dec(v_as_x27_3215_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(lean_object* v_histogram_3218_, lean_object* v_index_3219_, lean_object* v_val_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3218_, v_val_3220_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3222_ = lean_unsigned_to_nat(0u);
v___x_3223_ = lean_box(0);
v___x_3224_ = lean_unsigned_to_nat(1u);
v___x_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3225_, 0, v_index_3219_);
v___x_3226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3222_);
lean_ctor_set(v___x_3226_, 1, v___x_3223_);
lean_ctor_set(v___x_3226_, 2, v___x_3224_);
lean_ctor_set(v___x_3226_, 3, v___x_3225_);
v___x_3227_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3218_, v_val_3220_, v___x_3226_);
return v___x_3227_;
}
else
{
lean_object* v_val_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3249_; 
v_val_3228_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3230_ = v___x_3221_;
v_isShared_3231_ = v_isSharedCheck_3249_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_val_3228_);
lean_dec(v___x_3221_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3249_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v_leftCount_3232_; lean_object* v_leftIndex_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3246_; 
v_leftCount_3232_ = lean_ctor_get(v_val_3228_, 0);
v_leftIndex_3233_ = lean_ctor_get(v_val_3228_, 1);
v_isSharedCheck_3246_ = !lean_is_exclusive(v_val_3228_);
if (v_isSharedCheck_3246_ == 0)
{
lean_object* v_unused_3247_; lean_object* v_unused_3248_; 
v_unused_3247_ = lean_ctor_get(v_val_3228_, 3);
lean_dec(v_unused_3247_);
v_unused_3248_ = lean_ctor_get(v_val_3228_, 2);
lean_dec(v_unused_3248_);
v___x_3235_ = v_val_3228_;
v_isShared_3236_ = v_isSharedCheck_3246_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_leftIndex_3233_);
lean_inc(v_leftCount_3232_);
lean_dec(v_val_3228_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3246_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3237_ = lean_unsigned_to_nat(1u);
v___x_3238_ = lean_nat_add(v_leftCount_3232_, v___x_3237_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v_index_3219_);
v___x_3240_ = v___x_3230_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_index_3219_);
v___x_3240_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3242_; 
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 3, v___x_3240_);
lean_ctor_set(v___x_3235_, 2, v___x_3238_);
v___x_3242_ = v___x_3235_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_leftCount_3232_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_leftIndex_3233_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3218_, v_val_3220_, v___x_3242_);
return v___x_3243_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(lean_object* v_upperBound_3250_, lean_object* v___x_3251_, lean_object* v_fst_3252_, lean_object* v___x_3253_, lean_object* v_a_3254_, lean_object* v_b_3255_){
_start:
{
uint8_t v___x_3256_; 
v___x_3256_ = lean_nat_dec_lt(v_a_3254_, v_upperBound_3250_);
if (v___x_3256_ == 0)
{
lean_dec(v_a_3254_);
return v_b_3255_;
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3257_ = l_Subarray_get___redArg(v_fst_3252_, v_a_3254_);
lean_inc(v_a_3254_);
v___x_3258_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_b_3255_, v_a_3254_, v___x_3257_);
v___x_3259_ = lean_unsigned_to_nat(1u);
v___x_3260_ = lean_nat_add(v_a_3254_, v___x_3259_);
lean_dec(v_a_3254_);
v_a_3254_ = v___x_3260_;
v_b_3255_ = v___x_3258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg___boxed(lean_object* v_upperBound_3262_, lean_object* v___x_3263_, lean_object* v_fst_3264_, lean_object* v___x_3265_, lean_object* v_a_3266_, lean_object* v_b_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3262_, v___x_3263_, v_fst_3264_, v___x_3265_, v_a_3266_, v_b_3267_);
lean_dec(v___x_3265_);
lean_dec_ref(v_fst_3264_);
lean_dec(v___x_3263_);
lean_dec(v_upperBound_3262_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(lean_object* v_a_3269_, lean_object* v_b_3270_){
_start:
{
lean_object* v_array_3271_; lean_object* v_start_3272_; lean_object* v_stop_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3286_; 
v_array_3271_ = lean_ctor_get(v_a_3269_, 0);
v_start_3272_ = lean_ctor_get(v_a_3269_, 1);
v_stop_3273_ = lean_ctor_get(v_a_3269_, 2);
v_isSharedCheck_3286_ = !lean_is_exclusive(v_a_3269_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3275_ = v_a_3269_;
v_isShared_3276_ = v_isSharedCheck_3286_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_stop_3273_);
lean_inc(v_start_3272_);
lean_inc(v_array_3271_);
lean_dec(v_a_3269_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3286_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
uint8_t v___x_3277_; 
v___x_3277_ = lean_nat_dec_lt(v_start_3272_, v_stop_3273_);
if (v___x_3277_ == 0)
{
lean_del_object(v___x_3275_);
lean_dec(v_stop_3273_);
lean_dec(v_start_3272_);
lean_dec_ref(v_array_3271_);
return v_b_3270_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3278_ = lean_unsigned_to_nat(1u);
v___x_3279_ = lean_nat_add(v_start_3272_, v___x_3278_);
lean_inc_ref(v_array_3271_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 1, v___x_3279_);
v___x_3281_ = v___x_3275_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_array_3271_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3285_, 2, v_stop_3273_);
v___x_3281_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = lean_array_fget(v_array_3271_, v_start_3272_);
lean_dec(v_start_3272_);
lean_dec_ref(v_array_3271_);
v___x_3283_ = lean_array_push(v_b_3270_, v___x_3282_);
v_a_3269_ = v___x_3281_;
v_b_3270_ = v___x_3283_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(lean_object* v_left_3287_, lean_object* v_right_3288_, lean_object* v_i_3289_){
_start:
{
lean_object* v_start_3290_; lean_object* v_stop_3291_; lean_object* v___x_3292_; uint8_t v___x_3306_; 
v_start_3290_ = lean_ctor_get(v_left_3287_, 1);
v_stop_3291_ = lean_ctor_get(v_left_3287_, 2);
v___x_3292_ = lean_nat_sub(v_stop_3291_, v_start_3290_);
v___x_3306_ = lean_nat_dec_lt(v_i_3289_, v___x_3292_);
if (v___x_3306_ == 0)
{
goto v___jp_3293_;
}
else
{
lean_object* v_start_3307_; lean_object* v_stop_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
v_start_3307_ = lean_ctor_get(v_right_3288_, 1);
v_stop_3308_ = lean_ctor_get(v_right_3288_, 2);
v___x_3309_ = lean_nat_sub(v_stop_3308_, v_start_3307_);
v___x_3310_ = lean_nat_dec_lt(v_i_3289_, v___x_3309_);
if (v___x_3310_ == 0)
{
lean_dec(v___x_3309_);
goto v___jp_3293_;
}
else
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v___x_3311_ = lean_nat_sub(v___x_3292_, v_i_3289_);
lean_dec(v___x_3292_);
v___x_3312_ = lean_unsigned_to_nat(1u);
v___x_3313_ = lean_nat_sub(v___x_3311_, v___x_3312_);
v___x_3314_ = l_Subarray_get___redArg(v_left_3287_, v___x_3313_);
lean_dec(v___x_3313_);
v___x_3315_ = lean_nat_sub(v___x_3309_, v_i_3289_);
lean_dec(v___x_3309_);
v___x_3316_ = lean_nat_sub(v___x_3315_, v___x_3312_);
v___x_3317_ = l_Subarray_get___redArg(v_right_3288_, v___x_3316_);
lean_dec(v___x_3316_);
v___x_3318_ = lean_string_dec_eq(v___x_3314_, v___x_3317_);
lean_dec(v___x_3317_);
lean_dec(v___x_3314_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_dec(v_i_3289_);
lean_inc_ref(v_left_3287_);
v___x_3319_ = l_Subarray_take___redArg(v_left_3287_, v___x_3311_);
v___x_3320_ = l_Subarray_take___redArg(v_right_3288_, v___x_3315_);
lean_dec(v___x_3315_);
v___x_3321_ = l_Subarray_drop___redArg(v_left_3287_, v___x_3311_);
lean_dec(v___x_3311_);
v___x_3322_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3323_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3321_, v___x_3322_);
v___x_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3320_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3319_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
return v___x_3325_;
}
else
{
lean_object* v___x_3326_; 
lean_dec(v___x_3315_);
lean_dec(v___x_3311_);
v___x_3326_ = lean_nat_add(v_i_3289_, v___x_3312_);
lean_dec(v_i_3289_);
v_i_3289_ = v___x_3326_;
goto _start;
}
}
}
v___jp_3293_:
{
lean_object* v_start_3294_; lean_object* v_stop_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v_start_3294_ = lean_ctor_get(v_right_3288_, 1);
v_stop_3295_ = lean_ctor_get(v_right_3288_, 2);
v___x_3296_ = lean_nat_sub(v___x_3292_, v_i_3289_);
lean_dec(v___x_3292_);
lean_inc_ref(v_left_3287_);
v___x_3297_ = l_Subarray_take___redArg(v_left_3287_, v___x_3296_);
v___x_3298_ = lean_nat_sub(v_stop_3295_, v_start_3294_);
v___x_3299_ = lean_nat_sub(v___x_3298_, v_i_3289_);
lean_dec(v_i_3289_);
lean_dec(v___x_3298_);
v___x_3300_ = l_Subarray_take___redArg(v_right_3288_, v___x_3299_);
lean_dec(v___x_3299_);
v___x_3301_ = l_Subarray_drop___redArg(v_left_3287_, v___x_3296_);
lean_dec(v___x_3296_);
v___x_3302_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3303_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3301_, v___x_3302_);
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3300_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3297_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(lean_object* v_left_3328_, lean_object* v_right_3329_){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = lean_unsigned_to_nat(0u);
v___x_3331_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(v_left_3328_, v_right_3329_, v___x_3330_);
return v___x_3331_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_unsigned_to_nat(16u);
v___x_3334_ = lean_mk_array(v___x_3333_, v___x_3332_);
return v___x_3334_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1(void){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v_hist_3337_; 
v___x_3335_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0);
v___x_3336_ = lean_unsigned_to_nat(0u);
v_hist_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3337_, 0, v___x_3336_);
lean_ctor_set(v_hist_3337_, 1, v___x_3335_);
return v_hist_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_left_3338_, lean_object* v_right_3339_){
_start:
{
lean_object* v___x_3340_; lean_object* v_snd_3341_; lean_object* v_fst_3342_; lean_object* v_fst_3343_; lean_object* v_snd_3344_; lean_object* v___x_3345_; lean_object* v_snd_3346_; lean_object* v_fst_3347_; lean_object* v_fst_3348_; lean_object* v_snd_3349_; lean_object* v_start_3350_; lean_object* v_stop_3351_; lean_object* v___x_3352_; lean_object* v_hist_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v_start_3356_; lean_object* v_stop_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v_buckets_3360_; lean_object* v___x_3361_; lean_object* v___y_3363_; lean_object* v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v___x_3340_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(v_left_3338_, v_right_3339_);
v_snd_3341_ = lean_ctor_get(v___x_3340_, 1);
lean_inc(v_snd_3341_);
v_fst_3342_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_fst_3342_);
lean_dec_ref(v___x_3340_);
v_fst_3343_ = lean_ctor_get(v_snd_3341_, 0);
lean_inc(v_fst_3343_);
v_snd_3344_ = lean_ctor_get(v_snd_3341_, 1);
lean_inc(v_snd_3344_);
lean_dec(v_snd_3341_);
v___x_3345_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(v_fst_3343_, v_snd_3344_);
v_snd_3346_ = lean_ctor_get(v___x_3345_, 1);
lean_inc(v_snd_3346_);
v_fst_3347_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_fst_3347_);
lean_dec_ref(v___x_3345_);
v_fst_3348_ = lean_ctor_get(v_snd_3346_, 0);
lean_inc(v_fst_3348_);
v_snd_3349_ = lean_ctor_get(v_snd_3346_, 1);
lean_inc(v_snd_3349_);
lean_dec(v_snd_3346_);
v_start_3350_ = lean_ctor_get(v_fst_3347_, 1);
v_stop_3351_ = lean_ctor_get(v_fst_3347_, 2);
v___x_3352_ = lean_unsigned_to_nat(0u);
v_hist_3353_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1);
v___x_3354_ = lean_nat_sub(v_stop_3351_, v_start_3350_);
v___x_3355_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v___x_3354_, v_fst_3348_, v___x_3354_, v_fst_3347_, v___x_3352_, v_hist_3353_);
v_start_3356_ = lean_ctor_get(v_fst_3348_, 1);
v_stop_3357_ = lean_ctor_get(v_fst_3348_, 2);
v___x_3358_ = lean_nat_sub(v_stop_3357_, v_start_3356_);
v___x_3359_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v___x_3358_, v___x_3358_, v_fst_3348_, v___x_3354_, v___x_3352_, v___x_3355_);
lean_dec(v___x_3354_);
lean_dec(v___x_3358_);
v_buckets_3360_ = lean_ctor_get(v___x_3359_, 1);
lean_inc_ref(v_buckets_3360_);
lean_dec_ref(v___x_3359_);
v___x_3361_ = lean_box(0);
v___x_3389_ = lean_box(0);
v___x_3390_ = lean_array_get_size(v_buckets_3360_);
v___x_3391_ = lean_nat_dec_lt(v___x_3352_, v___x_3390_);
if (v___x_3391_ == 0)
{
lean_dec_ref(v_buckets_3360_);
v___y_3363_ = v___x_3389_;
goto v___jp_3362_;
}
else
{
size_t v___x_3392_; size_t v___x_3393_; lean_object* v___x_3394_; 
v___x_3392_ = lean_usize_of_nat(v___x_3390_);
v___x_3393_ = ((size_t)0ULL);
v___x_3394_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_buckets_3360_, v___x_3392_, v___x_3393_, v___x_3389_);
lean_dec_ref(v_buckets_3360_);
v___y_3363_ = v___x_3394_;
goto v___jp_3362_;
}
v___jp_3362_:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v___y_3363_, v___x_3361_);
lean_dec(v___y_3363_);
if (lean_obj_tag(v___x_3364_) == 1)
{
lean_object* v_val_3365_; lean_object* v_snd_3366_; lean_object* v_snd_3367_; lean_object* v_fst_3368_; lean_object* v_fst_3369_; lean_object* v_snd_3370_; lean_object* v___x_3371_; lean_object* v_fst_3372_; lean_object* v_snd_3373_; lean_object* v___x_3374_; lean_object* v_fst_3375_; lean_object* v_snd_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v_val_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_val_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v_snd_3366_ = lean_ctor_get(v_val_3365_, 1);
lean_inc(v_snd_3366_);
lean_dec(v_val_3365_);
v_snd_3367_ = lean_ctor_get(v_snd_3366_, 1);
lean_inc(v_snd_3367_);
v_fst_3368_ = lean_ctor_get(v_snd_3366_, 0);
lean_inc(v_fst_3368_);
lean_dec(v_snd_3366_);
v_fst_3369_ = lean_ctor_get(v_snd_3367_, 0);
lean_inc(v_fst_3369_);
v_snd_3370_ = lean_ctor_get(v_snd_3367_, 1);
lean_inc(v_snd_3370_);
lean_dec(v_snd_3367_);
v___x_3371_ = l_Subarray_split___redArg(v_fst_3347_, v_fst_3369_);
lean_dec(v_fst_3369_);
v_fst_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_fst_3372_);
v_snd_3373_ = lean_ctor_get(v___x_3371_, 1);
lean_inc(v_snd_3373_);
lean_dec_ref(v___x_3371_);
v___x_3374_ = l_Subarray_split___redArg(v_fst_3348_, v_snd_3370_);
lean_dec(v_snd_3370_);
v_fst_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_fst_3375_);
v_snd_3376_ = lean_ctor_get(v___x_3374_, 1);
lean_inc(v_snd_3376_);
lean_dec_ref(v___x_3374_);
v___x_3377_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_fst_3372_, v_fst_3375_);
v___x_3378_ = l_Array_append___redArg(v_fst_3342_, v___x_3377_);
lean_dec_ref(v___x_3377_);
v___x_3379_ = lean_unsigned_to_nat(1u);
v___x_3380_ = lean_mk_empty_array_with_capacity(v___x_3379_);
v___x_3381_ = lean_array_push(v___x_3380_, v_fst_3368_);
v___x_3382_ = l_Array_append___redArg(v___x_3378_, v___x_3381_);
lean_dec_ref(v___x_3381_);
v___x_3383_ = l_Subarray_drop___redArg(v_snd_3373_, v___x_3379_);
v___x_3384_ = l_Subarray_drop___redArg(v_snd_3376_, v___x_3379_);
v___x_3385_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3383_, v___x_3384_);
v___x_3386_ = l_Array_append___redArg(v___x_3382_, v___x_3385_);
lean_dec_ref(v___x_3385_);
v___x_3387_ = l_Array_append___redArg(v___x_3386_, v_snd_3349_);
lean_dec(v_snd_3349_);
return v___x_3387_;
}
else
{
lean_object* v___x_3388_; 
lean_dec(v___x_3364_);
lean_dec(v_fst_3348_);
lean_dec(v_fst_3347_);
v___x_3388_ = l_Array_append___redArg(v_fst_3342_, v_snd_3349_);
lean_dec(v_snd_3349_);
return v___x_3388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3395_, size_t v_i_3396_, lean_object* v_bs_3397_){
_start:
{
uint8_t v___x_3398_; 
v___x_3398_ = lean_usize_dec_lt(v_i_3396_, v_sz_3395_);
if (v___x_3398_ == 0)
{
return v_bs_3397_;
}
else
{
lean_object* v_v_3399_; lean_object* v___x_3400_; lean_object* v_bs_x27_3401_; uint8_t v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; size_t v___x_3405_; size_t v___x_3406_; lean_object* v___x_3407_; 
v_v_3399_ = lean_array_uget(v_bs_3397_, v_i_3396_);
v___x_3400_ = lean_unsigned_to_nat(0u);
v_bs_x27_3401_ = lean_array_uset(v_bs_3397_, v_i_3396_, v___x_3400_);
v___x_3402_ = 1;
v___x_3403_ = lean_box(v___x_3402_);
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
lean_ctor_set(v___x_3404_, 1, v_v_3399_);
v___x_3405_ = ((size_t)1ULL);
v___x_3406_ = lean_usize_add(v_i_3396_, v___x_3405_);
v___x_3407_ = lean_array_uset(v_bs_x27_3401_, v_i_3396_, v___x_3404_);
v_i_3396_ = v___x_3406_;
v_bs_3397_ = v___x_3407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3409_, lean_object* v_i_3410_, lean_object* v_bs_3411_){
_start:
{
size_t v_sz_boxed_3412_; size_t v_i_boxed_3413_; lean_object* v_res_3414_; 
v_sz_boxed_3412_ = lean_unbox_usize(v_sz_3409_);
lean_dec(v_sz_3409_);
v_i_boxed_3413_ = lean_unbox_usize(v_i_3410_);
lean_dec(v_i_3410_);
v_res_3414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3412_, v_i_boxed_3413_, v_bs_3411_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3422_, lean_object* v_edited_3423_){
_start:
{
lean_object* v_i_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v_i_3424_ = lean_unsigned_to_nat(0u);
v___x_3425_ = lean_array_get_size(v_original_3422_);
v___x_3426_ = lean_nat_dec_lt(v_i_3424_, v___x_3425_);
if (v___x_3426_ == 0)
{
size_t v_sz_3427_; size_t v___x_3428_; lean_object* v___x_3429_; 
lean_dec_ref(v_original_3422_);
v_sz_3427_ = lean_array_size(v_edited_3423_);
v___x_3428_ = ((size_t)0ULL);
v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3427_, v___x_3428_, v_edited_3423_);
return v___x_3429_;
}
else
{
lean_object* v___x_3430_; uint8_t v___x_3431_; 
v___x_3430_ = lean_array_get_size(v_edited_3423_);
v___x_3431_ = lean_nat_dec_lt(v_i_3424_, v___x_3430_);
if (v___x_3431_ == 0)
{
size_t v_sz_3432_; size_t v___x_3433_; lean_object* v___x_3434_; 
lean_dec_ref(v_edited_3423_);
v_sz_3432_ = lean_array_size(v_original_3422_);
v___x_3433_ = ((size_t)0ULL);
v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3432_, v___x_3433_, v_original_3422_);
return v___x_3434_;
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v_ds_3437_; lean_object* v___x_3438_; size_t v_sz_3439_; size_t v___x_3440_; lean_object* v___x_3441_; lean_object* v_snd_3442_; lean_object* v_fst_3443_; lean_object* v_fst_3444_; lean_object* v_snd_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3464_; 
lean_inc_ref(v_original_3422_);
v___x_3435_ = l_Array_toSubarray___redArg(v_original_3422_, v_i_3424_, v___x_3425_);
lean_inc_ref(v_edited_3423_);
v___x_3436_ = l_Array_toSubarray___redArg(v_edited_3423_, v_i_3424_, v___x_3430_);
v_ds_3437_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3435_, v___x_3436_);
v___x_3438_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3439_ = lean_array_size(v_ds_3437_);
v___x_3440_ = ((size_t)0ULL);
v___x_3441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_3430_, v_edited_3423_, v___x_3425_, v_original_3422_, v_ds_3437_, v_sz_3439_, v___x_3440_, v___x_3438_);
lean_dec_ref(v_ds_3437_);
v_snd_3442_ = lean_ctor_get(v___x_3441_, 1);
lean_inc(v_snd_3442_);
v_fst_3443_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_fst_3443_);
lean_dec_ref(v___x_3441_);
v_fst_3444_ = lean_ctor_get(v_snd_3442_, 0);
v_snd_3445_ = lean_ctor_get(v_snd_3442_, 1);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_snd_3442_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3447_ = v_snd_3442_;
v_isShared_3448_ = v_isSharedCheck_3464_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_snd_3445_);
lean_inc(v_fst_3444_);
lean_dec(v_snd_3442_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3464_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 1, v_fst_3444_);
lean_ctor_set(v___x_3447_, 0, v_fst_3443_);
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_fst_3443_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_fst_3444_);
v___x_3450_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3451_; lean_object* v_fst_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3461_; 
v___x_3451_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3425_, v_original_3422_, v___x_3450_);
lean_dec_ref(v_original_3422_);
v_fst_3452_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3461_ == 0)
{
lean_object* v_unused_3462_; 
v_unused_3462_ = lean_ctor_get(v___x_3451_, 1);
lean_dec(v_unused_3462_);
v___x_3454_ = v___x_3451_;
v_isShared_3455_ = v_isSharedCheck_3461_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_fst_3452_);
lean_dec(v___x_3451_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3461_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 1, v_snd_3445_);
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_fst_3452_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_snd_3445_);
v___x_3457_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; lean_object* v_fst_3459_; 
v___x_3458_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3430_, v_edited_3423_, v___x_3457_);
lean_dec_ref(v_edited_3423_);
v_fst_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_fst_3459_);
lean_dec_ref(v___x_3458_);
return v_fst_3459_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3465_, lean_object* v_x_3466_, lean_object* v_x_3467_){
_start:
{
if (lean_obj_tag(v_x_3466_) == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = l_List_reverse___redArg(v_x_3467_);
v___x_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
return v___x_3470_;
}
else
{
lean_object* v_head_3471_; lean_object* v_tail_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3481_; 
v_head_3471_ = lean_ctor_get(v_x_3466_, 0);
v_tail_3472_ = lean_ctor_get(v_x_3466_, 1);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_x_3466_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3474_ = v_x_3466_;
v_isShared_3475_ = v_isSharedCheck_3481_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_tail_3472_);
lean_inc(v_head_3471_);
lean_dec(v_x_3466_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3481_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3476_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3471_, v___y_3465_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 1, v_x_3467_);
lean_ctor_set(v___x_3474_, 0, v___x_3476_);
v___x_3478_ = v___x_3474_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_x_3467_);
v___x_3478_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
v_x_3466_ = v_tail_3472_;
v_x_3467_ = v___x_3478_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3482_, lean_object* v_x_3483_, lean_object* v_x_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3482_, v_x_3483_, v_x_3484_);
lean_dec(v___y_3482_);
return v_res_3486_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3493_ = l_Lean_stringToMessageData(v___x_3492_);
return v___x_3493_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = l_Lean_MessageLog_empty;
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_){
_start:
{
lean_object* v___x_3507_; uint8_t v___x_3508_; 
v___x_3507_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
lean_inc(v_x_3503_);
v___x_3508_ = l_Lean_Syntax_isOfKind(v_x_3503_, v___x_3507_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; 
lean_dec(v_x_3503_);
v___x_3509_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3509_;
}
else
{
lean_object* v___x_3510_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; uint8_t v___y_3551_; lean_object* v___y_3616_; lean_object* v___y_3617_; uint8_t v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; uint8_t v___y_3621_; lean_object* v___y_3622_; uint8_t v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v_dc_x3f_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___x_3759_; lean_object* v___x_3760_; uint8_t v___x_3761_; 
v___x_3510_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3759_ = lean_unsigned_to_nat(0u);
v___x_3760_ = l_Lean_Syntax_getArg(v_x_3503_, v___x_3759_);
v___x_3761_ = l_Lean_Syntax_isNone(v___x_3760_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; uint8_t v___x_3763_; 
v___x_3762_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3760_);
v___x_3763_ = l_Lean_Syntax_matchesNull(v___x_3760_, v___x_3762_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; 
lean_dec(v___x_3760_);
lean_dec(v_x_3503_);
v___x_3764_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3764_;
}
else
{
lean_object* v_dc_x3f_3765_; 
v_dc_x3f_3765_ = l_Lean_Syntax_getArg(v___x_3760_, v___x_3759_);
lean_dec(v___x_3760_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3768_; uint8_t v___x_3769_; 
v___x_3768_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3765_);
v___x_3769_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3765_, v___x_3768_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; 
lean_dec(v_dc_x3f_3765_);
lean_dec(v_x_3503_);
v___x_3770_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3770_;
}
else
{
goto v___jp_3766_;
}
}
else
{
goto v___jp_3766_;
}
v___jp_3766_:
{
lean_object* v___x_3767_; 
v___x_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3767_, 0, v_dc_x3f_3765_);
v_dc_x3f_3740_ = v___x_3767_;
v___y_3741_ = v_a_3504_;
v___y_3742_ = v_a_3505_;
goto v___jp_3739_;
}
}
}
else
{
lean_object* v___x_3771_; 
lean_dec(v___x_3760_);
v___x_3771_ = lean_box(0);
v_dc_x3f_3740_ = v___x_3771_;
v___y_3741_ = v_a_3504_;
v___y_3742_ = v_a_3505_;
goto v___jp_3739_;
}
v___jp_3511_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3517_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3518_ = l_Lean_stringToMessageData(v___y_3516_);
v___x_3519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3517_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
v___x_3520_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3515_, v___x_3519_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3515_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3540_; 
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3540_ == 0)
{
lean_object* v_unused_3541_; 
v_unused_3541_ = lean_ctor_get(v___x_3520_, 0);
lean_dec(v_unused_3541_);
v___x_3522_ = v___x_3520_;
v_isShared_3523_ = v_isSharedCheck_3540_;
goto v_resetjp_3521_;
}
else
{
lean_dec(v___x_3520_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3540_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Lean_Elab_Command_getRef___redArg(v___y_3512_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3529_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3524_, 1);
v___x_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3510_);
lean_ctor_set(v___x_3526_, 1, v___y_3514_);
v___x_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3527_, 0, v_a_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set_tag(v___x_3522_, 10);
lean_ctor_set(v___x_3522_, 0, v___x_3527_);
v___x_3529_ = v___x_3522_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3529_, v___y_3512_, v___y_3513_);
return v___x_3530_;
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_del_object(v___x_3522_);
lean_dec_ref(v___y_3514_);
v_a_3532_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3524_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3524_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3514_);
return v___x_3520_;
}
}
v___jp_3542_:
{
if (v___y_3551_ == 0)
{
lean_object* v___x_3552_; lean_object* v_env_3553_; lean_object* v_scopes_3554_; lean_object* v_usedQuotCtxts_3555_; lean_object* v_nextMacroScope_3556_; lean_object* v_maxRecDepth_3557_; lean_object* v_ngen_3558_; lean_object* v_auxDeclNGen_3559_; lean_object* v_infoState_3560_; lean_object* v_traceState_3561_; lean_object* v_snapshotTasks_3562_; lean_object* v_prevLinterStates_3563_; lean_object* v_codeQualityEntryTasks_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3589_; 
lean_dec(v___y_3543_);
v___x_3552_ = lean_st_ref_take(v___y_3546_);
v_env_3553_ = lean_ctor_get(v___x_3552_, 0);
v_scopes_3554_ = lean_ctor_get(v___x_3552_, 2);
v_usedQuotCtxts_3555_ = lean_ctor_get(v___x_3552_, 3);
v_nextMacroScope_3556_ = lean_ctor_get(v___x_3552_, 4);
v_maxRecDepth_3557_ = lean_ctor_get(v___x_3552_, 5);
v_ngen_3558_ = lean_ctor_get(v___x_3552_, 6);
v_auxDeclNGen_3559_ = lean_ctor_get(v___x_3552_, 7);
v_infoState_3560_ = lean_ctor_get(v___x_3552_, 8);
v_traceState_3561_ = lean_ctor_get(v___x_3552_, 9);
v_snapshotTasks_3562_ = lean_ctor_get(v___x_3552_, 10);
v_prevLinterStates_3563_ = lean_ctor_get(v___x_3552_, 11);
v_codeQualityEntryTasks_3564_ = lean_ctor_get(v___x_3552_, 12);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; 
v_unused_3590_ = lean_ctor_get(v___x_3552_, 1);
lean_dec(v_unused_3590_);
v___x_3566_ = v___x_3552_;
v_isShared_3567_ = v_isSharedCheck_3589_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3564_);
lean_inc(v_prevLinterStates_3563_);
lean_inc(v_snapshotTasks_3562_);
lean_inc(v_traceState_3561_);
lean_inc(v_infoState_3560_);
lean_inc(v_auxDeclNGen_3559_);
lean_inc(v_ngen_3558_);
lean_inc(v_maxRecDepth_3557_);
lean_inc(v_nextMacroScope_3556_);
lean_inc(v_usedQuotCtxts_3555_);
lean_inc(v_scopes_3554_);
lean_inc(v_env_3553_);
lean_dec(v___x_3552_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3589_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 1, v___y_3545_);
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_env_3553_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v___y_3545_);
lean_ctor_set(v_reuseFailAlloc_3588_, 2, v_scopes_3554_);
lean_ctor_set(v_reuseFailAlloc_3588_, 3, v_usedQuotCtxts_3555_);
lean_ctor_set(v_reuseFailAlloc_3588_, 4, v_nextMacroScope_3556_);
lean_ctor_set(v_reuseFailAlloc_3588_, 5, v_maxRecDepth_3557_);
lean_ctor_set(v_reuseFailAlloc_3588_, 6, v_ngen_3558_);
lean_ctor_set(v_reuseFailAlloc_3588_, 7, v_auxDeclNGen_3559_);
lean_ctor_set(v_reuseFailAlloc_3588_, 8, v_infoState_3560_);
lean_ctor_set(v_reuseFailAlloc_3588_, 9, v_traceState_3561_);
lean_ctor_set(v_reuseFailAlloc_3588_, 10, v_snapshotTasks_3562_);
lean_ctor_set(v_reuseFailAlloc_3588_, 11, v_prevLinterStates_3563_);
lean_ctor_set(v_reuseFailAlloc_3588_, 12, v_codeQualityEntryTasks_3564_);
v___x_3569_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v_scopes_3573_; lean_object* v___x_3574_; lean_object* v_opts_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v___x_3570_ = lean_st_ref_put(v___y_3546_, v___x_3569_);
v___x_3571_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3572_ = lean_st_ref_get(v___y_3546_);
v_scopes_3573_ = lean_ctor_get(v___x_3572_, 2);
lean_inc(v_scopes_3573_);
lean_dec(v___x_3572_);
v___x_3574_ = l_List_head_x21___redArg(v___x_3571_, v_scopes_3573_);
lean_dec(v_scopes_3573_);
v_opts_3575_ = lean_ctor_get(v___x_3574_, 1);
lean_inc_ref(v_opts_3575_);
lean_dec(v___x_3574_);
v___x_3576_ = l_Lean_guard__msgs_diff;
v___x_3577_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3575_, v___x_3576_);
lean_dec_ref(v_opts_3575_);
if (v___x_3577_ == 0)
{
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3547_);
lean_inc_ref(v___y_3548_);
v___y_3512_ = v___y_3544_;
v___y_3513_ = v___y_3546_;
v___y_3514_ = v___y_3548_;
v___y_3515_ = v___y_3549_;
v___y_3516_ = v___y_3548_;
goto v___jp_3511_;
}
else
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3578_ = lean_string_utf8_byte_size(v___y_3550_);
lean_inc(v___y_3547_);
lean_inc_ref(v___y_3550_);
v___x_3579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3579_, 0, v___y_3550_);
lean_ctor_set(v___x_3579_, 1, v___y_3547_);
lean_ctor_set(v___x_3579_, 2, v___x_3578_);
v___x_3580_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
v___x_3581_ = lean_mk_empty_array_with_capacity(v___y_3547_);
lean_inc_ref(v___x_3581_);
v___x_3582_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3550_, v___x_3579_, v___x_3578_, v___x_3580_, v___x_3581_);
lean_dec_ref_known(v___x_3579_, 3);
v___x_3583_ = lean_string_utf8_byte_size(v___y_3548_);
lean_inc_ref_n(v___y_3548_, 2);
v___x_3584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3584_, 0, v___y_3548_);
lean_ctor_set(v___x_3584_, 1, v___y_3547_);
lean_ctor_set(v___x_3584_, 2, v___x_3583_);
v___x_3585_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3548_, v___x_3584_, v___x_3583_, v___x_3580_, v___x_3581_);
lean_dec_ref_known(v___x_3584_, 3);
v___x_3586_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3582_, v___x_3585_);
v___x_3587_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3586_);
lean_dec_ref(v___x_3586_);
v___y_3512_ = v___y_3544_;
v___y_3513_ = v___y_3546_;
v___y_3514_ = v___y_3548_;
v___y_3515_ = v___y_3549_;
v___y_3516_ = v___x_3587_;
goto v___jp_3511_;
}
}
}
}
else
{
lean_object* v___x_3591_; lean_object* v_env_3592_; lean_object* v_scopes_3593_; lean_object* v_usedQuotCtxts_3594_; lean_object* v_nextMacroScope_3595_; lean_object* v_maxRecDepth_3596_; lean_object* v_ngen_3597_; lean_object* v_auxDeclNGen_3598_; lean_object* v_infoState_3599_; lean_object* v_traceState_3600_; lean_object* v_snapshotTasks_3601_; lean_object* v_prevLinterStates_3602_; lean_object* v_codeQualityEntryTasks_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3613_; 
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3545_);
v___x_3591_ = lean_st_ref_take(v___y_3546_);
v_env_3592_ = lean_ctor_get(v___x_3591_, 0);
v_scopes_3593_ = lean_ctor_get(v___x_3591_, 2);
v_usedQuotCtxts_3594_ = lean_ctor_get(v___x_3591_, 3);
v_nextMacroScope_3595_ = lean_ctor_get(v___x_3591_, 4);
v_maxRecDepth_3596_ = lean_ctor_get(v___x_3591_, 5);
v_ngen_3597_ = lean_ctor_get(v___x_3591_, 6);
v_auxDeclNGen_3598_ = lean_ctor_get(v___x_3591_, 7);
v_infoState_3599_ = lean_ctor_get(v___x_3591_, 8);
v_traceState_3600_ = lean_ctor_get(v___x_3591_, 9);
v_snapshotTasks_3601_ = lean_ctor_get(v___x_3591_, 10);
v_prevLinterStates_3602_ = lean_ctor_get(v___x_3591_, 11);
v_codeQualityEntryTasks_3603_ = lean_ctor_get(v___x_3591_, 12);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; 
v_unused_3614_ = lean_ctor_get(v___x_3591_, 1);
lean_dec(v_unused_3614_);
v___x_3605_ = v___x_3591_;
v_isShared_3606_ = v_isSharedCheck_3613_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3603_);
lean_inc(v_prevLinterStates_3602_);
lean_inc(v_snapshotTasks_3601_);
lean_inc(v_traceState_3600_);
lean_inc(v_infoState_3599_);
lean_inc(v_auxDeclNGen_3598_);
lean_inc(v_ngen_3597_);
lean_inc(v_maxRecDepth_3596_);
lean_inc(v_nextMacroScope_3595_);
lean_inc(v_usedQuotCtxts_3594_);
lean_inc(v_scopes_3593_);
lean_inc(v_env_3592_);
lean_dec(v___x_3591_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3613_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; lean_object* v___x_3609_; 
v___x_3607_ = lean_box(0);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 1, v___y_3543_);
v___x_3609_ = v___x_3605_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_env_3592_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v___y_3543_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_scopes_3593_);
lean_ctor_set(v_reuseFailAlloc_3612_, 3, v_usedQuotCtxts_3594_);
lean_ctor_set(v_reuseFailAlloc_3612_, 4, v_nextMacroScope_3595_);
lean_ctor_set(v_reuseFailAlloc_3612_, 5, v_maxRecDepth_3596_);
lean_ctor_set(v_reuseFailAlloc_3612_, 6, v_ngen_3597_);
lean_ctor_set(v_reuseFailAlloc_3612_, 7, v_auxDeclNGen_3598_);
lean_ctor_set(v_reuseFailAlloc_3612_, 8, v_infoState_3599_);
lean_ctor_set(v_reuseFailAlloc_3612_, 9, v_traceState_3600_);
lean_ctor_set(v_reuseFailAlloc_3612_, 10, v_snapshotTasks_3601_);
lean_ctor_set(v_reuseFailAlloc_3612_, 11, v_prevLinterStates_3602_);
lean_ctor_set(v_reuseFailAlloc_3612_, 12, v_codeQualityEntryTasks_3603_);
v___x_3609_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3610_ = lean_st_ref_put(v___y_3546_, v___x_3609_);
v___x_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3607_);
return v___x_3611_;
}
}
}
}
v___jp_3615_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v_a_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v_str_3638_; lean_object* v_startInclusive_3639_; lean_object* v_endExclusive_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3655_; 
v___x_3628_ = l_Lean_MessageLog_toList(v___y_3625_);
lean_dec(v___y_3625_);
v___x_3629_ = lean_box(0);
v___x_3630_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3627_, v___x_3628_, v___x_3629_);
lean_dec(v___y_3627_);
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref(v___x_3630_);
v___x_3632_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3623_, v_a_3631_);
v___x_3633_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4));
v___x_3634_ = l_String_intercalate(v___x_3633_, v___x_3632_);
v___x_3635_ = lean_string_utf8_byte_size(v___x_3634_);
lean_inc(v___y_3622_);
v___x_3636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3634_);
lean_ctor_set(v___x_3636_, 1, v___y_3622_);
lean_ctor_set(v___x_3636_, 2, v___x_3635_);
v___x_3637_ = l_String_Slice_trimAscii(v___x_3636_);
v_str_3638_ = lean_ctor_get(v___x_3637_, 0);
v_startInclusive_3639_ = lean_ctor_get(v___x_3637_, 1);
v_endExclusive_3640_ = lean_ctor_get(v___x_3637_, 2);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3642_ = v___x_3637_;
v_isShared_3643_ = v_isSharedCheck_3655_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_endExclusive_3640_);
lean_inc(v_startInclusive_3639_);
lean_inc(v_str_3638_);
lean_dec(v___x_3637_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3655_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; 
v___x_3644_ = lean_string_utf8_extract_fast(v_str_3638_, v_startInclusive_3639_, v_endExclusive_3640_);
lean_dec(v_endExclusive_3640_);
lean_dec(v_startInclusive_3639_);
lean_dec_ref(v_str_3638_);
if (v___y_3621_ == 0)
{
lean_object* v___x_3645_; lean_object* v___x_3646_; uint8_t v___x_3647_; 
lean_del_object(v___x_3642_);
lean_inc_ref(v___y_3626_);
v___x_3645_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3618_, v___y_3626_);
lean_inc_ref(v___x_3644_);
v___x_3646_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3618_, v___x_3644_);
v___x_3647_ = lean_string_dec_eq(v___x_3645_, v___x_3646_);
lean_dec_ref(v___x_3646_);
lean_dec_ref(v___x_3645_);
v___y_3543_ = v___y_3616_;
v___y_3544_ = v___y_3617_;
v___y_3545_ = v___y_3619_;
v___y_3546_ = v___y_3620_;
v___y_3547_ = v___y_3622_;
v___y_3548_ = v___x_3644_;
v___y_3549_ = v___y_3624_;
v___y_3550_ = v___y_3626_;
v___y_3551_ = v___x_3647_;
goto v___jp_3542_;
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3652_; 
lean_inc_ref(v___x_3644_);
v___x_3648_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3618_, v___x_3644_);
lean_inc_ref(v___y_3626_);
v___x_3649_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3618_, v___y_3626_);
v___x_3650_ = lean_string_utf8_byte_size(v___x_3648_);
lean_inc(v___y_3622_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 2, v___x_3650_);
lean_ctor_set(v___x_3642_, 1, v___y_3622_);
lean_ctor_set(v___x_3642_, 0, v___x_3648_);
v___x_3652_ = v___x_3642_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v___y_3622_);
lean_ctor_set(v_reuseFailAlloc_3654_, 2, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
uint8_t v___x_3653_; 
v___x_3653_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3649_, v___x_3652_);
lean_dec_ref(v___x_3652_);
v___y_3543_ = v___y_3616_;
v___y_3544_ = v___y_3617_;
v___y_3545_ = v___y_3619_;
v___y_3546_ = v___y_3620_;
v___y_3547_ = v___y_3622_;
v___y_3548_ = v___x_3644_;
v___y_3549_ = v___y_3624_;
v___y_3550_ = v___y_3626_;
v___y_3551_ = v___x_3653_;
goto v___jp_3542_;
}
}
}
}
v___jp_3656_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v_str_3667_; lean_object* v_startInclusive_3668_; lean_object* v_endExclusive_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3663_ = lean_unsigned_to_nat(0u);
v___x_3664_ = lean_string_utf8_byte_size(v___y_3662_);
v___x_3665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3665_, 0, v___y_3662_);
lean_ctor_set(v___x_3665_, 1, v___x_3663_);
lean_ctor_set(v___x_3665_, 2, v___x_3664_);
v___x_3666_ = l_String_Slice_trimAscii(v___x_3665_);
v_str_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc_ref(v_str_3667_);
v_startInclusive_3668_ = lean_ctor_get(v___x_3666_, 1);
lean_inc(v_startInclusive_3668_);
v_endExclusive_3669_ = lean_ctor_get(v___x_3666_, 2);
lean_inc(v_endExclusive_3669_);
lean_dec_ref(v___x_3666_);
v___x_3670_ = lean_string_utf8_extract_fast(v_str_3667_, v_startInclusive_3668_, v_endExclusive_3669_);
lean_dec(v_endExclusive_3669_);
lean_dec(v_startInclusive_3668_);
lean_dec_ref(v_str_3667_);
v___x_3671_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3670_);
v___x_3672_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3661_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v_filterFn_3674_; uint8_t v_whitespace_3675_; uint8_t v_ordering_3676_; uint8_t v_reportPositions_3677_; uint8_t v_substring_3678_; lean_object* v___x_3679_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___x_3672_, 1);
v_filterFn_3674_ = lean_ctor_get(v_a_3673_, 0);
lean_inc_ref(v_filterFn_3674_);
v_whitespace_3675_ = lean_ctor_get_uint8(v_a_3673_, sizeof(void*)*1);
v_ordering_3676_ = lean_ctor_get_uint8(v_a_3673_, sizeof(void*)*1 + 1);
v_reportPositions_3677_ = lean_ctor_get_uint8(v_a_3673_, sizeof(void*)*1 + 2);
v_substring_3678_ = lean_ctor_get_uint8(v_a_3673_, sizeof(void*)*1 + 3);
lean_dec(v_a_3673_);
v___x_3679_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3659_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v_a_3684_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref_known(v___x_3679_, 1);
v___x_3681_ = l_Lean_MessageLog_toList(v_a_3680_);
v___x_3682_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5);
v___x_3683_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3674_, v___x_3681_, v___x_3682_);
lean_dec(v___x_3681_);
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref(v___x_3683_);
if (v_reportPositions_3677_ == 0)
{
lean_object* v_fst_3685_; lean_object* v_snd_3686_; lean_object* v___x_3687_; 
v_fst_3685_ = lean_ctor_get(v_a_3684_, 0);
lean_inc(v_fst_3685_);
v_snd_3686_ = lean_ctor_get(v_a_3684_, 1);
lean_inc(v_snd_3686_);
lean_dec(v_a_3684_);
v___x_3687_ = lean_box(0);
v___y_3616_ = v_snd_3686_;
v___y_3617_ = v___y_3657_;
v___y_3618_ = v_whitespace_3675_;
v___y_3619_ = v_a_3680_;
v___y_3620_ = v___y_3658_;
v___y_3621_ = v_substring_3678_;
v___y_3622_ = v___x_3663_;
v___y_3623_ = v_ordering_3676_;
v___y_3624_ = v___y_3660_;
v___y_3625_ = v_fst_3685_;
v___y_3626_ = v___x_3671_;
v___y_3627_ = v___x_3687_;
goto v___jp_3615_;
}
else
{
lean_object* v_fst_3688_; lean_object* v_snd_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; 
v_fst_3688_ = lean_ctor_get(v_a_3684_, 0);
lean_inc(v_fst_3688_);
v_snd_3689_ = lean_ctor_get(v_a_3684_, 1);
lean_inc(v_snd_3689_);
lean_dec(v_a_3684_);
v___x_3690_ = 0;
v___x_3691_ = l_Lean_Syntax_getPos_x3f(v___y_3660_, v___x_3690_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v___x_3692_; 
v___x_3692_ = lean_box(0);
v___y_3616_ = v_snd_3689_;
v___y_3617_ = v___y_3657_;
v___y_3618_ = v_whitespace_3675_;
v___y_3619_ = v_a_3680_;
v___y_3620_ = v___y_3658_;
v___y_3621_ = v_substring_3678_;
v___y_3622_ = v___x_3663_;
v___y_3623_ = v_ordering_3676_;
v___y_3624_ = v___y_3660_;
v___y_3625_ = v_fst_3688_;
v___y_3626_ = v___x_3671_;
v___y_3627_ = v___x_3692_;
goto v___jp_3615_;
}
else
{
lean_object* v_val_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3703_; 
v_val_3693_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3695_ = v___x_3691_;
v_isShared_3696_ = v_isSharedCheck_3703_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_val_3693_);
lean_dec(v___x_3691_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3703_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v_fileMap_3697_; lean_object* v___x_3698_; lean_object* v_line_3699_; lean_object* v___x_3701_; 
v_fileMap_3697_ = lean_ctor_get(v___y_3657_, 1);
lean_inc_ref(v_fileMap_3697_);
v___x_3698_ = l_Lean_FileMap_toPosition(v_fileMap_3697_, v_val_3693_);
lean_dec(v_val_3693_);
v_line_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_line_3699_);
lean_dec_ref(v___x_3698_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 0, v_line_3699_);
v___x_3701_ = v___x_3695_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_line_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
v___y_3616_ = v_snd_3689_;
v___y_3617_ = v___y_3657_;
v___y_3618_ = v_whitespace_3675_;
v___y_3619_ = v_a_3680_;
v___y_3620_ = v___y_3658_;
v___y_3621_ = v_substring_3678_;
v___y_3622_ = v___x_3663_;
v___y_3623_ = v_ordering_3676_;
v___y_3624_ = v___y_3660_;
v___y_3625_ = v_fst_3688_;
v___y_3626_ = v___x_3671_;
v___y_3627_ = v___x_3701_;
goto v___jp_3615_;
}
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v_filterFn_3674_);
lean_dec_ref(v___x_3671_);
lean_dec(v___y_3660_);
v_a_3704_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3679_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3679_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec_ref(v___x_3671_);
lean_dec(v___y_3660_);
lean_dec(v___y_3659_);
v_a_3712_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3672_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3672_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
v___jp_3720_:
{
if (lean_obj_tag(v___y_3723_) == 0)
{
lean_object* v___x_3727_; 
v___x_3727_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_3657_ = v___y_3721_;
v___y_3658_ = v___y_3722_;
v___y_3659_ = v___y_3724_;
v___y_3660_ = v___y_3725_;
v___y_3661_ = v___y_3726_;
v___y_3662_ = v___x_3727_;
goto v___jp_3656_;
}
else
{
lean_object* v_val_3728_; lean_object* v___x_3729_; 
v_val_3728_ = lean_ctor_get(v___y_3723_, 0);
lean_inc(v_val_3728_);
lean_dec_ref_known(v___y_3723_, 1);
v___x_3729_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3728_, v___y_3721_, v___y_3722_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v___y_3657_ = v___y_3721_;
v___y_3658_ = v___y_3722_;
v___y_3659_ = v___y_3724_;
v___y_3660_ = v___y_3725_;
v___y_3661_ = v___y_3726_;
v___y_3662_ = v_a_3730_;
goto v___jp_3656_;
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec(v___y_3724_);
v_a_3731_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3729_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3729_);
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
}
v___jp_3739_:
{
lean_object* v___x_3743_; lean_object* v_tk_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3743_ = lean_unsigned_to_nat(1u);
v_tk_3744_ = l_Lean_Syntax_getArg(v_x_3503_, v___x_3743_);
v___x_3745_ = lean_unsigned_to_nat(2u);
v___x_3746_ = l_Lean_Syntax_getArg(v_x_3503_, v___x_3745_);
v___x_3747_ = lean_unsigned_to_nat(4u);
v___x_3748_ = l_Lean_Syntax_getArg(v_x_3503_, v___x_3747_);
lean_dec(v_x_3503_);
v___x_3749_ = l_Lean_Syntax_getOptional_x3f(v___x_3746_);
lean_dec(v___x_3746_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_box(0);
v___y_3721_ = v___y_3741_;
v___y_3722_ = v___y_3742_;
v___y_3723_ = v_dc_x3f_3740_;
v___y_3724_ = v___x_3748_;
v___y_3725_ = v_tk_3744_;
v___y_3726_ = v___x_3750_;
goto v___jp_3720_;
}
else
{
lean_object* v_val_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
v_val_3751_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3749_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_val_3751_);
lean_dec(v___x_3749_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_val_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
v___y_3721_ = v___y_3741_;
v___y_3722_ = v___y_3742_;
v___y_3723_ = v_dc_x3f_3740_;
v___y_3724_ = v___x_3748_;
v___y_3725_ = v_tk_3744_;
v___y_3726_ = v___x_3756_;
goto v___jp_3720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3772_, v_a_3773_, v_a_3774_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3777_, lean_object* v_as_3778_, lean_object* v_as_x27_3779_, lean_object* v_b_3780_, lean_object* v_a_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3777_, v_as_x27_3779_, v_b_3780_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3786_, lean_object* v_as_3787_, lean_object* v_as_x27_3788_, lean_object* v_b_3789_, lean_object* v_a_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3786_, v_as_3787_, v_as_x27_3788_, v_b_3789_, v_a_3790_, v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v_as_x27_3788_);
lean_dec(v_as_3787_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3795_, lean_object* v_x_3796_, lean_object* v_x_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3795_, v_x_3796_, v_x_3797_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3802_, lean_object* v_x_3803_, lean_object* v_x_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3802_, v_x_3803_, v_x_3804_, v___y_3805_, v___y_3806_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3802_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___x_3813_; 
v___x_3813_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3809_, v___y_3811_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3819_, lean_object* v___x_3820_, lean_object* v___x_3821_, lean_object* v_inst_3822_, lean_object* v_R_3823_, lean_object* v_a_3824_, lean_object* v_b_3825_){
_start:
{
lean_object* v___x_3826_; 
v___x_3826_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3819_, v___x_3820_, v___x_3821_, v_a_3824_, v_b_3825_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3827_, lean_object* v___x_3828_, lean_object* v___x_3829_, lean_object* v_inst_3830_, lean_object* v_R_3831_, lean_object* v_a_3832_, lean_object* v_b_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3827_, v___x_3828_, v___x_3829_, v_inst_3830_, v_R_3831_, v_a_3832_, v_b_3833_);
lean_dec_ref(v___x_3828_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3835_, v___y_3837_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3840_, v___y_3841_, v___y_3842_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3845_, lean_object* v___x_3846_, lean_object* v___x_3847_, lean_object* v_inst_3848_, lean_object* v_R_3849_, lean_object* v_a_3850_, lean_object* v_b_3851_){
_start:
{
lean_object* v___x_3852_; 
v___x_3852_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3845_, v___x_3846_, v___x_3847_, v_a_3850_, v_b_3851_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3853_, lean_object* v___x_3854_, lean_object* v___x_3855_, lean_object* v_inst_3856_, lean_object* v_R_3857_, lean_object* v_a_3858_, lean_object* v_b_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3853_, v___x_3854_, v___x_3855_, v_inst_3856_, v_R_3857_, v_a_3858_, v_b_3859_);
lean_dec_ref(v___x_3854_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v___x_3861_, lean_object* v_original_3862_, lean_object* v_a_3863_, lean_object* v_inst_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_3861_, v_original_3862_, v_a_3863_, v_a_3865_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___boxed(lean_object* v___x_3867_, lean_object* v_original_3868_, lean_object* v_a_3869_, lean_object* v_inst_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3867_, v_original_3868_, v_a_3869_, v_inst_3870_, v_a_3871_);
lean_dec_ref(v_a_3869_);
lean_dec_ref(v_original_3868_);
lean_dec(v___x_3867_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v___x_3873_, lean_object* v_edited_3874_, lean_object* v_a_3875_, lean_object* v_inst_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_3873_, v_edited_3874_, v_a_3875_, v_a_3877_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v___x_3879_, lean_object* v_edited_3880_, lean_object* v_a_3881_, lean_object* v_inst_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v___x_3879_, v_edited_3880_, v_a_3881_, v_inst_3882_, v_a_3883_);
lean_dec_ref(v_a_3881_);
lean_dec_ref(v_edited_3880_);
lean_dec(v___x_3879_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3885_, lean_object* v_original_3886_, lean_object* v_inst_3887_, lean_object* v_a_3888_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3885_, v_original_3886_, v_a_3888_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3890_, lean_object* v_original_3891_, lean_object* v_inst_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3890_, v_original_3891_, v_inst_3892_, v_a_3893_);
lean_dec_ref(v_original_3891_);
lean_dec(v___x_3890_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3895_, lean_object* v_edited_3896_, lean_object* v_inst_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3895_, v_edited_3896_, v_a_3898_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3900_, lean_object* v_edited_3901_, lean_object* v_inst_3902_, lean_object* v_a_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3900_, v_edited_3901_, v_inst_3902_, v_a_3903_);
lean_dec_ref(v_edited_3901_);
lean_dec(v___x_3900_);
return v_res_3904_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3905_, lean_object* v_inst_3906_, lean_object* v_R_3907_, lean_object* v_a_3908_, uint8_t v_b_3909_, lean_object* v_c_3910_){
_start:
{
uint8_t v___x_3911_; 
v___x_3911_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3905_, v_a_3908_, v_b_3909_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3912_, lean_object* v_inst_3913_, lean_object* v_R_3914_, lean_object* v_a_3915_, lean_object* v_b_3916_, lean_object* v_c_3917_){
_start:
{
uint8_t v_b_boxed_3918_; uint8_t v_res_3919_; lean_object* v_r_3920_; 
v_b_boxed_3918_ = lean_unbox(v_b_3916_);
v_res_3919_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3912_, v_inst_3913_, v_R_3914_, v_a_3915_, v_b_boxed_3918_, v_c_3917_);
lean_dec_ref(v_s_3912_);
v_r_3920_ = lean_box(v_res_3919_);
return v_r_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3921_, lean_object* v_ref_3922_, lean_object* v_msg_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3922_, v_msg_3923_, v___y_3924_, v___y_3925_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3928_, lean_object* v_ref_3929_, lean_object* v_msg_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3928_, v_ref_3929_, v_msg_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v_ref_3929_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(lean_object* v_as_3935_, lean_object* v_as_x27_3936_, lean_object* v_b_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3936_, v_b_3937_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___boxed(lean_object* v_as_3940_, lean_object* v_as_x27_3941_, lean_object* v_b_3942_, lean_object* v_a_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(v_as_3940_, v_as_x27_3941_, v_b_3942_, v_a_3943_);
lean_dec(v_as_x27_3941_);
lean_dec(v_as_3940_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(lean_object* v_lsize_3945_, lean_object* v_rsize_3946_, lean_object* v_histogram_3947_, lean_object* v_index_3948_, lean_object* v_val_3949_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_histogram_3947_, v_index_3948_, v_val_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___boxed(lean_object* v_lsize_3951_, lean_object* v_rsize_3952_, lean_object* v_histogram_3953_, lean_object* v_index_3954_, lean_object* v_val_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(v_lsize_3951_, v_rsize_3952_, v_histogram_3953_, v_index_3954_, v_val_3955_);
lean_dec(v_rsize_3952_);
lean_dec(v_lsize_3951_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(lean_object* v_upperBound_3957_, lean_object* v___x_3958_, lean_object* v_fst_3959_, lean_object* v___x_3960_, lean_object* v_inst_3961_, lean_object* v_R_3962_, lean_object* v_a_3963_, lean_object* v_b_3964_, lean_object* v_c_3965_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3957_, v___x_3958_, v_fst_3959_, v___x_3960_, v_a_3963_, v_b_3964_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___boxed(lean_object* v_upperBound_3967_, lean_object* v___x_3968_, lean_object* v_fst_3969_, lean_object* v___x_3970_, lean_object* v_inst_3971_, lean_object* v_R_3972_, lean_object* v_a_3973_, lean_object* v_b_3974_, lean_object* v_c_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(v_upperBound_3967_, v___x_3968_, v_fst_3969_, v___x_3970_, v_inst_3971_, v_R_3972_, v_a_3973_, v_b_3974_, v_c_3975_);
lean_dec(v___x_3970_);
lean_dec_ref(v_fst_3969_);
lean_dec(v___x_3968_);
lean_dec(v_upperBound_3967_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(lean_object* v_lsize_3977_, lean_object* v_rsize_3978_, lean_object* v_histogram_3979_, lean_object* v_index_3980_, lean_object* v_val_3981_){
_start:
{
lean_object* v___x_3982_; 
v___x_3982_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_histogram_3979_, v_index_3980_, v_val_3981_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___boxed(lean_object* v_lsize_3983_, lean_object* v_rsize_3984_, lean_object* v_histogram_3985_, lean_object* v_index_3986_, lean_object* v_val_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(v_lsize_3983_, v_rsize_3984_, v_histogram_3985_, v_index_3986_, v_val_3987_);
lean_dec(v_rsize_3984_);
lean_dec(v_lsize_3983_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(lean_object* v_upperBound_3989_, lean_object* v_fst_3990_, lean_object* v___x_3991_, lean_object* v_fst_3992_, lean_object* v_inst_3993_, lean_object* v_R_3994_, lean_object* v_a_3995_, lean_object* v_b_3996_, lean_object* v_c_3997_){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3989_, v_fst_3990_, v___x_3991_, v_fst_3992_, v_a_3995_, v_b_3996_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___boxed(lean_object* v_upperBound_3999_, lean_object* v_fst_4000_, lean_object* v___x_4001_, lean_object* v_fst_4002_, lean_object* v_inst_4003_, lean_object* v_R_4004_, lean_object* v_a_4005_, lean_object* v_b_4006_, lean_object* v_c_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(v_upperBound_3999_, v_fst_4000_, v___x_4001_, v_fst_4002_, v_inst_4003_, v_R_4004_, v_a_4005_, v_b_4006_, v_c_4007_);
lean_dec_ref(v_fst_4002_);
lean_dec(v___x_4001_);
lean_dec_ref(v_fst_4000_);
lean_dec(v_upperBound_3999_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_4009_, lean_object* v_msg_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_4010_, v___y_4011_, v___y_4012_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_4015_, lean_object* v_msg_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_4015_, v_msg_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(lean_object* v_00_u03b2_4021_, lean_object* v_m_4022_, lean_object* v_a_4023_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_4022_, v_a_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___boxed(lean_object* v_00_u03b2_4025_, lean_object* v_m_4026_, lean_object* v_a_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(v_00_u03b2_4025_, v_m_4026_, v_a_4027_);
lean_dec_ref(v_a_4027_);
lean_dec_ref(v_m_4026_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26(lean_object* v_00_u03b2_4029_, lean_object* v_m_4030_, lean_object* v_a_4031_, lean_object* v_b_4032_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_m_4030_, v_a_4031_, v_b_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_4034_, lean_object* v_macroStack_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_4034_, v_macroStack_4035_, v___y_4037_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4040_, lean_object* v_macroStack_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4040_, v_macroStack_4041_, v___y_4042_, v___y_4043_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29(lean_object* v_inst_4046_, lean_object* v_R_4047_, lean_object* v_a_4048_, lean_object* v_b_4049_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v_a_4048_, v_b_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(lean_object* v_00_u03b2_4051_, lean_object* v_a_4052_, lean_object* v_x_4053_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_4052_, v_x_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___boxed(lean_object* v_00_u03b2_4055_, lean_object* v_a_4056_, lean_object* v_x_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(v_00_u03b2_4055_, v_a_4056_, v_x_4057_);
lean_dec(v_x_4057_);
lean_dec_ref(v_a_4056_);
return v_res_4058_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(lean_object* v_00_u03b2_4059_, lean_object* v_a_4060_, lean_object* v_x_4061_){
_start:
{
uint8_t v___x_4062_; 
v___x_4062_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_4060_, v_x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___boxed(lean_object* v_00_u03b2_4063_, lean_object* v_a_4064_, lean_object* v_x_4065_){
_start:
{
uint8_t v_res_4066_; lean_object* v_r_4067_; 
v_res_4066_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(v_00_u03b2_4063_, v_a_4064_, v_x_4065_);
lean_dec(v_x_4065_);
lean_dec_ref(v_a_4064_);
v_r_4067_ = lean_box(v_res_4066_);
return v_r_4067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38(lean_object* v_00_u03b2_4068_, lean_object* v_data_4069_){
_start:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_data_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39(lean_object* v_00_u03b2_4071_, lean_object* v_a_4072_, lean_object* v_b_4073_, lean_object* v_x_4074_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_4072_, v_b_4073_, v_x_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44(lean_object* v_00_u03b2_4076_, lean_object* v_i_4077_, lean_object* v_source_4078_, lean_object* v_target_4079_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v_i_4077_, v_source_4078_, v_target_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4081_, lean_object* v_x_4082_, lean_object* v_x_4083_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_x_4082_, v_x_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4093_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4094_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
v___x_4095_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4096_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4097_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4093_, v___x_4094_, v___x_4095_, v___x_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4126_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4127_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4128_ = l_Lean_addBuiltinDeclarationRanges(v___x_4126_, v___x_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4131_){
_start:
{
lean_object* v_doc_4133_; lean_object* v___x_4134_; 
v_doc_4133_ = lean_ctor_get(v___y_4131_, 1);
lean_inc_ref(v_doc_4133_);
v___x_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4134_, 0, v_doc_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4135_);
lean_dec_ref(v___y_4135_);
return v_res_4137_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4138_, lean_object* v_a_4139_, uint8_t v_b_4140_){
_start:
{
lean_object* v_str_4141_; lean_object* v_startInclusive_4142_; lean_object* v_endExclusive_4143_; lean_object* v___x_4144_; uint8_t v_decide_4145_; 
v_str_4141_ = lean_ctor_get(v_s_4138_, 0);
v_startInclusive_4142_ = lean_ctor_get(v_s_4138_, 1);
v_endExclusive_4143_ = lean_ctor_get(v_s_4138_, 2);
v___x_4144_ = lean_nat_sub(v_endExclusive_4143_, v_startInclusive_4142_);
v_decide_4145_ = lean_nat_dec_eq(v_a_4139_, v___x_4144_);
lean_dec(v___x_4144_);
if (v_decide_4145_ == 0)
{
lean_object* v___x_4146_; uint32_t v___x_4147_; uint32_t v___x_4148_; uint8_t v___x_4149_; 
v___x_4146_ = lean_nat_add(v_startInclusive_4142_, v_a_4139_);
lean_dec(v_a_4139_);
v___x_4147_ = lean_string_utf8_get_fast(v_str_4141_, v___x_4146_);
v___x_4148_ = 10;
v___x_4149_ = lean_uint32_dec_eq(v___x_4147_, v___x_4148_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4150_ = lean_string_utf8_next_fast(v_str_4141_, v___x_4146_);
lean_dec(v___x_4146_);
v___x_4151_ = lean_nat_sub(v___x_4150_, v_startInclusive_4142_);
v_a_4139_ = v___x_4151_;
v_b_4140_ = v___x_4149_;
goto _start;
}
else
{
lean_dec(v___x_4146_);
return v___x_4149_;
}
}
else
{
lean_dec(v_a_4139_);
return v_b_4140_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4153_, lean_object* v_a_4154_, lean_object* v_b_4155_){
_start:
{
uint8_t v_b_boxed_4156_; uint8_t v_res_4157_; lean_object* v_r_4158_; 
v_b_boxed_4156_ = lean_unbox(v_b_4155_);
v_res_4157_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4153_, v_a_4154_, v_b_boxed_4156_);
lean_dec_ref(v_s_4153_);
v_r_4158_ = lean_box(v_res_4157_);
return v_r_4158_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4159_){
_start:
{
lean_object* v_searcher_4160_; uint8_t v___x_4161_; uint8_t v___x_4162_; 
v_searcher_4160_ = lean_unsigned_to_nat(0u);
v___x_4161_ = 0;
v___x_4162_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4159_, v_searcher_4160_, v___x_4161_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4163_){
_start:
{
uint8_t v_res_4164_; lean_object* v_r_4165_; 
v_res_4164_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4163_);
lean_dec_ref(v_s_4163_);
v_r_4165_ = lean_box(v_res_4164_);
return v_r_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4177_, lean_object* v_fst_4178_, uint8_t v___x_4179_, lean_object* v_a_4180_, lean_object* v___x_4181_, lean_object* v___x_4182_, lean_object* v___x_4183_, lean_object* v___x_4184_, lean_object* v___x_4185_, lean_object* v___x_4186_, lean_object* v___x_4187_, lean_object* v___x_4188_, lean_object* v_snd_4189_, lean_object* v___x_4190_){
_start:
{
if (lean_obj_tag(v___x_4177_) == 1)
{
lean_object* v_val_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4253_; 
v_val_4192_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4194_ = v___x_4177_;
v_isShared_4195_ = v_isSharedCheck_4253_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_val_4192_);
lean_dec(v___x_4177_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4253_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4196_ = lean_unsigned_to_nat(0u);
v___x_4197_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4198_ = l_Lean_Syntax_setArg(v_fst_4178_, v___x_4196_, v___x_4197_);
v___x_4199_ = l_Lean_Syntax_getPos_x3f(v___x_4198_, v___x_4179_);
lean_dec(v___x_4198_);
if (lean_obj_tag(v___x_4199_) == 1)
{
lean_object* v_val_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4249_; 
lean_dec_ref(v___x_4190_);
v_val_4200_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4202_ = v___x_4199_;
v_isShared_4203_ = v_isSharedCheck_4249_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_val_4200_);
lean_dec(v___x_4199_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4249_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___y_4205_; lean_object* v___x_4231_; lean_object* v___x_4237_; uint8_t v___x_4238_; 
v___x_4231_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4189_);
v___x_4237_ = lean_string_utf8_byte_size(v___x_4231_);
v___x_4238_ = lean_nat_dec_eq(v___x_4237_, v___x_4196_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; 
v___x_4239_ = lean_string_length(v___x_4231_);
v___x_4240_ = lean_unsigned_to_nat(93u);
v___x_4241_ = lean_nat_dec_le(v___x_4239_, v___x_4240_);
if (v___x_4241_ == 0)
{
goto v___jp_4232_;
}
else
{
lean_object* v___x_4242_; uint8_t v___x_4243_; 
lean_inc_ref(v___x_4231_);
v___x_4242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4231_);
lean_ctor_set(v___x_4242_, 1, v___x_4196_);
lean_ctor_set(v___x_4242_, 2, v___x_4237_);
v___x_4243_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4242_);
lean_dec_ref_known(v___x_4242_, 3);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4244_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4245_ = lean_string_append(v___x_4244_, v___x_4231_);
lean_dec_ref(v___x_4231_);
v___x_4246_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4247_ = lean_string_append(v___x_4245_, v___x_4246_);
v___y_4205_ = v___x_4247_;
goto v___jp_4204_;
}
else
{
goto v___jp_4232_;
}
}
}
else
{
lean_object* v___x_4248_; 
lean_dec_ref(v___x_4231_);
v___x_4248_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_4205_ = v___x_4248_;
goto v___jp_4204_;
}
v___jp_4204_:
{
lean_object* v_toEditableDocumentCore_4206_; lean_object* v_meta_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4227_; 
v_toEditableDocumentCore_4206_ = lean_ctor_get(v_a_4180_, 0);
lean_inc_ref(v_toEditableDocumentCore_4206_);
v_meta_4207_ = lean_ctor_get(v_toEditableDocumentCore_4206_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v_toEditableDocumentCore_4206_);
if (v_isSharedCheck_4227_ == 0)
{
lean_object* v_unused_4228_; lean_object* v_unused_4229_; lean_object* v_unused_4230_; 
v_unused_4228_ = lean_ctor_get(v_toEditableDocumentCore_4206_, 3);
lean_dec(v_unused_4228_);
v_unused_4229_ = lean_ctor_get(v_toEditableDocumentCore_4206_, 2);
lean_dec(v_unused_4229_);
v_unused_4230_ = lean_ctor_get(v_toEditableDocumentCore_4206_, 1);
lean_dec(v_unused_4230_);
v___x_4209_ = v_toEditableDocumentCore_4206_;
v_isShared_4210_ = v_isSharedCheck_4227_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_meta_4207_);
lean_dec(v_toEditableDocumentCore_4206_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4227_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v_text_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4217_; 
v_text_4211_ = lean_ctor_get(v_meta_4207_, 3);
lean_inc_ref(v_text_4211_);
lean_dec_ref(v_meta_4207_);
v___x_4212_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4180_);
v___x_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4213_, 0, v_val_4192_);
lean_ctor_set(v___x_4213_, 1, v_val_4200_);
v___x_4214_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4211_, v___x_4213_);
v___x_4215_ = lean_box(0);
lean_inc(v___x_4181_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 3, v___x_4181_);
lean_ctor_set(v___x_4209_, 2, v___x_4215_);
lean_ctor_set(v___x_4209_, 1, v___y_4205_);
lean_ctor_set(v___x_4209_, 0, v___x_4214_);
v___x_4217_ = v___x_4209_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4226_, 1, v___y_4205_);
lean_ctor_set(v_reuseFailAlloc_4226_, 2, v___x_4215_);
lean_ctor_set(v_reuseFailAlloc_4226_, 3, v___x_4181_);
v___x_4217_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
lean_object* v___x_4218_; lean_object* v___x_4220_; 
v___x_4218_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4212_, v___x_4217_);
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 0, v___x_4218_);
v___x_4220_ = v___x_4202_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4218_);
v___x_4220_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
lean_object* v___x_4221_; lean_object* v___x_4223_; 
lean_inc(v___x_4181_);
v___x_4221_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4181_);
lean_ctor_set(v___x_4221_, 1, v___x_4181_);
lean_ctor_set(v___x_4221_, 2, v___x_4182_);
lean_ctor_set(v___x_4221_, 3, v___x_4183_);
lean_ctor_set(v___x_4221_, 4, v___x_4184_);
lean_ctor_set(v___x_4221_, 5, v___x_4185_);
lean_ctor_set(v___x_4221_, 6, v___x_4186_);
lean_ctor_set(v___x_4221_, 7, v___x_4220_);
lean_ctor_set(v___x_4221_, 8, v___x_4187_);
lean_ctor_set(v___x_4221_, 9, v___x_4188_);
if (v_isShared_4195_ == 0)
{
lean_ctor_set_tag(v___x_4194_, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4221_);
v___x_4223_ = v___x_4194_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4221_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
}
v___jp_4232_:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4233_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4234_ = lean_string_append(v___x_4233_, v___x_4231_);
lean_dec_ref(v___x_4231_);
v___x_4235_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4236_ = lean_string_append(v___x_4234_, v___x_4235_);
v___y_4205_ = v___x_4236_;
goto v___jp_4204_;
}
}
}
else
{
lean_object* v___x_4251_; 
lean_dec(v___x_4199_);
lean_dec(v_val_4192_);
lean_dec_ref(v_snd_4189_);
lean_dec(v___x_4188_);
lean_dec(v___x_4187_);
lean_dec(v___x_4186_);
lean_dec(v___x_4185_);
lean_dec(v___x_4184_);
lean_dec(v___x_4183_);
lean_dec_ref(v___x_4182_);
lean_dec(v___x_4181_);
lean_dec_ref(v_a_4180_);
if (v_isShared_4195_ == 0)
{
lean_ctor_set_tag(v___x_4194_, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4190_);
v___x_4251_ = v___x_4194_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4190_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
else
{
lean_object* v___x_4254_; 
lean_dec_ref(v_snd_4189_);
lean_dec(v___x_4188_);
lean_dec(v___x_4187_);
lean_dec(v___x_4186_);
lean_dec(v___x_4185_);
lean_dec(v___x_4184_);
lean_dec(v___x_4183_);
lean_dec_ref(v___x_4182_);
lean_dec(v___x_4181_);
lean_dec_ref(v_a_4180_);
lean_dec(v_fst_4178_);
lean_dec(v___x_4177_);
v___x_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4190_);
return v___x_4254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4255_, lean_object* v_fst_4256_, lean_object* v___x_4257_, lean_object* v_a_4258_, lean_object* v___x_4259_, lean_object* v___x_4260_, lean_object* v___x_4261_, lean_object* v___x_4262_, lean_object* v___x_4263_, lean_object* v___x_4264_, lean_object* v___x_4265_, lean_object* v___x_4266_, lean_object* v_snd_4267_, lean_object* v___x_4268_, lean_object* v___y_4269_){
_start:
{
uint8_t v___x_4482__boxed_4270_; lean_object* v_res_4271_; 
v___x_4482__boxed_4270_ = lean_unbox(v___x_4257_);
v_res_4271_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4255_, v_fst_4256_, v___x_4482__boxed_4270_, v_a_4258_, v___x_4259_, v___x_4260_, v___x_4261_, v___x_4262_, v___x_4263_, v___x_4264_, v___x_4265_, v___x_4266_, v_snd_4267_, v___x_4268_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4275_, size_t v_sz_4276_, size_t v_i_4277_, lean_object* v_b_4278_){
_start:
{
lean_object* v_a_4280_; uint8_t v___x_4284_; 
v___x_4284_ = lean_usize_dec_lt(v_i_4277_, v_sz_4276_);
if (v___x_4284_ == 0)
{
lean_inc_ref(v_b_4278_);
return v_b_4278_;
}
else
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v_a_4287_; 
v___x_4285_ = lean_box(0);
v___x_4286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4287_ = lean_array_uget(v_as_4275_, v_i_4277_);
if (lean_obj_tag(v_a_4287_) == 1)
{
lean_object* v_i_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4322_; 
v_i_4288_ = lean_ctor_get(v_a_4287_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v_a_4287_);
if (v_isSharedCheck_4322_ == 0)
{
lean_object* v_unused_4323_; 
v_unused_4323_ = lean_ctor_get(v_a_4287_, 1);
lean_dec(v_unused_4323_);
v___x_4290_ = v_a_4287_;
v_isShared_4291_ = v_isSharedCheck_4322_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_i_4288_);
lean_dec(v_a_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4322_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
if (lean_obj_tag(v_i_4288_) == 10)
{
lean_object* v_i_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4321_; 
v_i_4292_ = lean_ctor_get(v_i_4288_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v_i_4288_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4294_ = v_i_4288_;
v_isShared_4295_ = v_isSharedCheck_4321_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_i_4292_);
lean_dec(v_i_4288_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4321_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v_stx_4296_; lean_object* v_value_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4320_; 
v_stx_4296_ = lean_ctor_get(v_i_4292_, 0);
v_value_4297_ = lean_ctor_get(v_i_4292_, 1);
v_isSharedCheck_4320_ = !lean_is_exclusive(v_i_4292_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4299_ = v_i_4292_;
v_isShared_4300_ = v_isSharedCheck_4320_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_value_4297_);
lean_inc(v_stx_4296_);
lean_dec(v_i_4292_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4320_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4301_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4302_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4297_, v___x_4301_);
lean_dec(v_value_4297_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_del_object(v___x_4299_);
lean_dec(v_stx_4296_);
lean_del_object(v___x_4294_);
lean_del_object(v___x_4290_);
v_a_4280_ = v___x_4286_;
goto v___jp_4279_;
}
else
{
lean_object* v_val_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4319_; 
v_val_4303_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4305_ = v___x_4302_;
v_isShared_4306_ = v_isSharedCheck_4319_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_val_4303_);
lean_dec(v___x_4302_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4319_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 1, v_val_4303_);
v___x_4308_ = v___x_4299_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_stx_4296_);
lean_ctor_set(v_reuseFailAlloc_4318_, 1, v_val_4303_);
v___x_4308_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
lean_object* v___x_4310_; 
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v___x_4308_);
v___x_4310_ = v___x_4305_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4308_);
v___x_4310_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
lean_object* v___x_4312_; 
if (v_isShared_4295_ == 0)
{
lean_ctor_set_tag(v___x_4294_, 1);
lean_ctor_set(v___x_4294_, 0, v___x_4310_);
v___x_4312_ = v___x_4294_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4310_);
v___x_4312_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
lean_object* v___x_4314_; 
if (v_isShared_4291_ == 0)
{
lean_ctor_set_tag(v___x_4290_, 0);
lean_ctor_set(v___x_4290_, 1, v___x_4285_);
lean_ctor_set(v___x_4290_, 0, v___x_4312_);
v___x_4314_ = v___x_4290_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4312_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v___x_4285_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
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
lean_del_object(v___x_4290_);
lean_dec_ref(v_i_4288_);
v_a_4280_ = v___x_4286_;
goto v___jp_4279_;
}
}
}
else
{
lean_dec(v_a_4287_);
v_a_4280_ = v___x_4286_;
goto v___jp_4279_;
}
}
v___jp_4279_:
{
size_t v___x_4281_; size_t v___x_4282_; 
v___x_4281_ = ((size_t)1ULL);
v___x_4282_ = lean_usize_add(v_i_4277_, v___x_4281_);
v_i_4277_ = v___x_4282_;
v_b_4278_ = v_a_4280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4324_, lean_object* v_sz_4325_, lean_object* v_i_4326_, lean_object* v_b_4327_){
_start:
{
size_t v_sz_boxed_4328_; size_t v_i_boxed_4329_; lean_object* v_res_4330_; 
v_sz_boxed_4328_ = lean_unbox_usize(v_sz_4325_);
lean_dec(v_sz_4325_);
v_i_boxed_4329_ = lean_unbox_usize(v_i_4326_);
lean_dec(v_i_4326_);
v_res_4330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4324_, v_sz_boxed_4328_, v_i_boxed_4329_, v_b_4327_);
lean_dec_ref(v_b_4327_);
lean_dec_ref(v_as_4324_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4331_, size_t v_sz_4332_, size_t v_i_4333_, lean_object* v_b_4334_){
_start:
{
lean_object* v_a_4336_; uint8_t v___x_4340_; 
v___x_4340_ = lean_usize_dec_lt(v_i_4333_, v_sz_4332_);
if (v___x_4340_ == 0)
{
lean_inc_ref(v_b_4334_);
return v_b_4334_;
}
else
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v_a_4343_; 
v___x_4341_ = lean_box(0);
v___x_4342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4343_ = lean_array_uget(v_as_4331_, v_i_4333_);
if (lean_obj_tag(v_a_4343_) == 1)
{
lean_object* v_i_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4378_; 
v_i_4344_ = lean_ctor_get(v_a_4343_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v_a_4343_);
if (v_isSharedCheck_4378_ == 0)
{
lean_object* v_unused_4379_; 
v_unused_4379_ = lean_ctor_get(v_a_4343_, 1);
lean_dec(v_unused_4379_);
v___x_4346_ = v_a_4343_;
v_isShared_4347_ = v_isSharedCheck_4378_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_i_4344_);
lean_dec(v_a_4343_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4378_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
if (lean_obj_tag(v_i_4344_) == 10)
{
lean_object* v_i_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4377_; 
v_i_4348_ = lean_ctor_get(v_i_4344_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v_i_4344_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4350_ = v_i_4344_;
v_isShared_4351_ = v_isSharedCheck_4377_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_i_4348_);
lean_dec(v_i_4344_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4377_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v_stx_4352_; lean_object* v_value_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4376_; 
v_stx_4352_ = lean_ctor_get(v_i_4348_, 0);
v_value_4353_ = lean_ctor_get(v_i_4348_, 1);
v_isSharedCheck_4376_ = !lean_is_exclusive(v_i_4348_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4355_ = v_i_4348_;
v_isShared_4356_ = v_isSharedCheck_4376_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_value_4353_);
lean_inc(v_stx_4352_);
lean_dec(v_i_4348_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4376_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4357_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4358_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4353_, v___x_4357_);
lean_dec(v_value_4353_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_del_object(v___x_4355_);
lean_dec(v_stx_4352_);
lean_del_object(v___x_4350_);
lean_del_object(v___x_4346_);
v_a_4336_ = v___x_4342_;
goto v___jp_4335_;
}
else
{
lean_object* v_val_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4375_; 
v_val_4359_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4361_ = v___x_4358_;
v_isShared_4362_ = v_isSharedCheck_4375_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_val_4359_);
lean_dec(v___x_4358_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4375_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 1, v_val_4359_);
v___x_4364_ = v___x_4355_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_stx_4352_);
lean_ctor_set(v_reuseFailAlloc_4374_, 1, v_val_4359_);
v___x_4364_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
lean_object* v___x_4366_; 
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 0, v___x_4364_);
v___x_4366_ = v___x_4361_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4364_);
v___x_4366_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
lean_object* v___x_4368_; 
if (v_isShared_4351_ == 0)
{
lean_ctor_set_tag(v___x_4350_, 1);
lean_ctor_set(v___x_4350_, 0, v___x_4366_);
v___x_4368_ = v___x_4350_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4366_);
v___x_4368_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
lean_object* v___x_4370_; 
if (v_isShared_4347_ == 0)
{
lean_ctor_set_tag(v___x_4346_, 0);
lean_ctor_set(v___x_4346_, 1, v___x_4341_);
lean_ctor_set(v___x_4346_, 0, v___x_4368_);
v___x_4370_ = v___x_4346_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
lean_ctor_set(v_reuseFailAlloc_4371_, 1, v___x_4341_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
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
lean_del_object(v___x_4346_);
lean_dec_ref(v_i_4344_);
v_a_4336_ = v___x_4342_;
goto v___jp_4335_;
}
}
}
else
{
lean_dec(v_a_4343_);
v_a_4336_ = v___x_4342_;
goto v___jp_4335_;
}
}
v___jp_4335_:
{
size_t v___x_4337_; size_t v___x_4338_; lean_object* v___x_4339_; 
v___x_4337_ = ((size_t)1ULL);
v___x_4338_ = lean_usize_add(v_i_4333_, v___x_4337_);
v___x_4339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4331_, v_sz_4332_, v___x_4338_, v_a_4336_);
return v___x_4339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4380_, lean_object* v_sz_4381_, lean_object* v_i_4382_, lean_object* v_b_4383_){
_start:
{
size_t v_sz_boxed_4384_; size_t v_i_boxed_4385_; lean_object* v_res_4386_; 
v_sz_boxed_4384_ = lean_unbox_usize(v_sz_4381_);
lean_dec(v_sz_4381_);
v_i_boxed_4385_ = lean_unbox_usize(v_i_4382_);
lean_dec(v_i_4382_);
v_res_4386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4380_, v_sz_boxed_4384_, v_i_boxed_4385_, v_b_4383_);
lean_dec_ref(v_b_4383_);
lean_dec_ref(v_as_4380_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4387_){
_start:
{
if (lean_obj_tag(v_x_4387_) == 0)
{
lean_object* v_cs_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; size_t v_sz_4391_; size_t v___x_4392_; lean_object* v___x_4393_; lean_object* v_fst_4394_; 
v_cs_4388_ = lean_ctor_get(v_x_4387_, 0);
v___x_4389_ = lean_box(0);
v___x_4390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4391_ = lean_array_size(v_cs_4388_);
v___x_4392_ = ((size_t)0ULL);
v___x_4393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4388_, v_sz_4391_, v___x_4392_, v___x_4390_);
v_fst_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc(v_fst_4394_);
lean_dec_ref(v___x_4393_);
if (lean_obj_tag(v_fst_4394_) == 0)
{
return v___x_4389_;
}
else
{
lean_object* v_val_4395_; 
v_val_4395_ = lean_ctor_get(v_fst_4394_, 0);
lean_inc(v_val_4395_);
lean_dec_ref_known(v_fst_4394_, 1);
return v_val_4395_;
}
}
else
{
lean_object* v_vs_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; size_t v_sz_4399_; size_t v___x_4400_; lean_object* v___x_4401_; lean_object* v_fst_4402_; 
v_vs_4396_ = lean_ctor_get(v_x_4387_, 0);
v___x_4397_ = lean_box(0);
v___x_4398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4399_ = lean_array_size(v_vs_4396_);
v___x_4400_ = ((size_t)0ULL);
v___x_4401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4396_, v_sz_4399_, v___x_4400_, v___x_4398_);
v_fst_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_fst_4402_);
lean_dec_ref(v___x_4401_);
if (lean_obj_tag(v_fst_4402_) == 0)
{
return v___x_4397_;
}
else
{
lean_object* v_val_4403_; 
v_val_4403_ = lean_ctor_get(v_fst_4402_, 0);
lean_inc(v_val_4403_);
lean_dec_ref_known(v_fst_4402_, 1);
return v_val_4403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4404_, size_t v_sz_4405_, size_t v_i_4406_, lean_object* v_b_4407_){
_start:
{
uint8_t v___x_4408_; 
v___x_4408_ = lean_usize_dec_lt(v_i_4406_, v_sz_4405_);
if (v___x_4408_ == 0)
{
lean_inc_ref(v_b_4407_);
return v_b_4407_;
}
else
{
lean_object* v___x_4409_; lean_object* v_a_4410_; lean_object* v___x_4411_; 
v___x_4409_ = lean_box(0);
v_a_4410_ = lean_array_uget_borrowed(v_as_4404_, v_i_4406_);
v___x_4411_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4410_);
if (lean_obj_tag(v___x_4411_) == 1)
{
lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
v___x_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4412_);
lean_ctor_set(v___x_4413_, 1, v___x_4409_);
return v___x_4413_;
}
else
{
lean_object* v___x_4414_; size_t v___x_4415_; size_t v___x_4416_; 
lean_dec(v___x_4411_);
v___x_4414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4415_ = ((size_t)1ULL);
v___x_4416_ = lean_usize_add(v_i_4406_, v___x_4415_);
v_i_4406_ = v___x_4416_;
v_b_4407_ = v___x_4414_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4418_, lean_object* v_sz_4419_, lean_object* v_i_4420_, lean_object* v_b_4421_){
_start:
{
size_t v_sz_boxed_4422_; size_t v_i_boxed_4423_; lean_object* v_res_4424_; 
v_sz_boxed_4422_ = lean_unbox_usize(v_sz_4419_);
lean_dec(v_sz_4419_);
v_i_boxed_4423_ = lean_unbox_usize(v_i_4420_);
lean_dec(v_i_4420_);
v_res_4424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4418_, v_sz_boxed_4422_, v_i_boxed_4423_, v_b_4421_);
lean_dec_ref(v_b_4421_);
lean_dec_ref(v_as_4418_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4425_);
lean_dec_ref(v_x_4425_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4427_){
_start:
{
lean_object* v_root_4428_; lean_object* v_tail_4429_; lean_object* v___x_4430_; 
v_root_4428_ = lean_ctor_get(v_t_4427_, 0);
v_tail_4429_ = lean_ctor_get(v_t_4427_, 1);
v___x_4430_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4428_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v___x_4431_; size_t v_sz_4432_; size_t v___x_4433_; lean_object* v___x_4434_; lean_object* v_fst_4435_; 
v___x_4431_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4432_ = lean_array_size(v_tail_4429_);
v___x_4433_ = ((size_t)0ULL);
v___x_4434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4429_, v_sz_4432_, v___x_4433_, v___x_4431_);
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
return v___x_4430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4437_);
lean_dec_ref(v_t_4437_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4453_, lean_object* v_a_4454_){
_start:
{
if (lean_obj_tag(v_node_4453_) == 1)
{
lean_object* v_children_4456_; lean_object* v_res_4457_; 
v_children_4456_ = lean_ctor_get(v_node_4453_, 1);
v_res_4457_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4456_);
if (lean_obj_tag(v_res_4457_) == 1)
{
lean_object* v_val_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4495_; 
v_val_4458_ = lean_ctor_get(v_res_4457_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_res_4457_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4460_ = v_res_4457_;
v_isShared_4461_ = v_isSharedCheck_4495_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_val_4458_);
lean_dec(v_res_4457_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4495_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v_fst_4462_; lean_object* v_snd_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4494_; 
v_fst_4462_ = lean_ctor_get(v_val_4458_, 0);
v_snd_4463_ = lean_ctor_get(v_val_4458_, 1);
v_isSharedCheck_4494_ = !lean_is_exclusive(v_val_4458_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4465_ = v_val_4458_;
v_isShared_4466_ = v_isSharedCheck_4494_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_snd_4463_);
lean_inc(v_fst_4462_);
lean_dec(v_val_4458_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4494_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4467_; lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4493_; 
v___x_4467_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4454_);
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4470_ = v___x_4467_;
v_isShared_4471_ = v_isSharedCheck_4493_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4467_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4493_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; uint8_t v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___y_4480_; lean_object* v___x_4482_; 
v___x_4472_ = lean_box(0);
v___x_4473_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4474_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4475_ = 1;
v___x_4476_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4477_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4478_ = l_Lean_Syntax_getPos_x3f(v_fst_4462_, v___x_4475_);
v___x_4479_ = lean_box(v___x_4475_);
v___y_4480_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4480_, 0, v___x_4478_);
lean_closure_set(v___y_4480_, 1, v_fst_4462_);
lean_closure_set(v___y_4480_, 2, v___x_4479_);
lean_closure_set(v___y_4480_, 3, v_a_4468_);
lean_closure_set(v___y_4480_, 4, v___x_4472_);
lean_closure_set(v___y_4480_, 5, v___x_4473_);
lean_closure_set(v___y_4480_, 6, v___x_4474_);
lean_closure_set(v___y_4480_, 7, v___x_4472_);
lean_closure_set(v___y_4480_, 8, v___x_4476_);
lean_closure_set(v___y_4480_, 9, v___x_4472_);
lean_closure_set(v___y_4480_, 10, v___x_4472_);
lean_closure_set(v___y_4480_, 11, v___x_4472_);
lean_closure_set(v___y_4480_, 12, v_snd_4463_);
lean_closure_set(v___y_4480_, 13, v___x_4477_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v___y_4480_);
v___x_4482_ = v___x_4460_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___y_4480_);
v___x_4482_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
lean_object* v___x_4484_; 
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 1, v___x_4482_);
lean_ctor_set(v___x_4465_, 0, v___x_4477_);
v___x_4484_ = v___x_4465_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4477_);
lean_ctor_set(v_reuseFailAlloc_4491_, 1, v___x_4482_);
v___x_4484_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4485_ = lean_unsigned_to_nat(1u);
v___x_4486_ = lean_mk_empty_array_with_capacity(v___x_4485_);
v___x_4487_ = lean_array_push(v___x_4486_, v___x_4484_);
if (v_isShared_4471_ == 0)
{
lean_ctor_set(v___x_4470_, 0, v___x_4487_);
v___x_4489_ = v___x_4470_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4496_; lean_object* v___x_4497_; 
lean_dec(v_res_4457_);
v___x_4496_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4496_);
return v___x_4497_;
}
}
else
{
lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4498_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
return v___x_4499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4500_, v_a_4501_);
lean_dec_ref(v_a_4501_);
lean_dec_ref(v_node_4500_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4504_, lean_object* v_x_4505_, lean_object* v_x_4506_, lean_object* v_node_4507_, lean_object* v_a_4508_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4507_, v_a_4508_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4511_, lean_object* v_x_4512_, lean_object* v_x_4513_, lean_object* v_node_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4511_, v_x_4512_, v_x_4513_, v_node_4514_, v_a_4515_);
lean_dec_ref(v_a_4515_);
lean_dec_ref(v_node_4514_);
lean_dec_ref(v_x_4513_);
lean_dec_ref(v_x_4512_);
lean_dec_ref(v_x_4511_);
return v_res_4517_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4518_, lean_object* v_inst_4519_, lean_object* v_R_4520_, lean_object* v_a_4521_, uint8_t v_b_4522_, lean_object* v_c_4523_){
_start:
{
uint8_t v___x_4524_; 
v___x_4524_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4518_, v_a_4521_, v_b_4522_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4525_, lean_object* v_inst_4526_, lean_object* v_R_4527_, lean_object* v_a_4528_, lean_object* v_b_4529_, lean_object* v_c_4530_){
_start:
{
uint8_t v_b_boxed_4531_; uint8_t v_res_4532_; lean_object* v_r_4533_; 
v_b_boxed_4531_ = lean_unbox(v_b_4529_);
v_res_4532_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4525_, v_inst_4526_, v_R_4527_, v_a_4528_, v_b_boxed_4531_, v_c_4530_);
lean_dec_ref(v_s_4525_);
v_r_4533_ = lean_box(v_res_4532_);
return v_r_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_(){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4539_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_));
v___x_4540_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4541_ = l_Lean_CodeAction_insertBuiltin(v___x_4539_, v___x_4540_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354____boxed(lean_object* v_a_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_();
return v_res_4543_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4549_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4550_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4549_);
return v___x_4550_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4551_ = lean_unsigned_to_nat(0u);
v___x_4552_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
v___x_4553_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4554_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4553_);
lean_ctor_set(v___x_4554_, 1, v___x_4552_);
lean_ctor_set(v___x_4554_, 2, v___x_4551_);
lean_ctor_set(v___x_4554_, 3, v___x_4551_);
return v___x_4554_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4555_){
_start:
{
lean_object* v___x_4556_; uint8_t v___x_4557_; uint8_t v___x_4558_; 
v___x_4556_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4557_ = 0;
v___x_4558_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4555_, v___x_4556_, v___x_4557_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4559_){
_start:
{
uint8_t v_res_4560_; lean_object* v_r_4561_; 
v_res_4560_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4559_);
lean_dec_ref(v_s_4559_);
v_r_4561_ = lean_box(v_res_4560_);
return v_r_4561_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4562_, lean_object* v_as_x27_4563_, uint8_t v_b_4564_){
_start:
{
if (lean_obj_tag(v_as_x27_4563_) == 0)
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4566_ = lean_box(v_b_4564_);
v___x_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4566_);
return v___x_4567_;
}
else
{
lean_object* v_head_4568_; uint8_t v_isSilent_4569_; 
v_head_4568_ = lean_ctor_get(v_as_x27_4563_, 0);
v_isSilent_4569_ = lean_ctor_get_uint8(v_head_4568_, sizeof(void*)*5 + 2);
if (v_isSilent_4569_ == 0)
{
lean_object* v_tail_4570_; lean_object* v_data_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; uint8_t v___x_4576_; 
v_tail_4570_ = lean_ctor_get(v_as_x27_4563_, 1);
v_data_4571_ = lean_ctor_get(v_head_4568_, 4);
lean_inc(v_data_4571_);
v___x_4572_ = l_Lean_MessageData_toString(v_data_4571_);
v___x_4573_ = lean_unsigned_to_nat(0u);
v___x_4574_ = lean_string_utf8_byte_size(v___x_4572_);
v___x_4575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4572_);
lean_ctor_set(v___x_4575_, 1, v___x_4573_);
lean_ctor_set(v___x_4575_, 2, v___x_4574_);
v___x_4576_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4575_);
lean_dec_ref_known(v___x_4575_, 3);
if (v___x_4576_ == 0)
{
v_as_x27_4563_ = v_tail_4570_;
goto _start;
}
else
{
lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4578_ = lean_box(v_foundPanic_4562_);
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
return v___x_4579_;
}
}
else
{
lean_object* v_tail_4580_; 
v_tail_4580_ = lean_ctor_get(v_as_x27_4563_, 1);
v_as_x27_4563_ = v_tail_4580_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4582_, lean_object* v_as_x27_4583_, lean_object* v_b_4584_, lean_object* v___y_4585_){
_start:
{
uint8_t v_foundPanic_boxed_4586_; uint8_t v_b_boxed_4587_; lean_object* v_res_4588_; 
v_foundPanic_boxed_4586_ = lean_unbox(v_foundPanic_4582_);
v_b_boxed_4587_ = lean_unbox(v_b_4584_);
v_res_4588_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4586_, v_as_x27_4583_, v_b_boxed_4587_);
lean_dec(v_as_x27_4583_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4589_, uint8_t v_severity_4590_, uint8_t v_isSilent_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v___x_4595_; 
v___x_4595_ = l_Lean_Elab_Command_getRef___redArg(v___y_4592_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v_a_4596_; lean_object* v___x_4597_; 
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
lean_inc(v_a_4596_);
lean_dec_ref_known(v___x_4595_, 1);
v___x_4597_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4596_, v_msgData_4589_, v_severity_4590_, v_isSilent_4591_, v___y_4592_, v___y_4593_);
lean_dec(v_a_4596_);
return v___x_4597_;
}
else
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4605_; 
lean_dec_ref(v_msgData_4589_);
v_a_4598_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4600_ = v___x_4595_;
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4595_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4603_; 
if (v_isShared_4601_ == 0)
{
v___x_4603_ = v___x_4600_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_a_4598_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4606_, lean_object* v_severity_4607_, lean_object* v_isSilent_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
uint8_t v_severity_boxed_4612_; uint8_t v_isSilent_boxed_4613_; lean_object* v_res_4614_; 
v_severity_boxed_4612_ = lean_unbox(v_severity_4607_);
v_isSilent_boxed_4613_ = lean_unbox(v_isSilent_4608_);
v_res_4614_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4606_, v_severity_boxed_4612_, v_isSilent_boxed_4613_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
uint8_t v___x_4619_; uint8_t v___x_4620_; lean_object* v___x_4621_; 
v___x_4619_ = 2;
v___x_4620_ = 0;
v___x_4621_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4615_, v___x_4619_, v___x_4620_, v___y_4616_, v___y_4617_);
return v___x_4621_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4622_, v___y_4623_, v___y_4624_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
return v_res_4626_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4634_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4635_ = l_Lean_MessageData_ofFormat(v___x_4634_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v___x_4640_; uint8_t v_foundPanic_4641_; 
v___x_4640_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4636_);
v_foundPanic_4641_ = l_Lean_Syntax_isOfKind(v_x_4636_, v___x_4640_);
if (v_foundPanic_4641_ == 0)
{
lean_object* v___x_4642_; 
lean_dec(v_x_4636_);
v___x_4642_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4642_;
}
else
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4643_ = lean_unsigned_to_nat(2u);
v___x_4644_ = l_Lean_Syntax_getArg(v_x_4636_, v___x_4643_);
lean_dec(v_x_4636_);
v___x_4645_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4644_, v_a_4637_, v_a_4638_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; uint8_t v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4706_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref_known(v___x_4645_, 1);
v___x_4647_ = 0;
v___x_4648_ = l_Lean_MessageLog_toList(v_a_4646_);
v___x_4649_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4641_, v___x_4648_, v___x_4647_);
lean_dec(v___x_4648_);
v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4652_ = v___x_4649_;
v_isShared_4653_ = v_isSharedCheck_4706_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4649_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4706_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
uint8_t v___x_4654_; 
v___x_4654_ = lean_unbox(v_a_4650_);
lean_dec(v_a_4650_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; lean_object* v_env_4656_; lean_object* v_scopes_4657_; lean_object* v_usedQuotCtxts_4658_; lean_object* v_nextMacroScope_4659_; lean_object* v_maxRecDepth_4660_; lean_object* v_ngen_4661_; lean_object* v_auxDeclNGen_4662_; lean_object* v_infoState_4663_; lean_object* v_traceState_4664_; lean_object* v_snapshotTasks_4665_; lean_object* v_prevLinterStates_4666_; lean_object* v_codeQualityEntryTasks_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4677_; 
lean_del_object(v___x_4652_);
v___x_4655_ = lean_st_ref_take(v_a_4638_);
v_env_4656_ = lean_ctor_get(v___x_4655_, 0);
v_scopes_4657_ = lean_ctor_get(v___x_4655_, 2);
v_usedQuotCtxts_4658_ = lean_ctor_get(v___x_4655_, 3);
v_nextMacroScope_4659_ = lean_ctor_get(v___x_4655_, 4);
v_maxRecDepth_4660_ = lean_ctor_get(v___x_4655_, 5);
v_ngen_4661_ = lean_ctor_get(v___x_4655_, 6);
v_auxDeclNGen_4662_ = lean_ctor_get(v___x_4655_, 7);
v_infoState_4663_ = lean_ctor_get(v___x_4655_, 8);
v_traceState_4664_ = lean_ctor_get(v___x_4655_, 9);
v_snapshotTasks_4665_ = lean_ctor_get(v___x_4655_, 10);
v_prevLinterStates_4666_ = lean_ctor_get(v___x_4655_, 11);
v_codeQualityEntryTasks_4667_ = lean_ctor_get(v___x_4655_, 12);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4677_ == 0)
{
lean_object* v_unused_4678_; 
v_unused_4678_ = lean_ctor_get(v___x_4655_, 1);
lean_dec(v_unused_4678_);
v___x_4669_ = v___x_4655_;
v_isShared_4670_ = v_isSharedCheck_4677_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4667_);
lean_inc(v_prevLinterStates_4666_);
lean_inc(v_snapshotTasks_4665_);
lean_inc(v_traceState_4664_);
lean_inc(v_infoState_4663_);
lean_inc(v_auxDeclNGen_4662_);
lean_inc(v_ngen_4661_);
lean_inc(v_maxRecDepth_4660_);
lean_inc(v_nextMacroScope_4659_);
lean_inc(v_usedQuotCtxts_4658_);
lean_inc(v_scopes_4657_);
lean_inc(v_env_4656_);
lean_dec(v___x_4655_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4677_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___x_4672_; 
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 1, v_a_4646_);
v___x_4672_ = v___x_4669_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_env_4656_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_a_4646_);
lean_ctor_set(v_reuseFailAlloc_4676_, 2, v_scopes_4657_);
lean_ctor_set(v_reuseFailAlloc_4676_, 3, v_usedQuotCtxts_4658_);
lean_ctor_set(v_reuseFailAlloc_4676_, 4, v_nextMacroScope_4659_);
lean_ctor_set(v_reuseFailAlloc_4676_, 5, v_maxRecDepth_4660_);
lean_ctor_set(v_reuseFailAlloc_4676_, 6, v_ngen_4661_);
lean_ctor_set(v_reuseFailAlloc_4676_, 7, v_auxDeclNGen_4662_);
lean_ctor_set(v_reuseFailAlloc_4676_, 8, v_infoState_4663_);
lean_ctor_set(v_reuseFailAlloc_4676_, 9, v_traceState_4664_);
lean_ctor_set(v_reuseFailAlloc_4676_, 10, v_snapshotTasks_4665_);
lean_ctor_set(v_reuseFailAlloc_4676_, 11, v_prevLinterStates_4666_);
lean_ctor_set(v_reuseFailAlloc_4676_, 12, v_codeQualityEntryTasks_4667_);
v___x_4672_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4673_ = lean_st_ref_put(v_a_4638_, v___x_4672_);
v___x_4674_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4675_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4674_, v_a_4637_, v_a_4638_);
return v___x_4675_;
}
}
}
else
{
lean_object* v___x_4679_; lean_object* v_env_4680_; lean_object* v_scopes_4681_; lean_object* v_usedQuotCtxts_4682_; lean_object* v_nextMacroScope_4683_; lean_object* v_maxRecDepth_4684_; lean_object* v_ngen_4685_; lean_object* v_auxDeclNGen_4686_; lean_object* v_infoState_4687_; lean_object* v_traceState_4688_; lean_object* v_snapshotTasks_4689_; lean_object* v_prevLinterStates_4690_; lean_object* v_codeQualityEntryTasks_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4704_; 
lean_dec(v_a_4646_);
v___x_4679_ = lean_st_ref_take(v_a_4638_);
v_env_4680_ = lean_ctor_get(v___x_4679_, 0);
v_scopes_4681_ = lean_ctor_get(v___x_4679_, 2);
v_usedQuotCtxts_4682_ = lean_ctor_get(v___x_4679_, 3);
v_nextMacroScope_4683_ = lean_ctor_get(v___x_4679_, 4);
v_maxRecDepth_4684_ = lean_ctor_get(v___x_4679_, 5);
v_ngen_4685_ = lean_ctor_get(v___x_4679_, 6);
v_auxDeclNGen_4686_ = lean_ctor_get(v___x_4679_, 7);
v_infoState_4687_ = lean_ctor_get(v___x_4679_, 8);
v_traceState_4688_ = lean_ctor_get(v___x_4679_, 9);
v_snapshotTasks_4689_ = lean_ctor_get(v___x_4679_, 10);
v_prevLinterStates_4690_ = lean_ctor_get(v___x_4679_, 11);
v_codeQualityEntryTasks_4691_ = lean_ctor_get(v___x_4679_, 12);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4704_ == 0)
{
lean_object* v_unused_4705_; 
v_unused_4705_ = lean_ctor_get(v___x_4679_, 1);
lean_dec(v_unused_4705_);
v___x_4693_ = v___x_4679_;
v_isShared_4694_ = v_isSharedCheck_4704_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4691_);
lean_inc(v_prevLinterStates_4690_);
lean_inc(v_snapshotTasks_4689_);
lean_inc(v_traceState_4688_);
lean_inc(v_infoState_4687_);
lean_inc(v_auxDeclNGen_4686_);
lean_inc(v_ngen_4685_);
lean_inc(v_maxRecDepth_4684_);
lean_inc(v_nextMacroScope_4683_);
lean_inc(v_usedQuotCtxts_4682_);
lean_inc(v_scopes_4681_);
lean_inc(v_env_4680_);
lean_dec(v___x_4679_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4704_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4698_; 
v___x_4695_ = lean_box(0);
v___x_4696_ = l_Lean_MessageLog_empty;
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 1, v___x_4696_);
v___x_4698_ = v___x_4693_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_env_4680_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v___x_4696_);
lean_ctor_set(v_reuseFailAlloc_4703_, 2, v_scopes_4681_);
lean_ctor_set(v_reuseFailAlloc_4703_, 3, v_usedQuotCtxts_4682_);
lean_ctor_set(v_reuseFailAlloc_4703_, 4, v_nextMacroScope_4683_);
lean_ctor_set(v_reuseFailAlloc_4703_, 5, v_maxRecDepth_4684_);
lean_ctor_set(v_reuseFailAlloc_4703_, 6, v_ngen_4685_);
lean_ctor_set(v_reuseFailAlloc_4703_, 7, v_auxDeclNGen_4686_);
lean_ctor_set(v_reuseFailAlloc_4703_, 8, v_infoState_4687_);
lean_ctor_set(v_reuseFailAlloc_4703_, 9, v_traceState_4688_);
lean_ctor_set(v_reuseFailAlloc_4703_, 10, v_snapshotTasks_4689_);
lean_ctor_set(v_reuseFailAlloc_4703_, 11, v_prevLinterStates_4690_);
lean_ctor_set(v_reuseFailAlloc_4703_, 12, v_codeQualityEntryTasks_4691_);
v___x_4698_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
lean_object* v___x_4699_; lean_object* v___x_4701_; 
v___x_4699_ = lean_st_ref_put(v_a_4638_, v___x_4698_);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 0, v___x_4695_);
v___x_4701_ = v___x_4652_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v___x_4695_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
}
}
}
}
else
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4714_; 
v_a_4707_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4714_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4709_ = v___x_4645_;
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v___x_4645_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4712_; 
if (v_isShared_4710_ == 0)
{
v___x_4712_ = v___x_4709_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4707_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_){
_start:
{
lean_object* v_res_4719_; 
v_res_4719_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4715_, v_a_4716_, v_a_4717_);
lean_dec(v_a_4717_);
lean_dec_ref(v_a_4716_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4720_, lean_object* v_as_4721_, lean_object* v_as_x27_4722_, uint8_t v_b_4723_, lean_object* v_a_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v___x_4728_; 
v___x_4728_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4720_, v_as_x27_4722_, v_b_4723_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4729_, lean_object* v_as_4730_, lean_object* v_as_x27_4731_, lean_object* v_b_4732_, lean_object* v_a_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_){
_start:
{
uint8_t v_foundPanic_boxed_4737_; uint8_t v_b_boxed_4738_; lean_object* v_res_4739_; 
v_foundPanic_boxed_4737_ = lean_unbox(v_foundPanic_4729_);
v_b_boxed_4738_ = lean_unbox(v_b_4732_);
v_res_4739_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4737_, v_as_4730_, v_as_x27_4731_, v_b_boxed_4738_, v_a_4733_, v___y_4734_, v___y_4735_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec(v_as_x27_4731_);
lean_dec(v_as_4730_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4748_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4749_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4750_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4751_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4752_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4748_, v___x_4749_, v___x_4750_, v___x_4751_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4754_;
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
