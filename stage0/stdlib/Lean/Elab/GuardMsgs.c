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
lean_object* v_fileName_1702_; lean_object* v_fileMap_1703_; lean_object* v_currRecDepth_1704_; lean_object* v_cmdPos_1705_; lean_object* v_macroStack_1706_; lean_object* v_quotContext_x3f_1707_; lean_object* v_currMacroScope_1708_; lean_object* v_ref_1709_; lean_object* v_cancelTk_x3f_1710_; uint8_t v_suppressElabErrors_1711_; uint8_t v_checkDeprecated_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
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
v_checkDeprecated_1712_ = lean_ctor_get_uint8(v_a_1699_, sizeof(void*)*10 + 1);
v___x_1713_ = lean_box(0);
lean_inc(v_cancelTk_x3f_1710_);
lean_inc(v_ref_1709_);
lean_inc(v_currMacroScope_1708_);
lean_inc(v_quotContext_x3f_1707_);
lean_inc(v_macroStack_1706_);
lean_inc(v_cmdPos_1705_);
lean_inc(v_currRecDepth_1704_);
lean_inc_ref(v_fileMap_1703_);
lean_inc_ref(v_fileName_1702_);
v___x_1714_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1714_, 0, v_fileName_1702_);
lean_ctor_set(v___x_1714_, 1, v_fileMap_1703_);
lean_ctor_set(v___x_1714_, 2, v_currRecDepth_1704_);
lean_ctor_set(v___x_1714_, 3, v_cmdPos_1705_);
lean_ctor_set(v___x_1714_, 4, v_macroStack_1706_);
lean_ctor_set(v___x_1714_, 5, v_quotContext_x3f_1707_);
lean_ctor_set(v___x_1714_, 6, v_currMacroScope_1708_);
lean_ctor_set(v___x_1714_, 7, v_ref_1709_);
lean_ctor_set(v___x_1714_, 8, v___x_1713_);
lean_ctor_set(v___x_1714_, 9, v_cancelTk_x3f_1710_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*10, v_suppressElabErrors_1711_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*10 + 1, v_checkDeprecated_1712_);
v___x_1715_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_1698_, v___x_1714_, v_a_1700_);
lean_dec_ref_known(v___x_1714_, 10);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1759_; 
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v___x_1715_, 0);
lean_dec(v_unused_1760_);
v___x_1717_ = v___x_1715_;
v_isShared_1718_ = v_isSharedCheck_1759_;
goto v_resetjp_1716_;
}
else
{
lean_dec(v___x_1715_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1759_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v_messages_1721_; lean_object* v___y_1723_; lean_object* v_snapshotTasks_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1719_ = lean_st_ref_get(v_a_1700_);
v___x_1720_ = lean_st_ref_get(v_a_1700_);
v_messages_1721_ = lean_ctor_get(v___x_1719_, 1);
lean_inc_ref(v_messages_1721_);
lean_dec(v___x_1719_);
v_snapshotTasks_1751_ = lean_ctor_get(v___x_1720_, 10);
lean_inc_ref(v_snapshotTasks_1751_);
lean_dec(v___x_1720_);
v___x_1752_ = l_Lean_MessageLog_empty;
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = lean_array_get_size(v_snapshotTasks_1751_);
v___x_1755_ = lean_nat_dec_lt(v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_dec_ref(v_snapshotTasks_1751_);
v___y_1723_ = v___x_1752_;
goto v___jp_1722_;
}
else
{
size_t v___x_1756_; size_t v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = ((size_t)0ULL);
v___x_1757_ = lean_usize_of_nat(v___x_1754_);
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages_spec__1(v_snapshotTasks_1751_, v___x_1756_, v___x_1757_, v___x_1752_);
lean_dec_ref(v_snapshotTasks_1751_);
v___y_1723_ = v___x_1758_;
goto v___jp_1722_;
}
v___jp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v_env_1726_; lean_object* v_messages_1727_; lean_object* v_scopes_1728_; lean_object* v_usedQuotCtxts_1729_; lean_object* v_nextMacroScope_1730_; lean_object* v_maxRecDepth_1731_; lean_object* v_ngen_1732_; lean_object* v_auxDeclNGen_1733_; lean_object* v_infoState_1734_; lean_object* v_traceState_1735_; lean_object* v_prevLinterStates_1736_; lean_object* v_codeQualityEntryTasks_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1749_; 
v___x_1724_ = l_Lean_MessageLog_append(v_messages_1721_, v___y_1723_);
v___x_1725_ = lean_st_ref_take(v_a_1700_);
v_env_1726_ = lean_ctor_get(v___x_1725_, 0);
v_messages_1727_ = lean_ctor_get(v___x_1725_, 1);
v_scopes_1728_ = lean_ctor_get(v___x_1725_, 2);
v_usedQuotCtxts_1729_ = lean_ctor_get(v___x_1725_, 3);
v_nextMacroScope_1730_ = lean_ctor_get(v___x_1725_, 4);
v_maxRecDepth_1731_ = lean_ctor_get(v___x_1725_, 5);
v_ngen_1732_ = lean_ctor_get(v___x_1725_, 6);
v_auxDeclNGen_1733_ = lean_ctor_get(v___x_1725_, 7);
v_infoState_1734_ = lean_ctor_get(v___x_1725_, 8);
v_traceState_1735_ = lean_ctor_get(v___x_1725_, 9);
v_prevLinterStates_1736_ = lean_ctor_get(v___x_1725_, 11);
v_codeQualityEntryTasks_1737_ = lean_ctor_get(v___x_1725_, 12);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v___x_1725_, 10);
lean_dec(v_unused_1750_);
v___x_1739_ = v___x_1725_;
v_isShared_1740_ = v_isSharedCheck_1749_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1737_);
lean_inc(v_prevLinterStates_1736_);
lean_inc(v_traceState_1735_);
lean_inc(v_infoState_1734_);
lean_inc(v_auxDeclNGen_1733_);
lean_inc(v_ngen_1732_);
lean_inc(v_maxRecDepth_1731_);
lean_inc(v_nextMacroScope_1730_);
lean_inc(v_usedQuotCtxts_1729_);
lean_inc(v_scopes_1728_);
lean_inc(v_messages_1727_);
lean_inc(v_env_1726_);
lean_dec(v___x_1725_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1749_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1741_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___closed__0));
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 10, v___x_1741_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_env_1726_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_messages_1727_);
lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_scopes_1728_);
lean_ctor_set(v_reuseFailAlloc_1748_, 3, v_usedQuotCtxts_1729_);
lean_ctor_set(v_reuseFailAlloc_1748_, 4, v_nextMacroScope_1730_);
lean_ctor_set(v_reuseFailAlloc_1748_, 5, v_maxRecDepth_1731_);
lean_ctor_set(v_reuseFailAlloc_1748_, 6, v_ngen_1732_);
lean_ctor_set(v_reuseFailAlloc_1748_, 7, v_auxDeclNGen_1733_);
lean_ctor_set(v_reuseFailAlloc_1748_, 8, v_infoState_1734_);
lean_ctor_set(v_reuseFailAlloc_1748_, 9, v_traceState_1735_);
lean_ctor_set(v_reuseFailAlloc_1748_, 10, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1748_, 11, v_prevLinterStates_1736_);
lean_ctor_set(v_reuseFailAlloc_1748_, 12, v_codeQualityEntryTasks_1737_);
v___x_1743_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1744_ = lean_st_ref_put(v_a_1700_, v___x_1743_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1724_);
v___x_1746_ = v___x_1717_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1724_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1715_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1715_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages___boxed(lean_object* v_cmd_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v_cmd_1769_, v_a_1770_, v_a_1771_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
return v_res_1773_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(lean_object* v_opts_1774_, lean_object* v_opt_1775_){
_start:
{
lean_object* v_name_1776_; lean_object* v_defValue_1777_; lean_object* v_map_1778_; lean_object* v___x_1779_; 
v_name_1776_ = lean_ctor_get(v_opt_1775_, 0);
v_defValue_1777_ = lean_ctor_get(v_opt_1775_, 1);
v_map_1778_ = lean_ctor_get(v_opts_1774_, 0);
v___x_1779_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1778_, v_name_1776_);
if (lean_obj_tag(v___x_1779_) == 0)
{
uint8_t v___x_1780_; 
v___x_1780_ = lean_unbox(v_defValue_1777_);
return v___x_1780_;
}
else
{
lean_object* v_val_1781_; 
v_val_1781_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_val_1781_);
lean_dec_ref_known(v___x_1779_, 1);
if (lean_obj_tag(v_val_1781_) == 1)
{
uint8_t v_v_1782_; 
v_v_1782_ = lean_ctor_get_uint8(v_val_1781_, 0);
lean_dec_ref_known(v_val_1781_, 0);
return v_v_1782_;
}
else
{
uint8_t v___x_1783_; 
lean_dec(v_val_1781_);
v___x_1783_ = lean_unbox(v_defValue_1777_);
return v___x_1783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4___boxed(lean_object* v_opts_1784_, lean_object* v_opt_1785_){
_start:
{
uint8_t v_res_1786_; lean_object* v_r_1787_; 
v_res_1786_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1784_, v_opt_1785_);
lean_dec_ref(v_opt_1785_);
lean_dec_ref(v_opts_1784_);
v_r_1787_ = lean_box(v_res_1786_);
return v_r_1787_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg(){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___closed__0));
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg___boxed(lean_object* v___dummy_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v_res_1793_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___redArg();
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(lean_object* v_s_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___boxed(lean_object* v_s_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5(v_s_1797_);
lean_dec_ref(v_s_1797_);
return v_res_1798_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_box(1);
v___x_1800_ = l_Lean_MessageData_ofFormat(v___x_1799_);
return v___x_1800_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__2));
v___x_1805_ = l_Lean_MessageData_ofFormat(v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(lean_object* v_x_1806_, lean_object* v_x_1807_){
_start:
{
if (lean_obj_tag(v_x_1807_) == 0)
{
return v_x_1806_;
}
else
{
lean_object* v_head_1808_; lean_object* v_tail_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1831_; 
v_head_1808_ = lean_ctor_get(v_x_1807_, 0);
v_tail_1809_ = lean_ctor_get(v_x_1807_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_x_1807_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1811_ = v_x_1807_;
v_isShared_1812_ = v_isSharedCheck_1831_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_tail_1809_);
lean_inc(v_head_1808_);
lean_dec(v_x_1807_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1831_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_before_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1829_; 
v_before_1813_ = lean_ctor_get(v_head_1808_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_head_1808_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v_head_1808_, 1);
lean_dec(v_unused_1830_);
v___x_1815_ = v_head_1808_;
v_isShared_1816_ = v_isSharedCheck_1829_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_before_1813_);
lean_dec(v_head_1808_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1829_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1816_ == 0)
{
lean_ctor_set_tag(v___x_1815_, 7);
lean_ctor_set(v___x_1815_, 1, v___x_1817_);
lean_ctor_set(v___x_1815_, 0, v_x_1806_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_x_1806_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__3);
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 7);
lean_ctor_set(v___x_1811_, 1, v___x_1820_);
lean_ctor_set(v___x_1811_, 0, v___x_1819_);
v___x_1822_ = v___x_1811_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = l_Lean_MessageData_ofSyntax(v_before_1813_);
v___x_1824_ = l_Lean_indentD(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1822_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v_x_1806_ = v___x_1825_;
v_x_1807_ = v_tail_1809_;
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
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__1));
v___x_1836_ = l_Lean_MessageData_ofFormat(v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(lean_object* v_msgData_1837_, lean_object* v_macroStack_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v_scopes_1843_; lean_object* v___x_1844_; lean_object* v_opts_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1841_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1842_ = lean_st_ref_get(v___y_1839_);
v_scopes_1843_ = lean_ctor_get(v___x_1842_, 2);
lean_inc(v_scopes_1843_);
lean_dec(v___x_1842_);
v___x_1844_ = l_List_head_x21___redArg(v___x_1841_, v_scopes_1843_);
lean_dec(v_scopes_1843_);
v_opts_1845_ = lean_ctor_get(v___x_1844_, 1);
lean_inc_ref(v_opts_1845_);
lean_dec(v___x_1844_);
v___x_1846_ = l_Lean_Elab_pp_macroStack;
v___x_1847_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_1845_, v___x_1846_);
lean_dec_ref(v_opts_1845_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; 
lean_dec(v_macroStack_1838_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v_msgData_1837_);
return v___x_1848_;
}
else
{
if (lean_obj_tag(v_macroStack_1838_) == 0)
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v_msgData_1837_);
return v___x_1849_;
}
else
{
lean_object* v_head_1850_; lean_object* v_after_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1866_; 
v_head_1850_ = lean_ctor_get(v_macroStack_1838_, 0);
lean_inc(v_head_1850_);
v_after_1851_ = lean_ctor_get(v_head_1850_, 1);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_head_1850_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; 
v_unused_1867_ = lean_ctor_get(v_head_1850_, 0);
lean_dec(v_unused_1867_);
v___x_1853_ = v_head_1850_;
v_isShared_1854_ = v_isSharedCheck_1866_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_after_1851_);
lean_dec(v_head_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1866_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46___closed__0);
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 7);
lean_ctor_set(v___x_1853_, 1, v___x_1855_);
lean_ctor_set(v___x_1853_, 0, v_msgData_1837_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_msgData_1837_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v_msgData_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1858_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___closed__2);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = l_Lean_MessageData_ofSyntax(v_after_1851_);
v___x_1861_ = l_Lean_indentD(v___x_1860_);
v_msgData_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1862_, 0, v___x_1859_);
lean_ctor_set(v_msgData_1862_, 1, v___x_1861_);
v___x_1863_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40_spec__46(v_msgData_1862_, v_macroStack_1838_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg___boxed(lean_object* v_msgData_1868_, lean_object* v_macroStack_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_1868_, v_macroStack_1869_, v___y_1870_);
lean_dec(v___y_1870_);
return v_res_1872_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__0);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_alloc_ctor(0, 11, 0);
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
lean_object* v_a_1952_; lean_object* v_fileName_1953_; lean_object* v_fileMap_1954_; lean_object* v_currRecDepth_1955_; lean_object* v_cmdPos_1956_; lean_object* v_macroStack_1957_; lean_object* v_quotContext_x3f_1958_; lean_object* v_currMacroScope_1959_; lean_object* v_snap_x3f_1960_; lean_object* v_cancelTk_x3f_1961_; uint8_t v_suppressElabErrors_1962_; uint8_t v_checkDeprecated_1963_; lean_object* v_ref_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
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
v_checkDeprecated_1963_ = lean_ctor_get_uint8(v___y_1948_, sizeof(void*)*10 + 1);
v_ref_1964_ = l_Lean_replaceRef(v_ref_1946_, v_a_1952_);
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
v___x_1965_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1965_, 0, v_fileName_1953_);
lean_ctor_set(v___x_1965_, 1, v_fileMap_1954_);
lean_ctor_set(v___x_1965_, 2, v_currRecDepth_1955_);
lean_ctor_set(v___x_1965_, 3, v_cmdPos_1956_);
lean_ctor_set(v___x_1965_, 4, v_macroStack_1957_);
lean_ctor_set(v___x_1965_, 5, v_quotContext_x3f_1958_);
lean_ctor_set(v___x_1965_, 6, v_currMacroScope_1959_);
lean_ctor_set(v___x_1965_, 7, v_ref_1964_);
lean_ctor_set(v___x_1965_, 8, v_snap_x3f_1960_);
lean_ctor_set(v___x_1965_, 9, v_cancelTk_x3f_1961_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*10, v_suppressElabErrors_1962_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*10 + 1, v_checkDeprecated_1963_);
v___x_1966_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_1947_, v___x_1965_, v___y_1949_);
lean_dec_ref_known(v___x_1965_, 10);
return v___x_1966_;
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref(v_msg_1947_);
v_a_1967_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1951_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1951_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg___boxed(lean_object* v_ref_1975_, lean_object* v_msg_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_1975_, v_msg_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v_ref_1975_);
return v_res_1980_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__0));
v___x_1983_ = l_Lean_stringToMessageData(v___x_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(lean_object* v_stx_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_unsigned_to_nat(1u);
v___x_1998_ = l_Lean_Syntax_getArg(v_stx_1987_, v___x_1997_);
if (lean_obj_tag(v___x_1998_) == 1)
{
lean_object* v_kind_1999_; 
v_kind_1999_ = lean_ctor_get(v___x_1998_, 1);
lean_inc(v_kind_1999_);
if (lean_obj_tag(v_kind_1999_) == 1)
{
lean_object* v_pre_2000_; 
v_pre_2000_ = lean_ctor_get(v_kind_1999_, 0);
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
lean_inc(v_pre_2002_);
if (lean_obj_tag(v_pre_2002_) == 1)
{
lean_object* v_pre_2003_; 
v_pre_2003_ = lean_ctor_get(v_pre_2002_, 0);
if (lean_obj_tag(v_pre_2003_) == 0)
{
lean_object* v_args_2004_; lean_object* v_str_2005_; lean_object* v_str_2006_; lean_object* v_str_2007_; lean_object* v_str_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v_args_2004_ = lean_ctor_get(v___x_1998_, 2);
lean_inc_ref(v_args_2004_);
lean_dec_ref_known(v___x_1998_, 3);
v_str_2005_ = lean_ctor_get(v_kind_1999_, 1);
lean_inc_ref(v_str_2005_);
lean_dec_ref_known(v_kind_1999_, 2);
v_str_2006_ = lean_ctor_get(v_pre_2000_, 1);
lean_inc_ref(v_str_2006_);
lean_dec_ref_known(v_pre_2000_, 2);
v_str_2007_ = lean_ctor_get(v_pre_2001_, 1);
lean_inc_ref(v_str_2007_);
lean_dec_ref_known(v_pre_2001_, 2);
v_str_2008_ = lean_ctor_get(v_pre_2002_, 1);
lean_inc_ref(v_str_2008_);
lean_dec_ref_known(v_pre_2002_, 2);
v___x_2009_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_initFn___closed__5_00___x40_Lean_Elab_GuardMsgs_2868335979____hygCtx___hyg_4_));
v___x_2010_ = lean_string_dec_eq(v_str_2008_, v___x_2009_);
lean_dec_ref(v_str_2008_);
if (v___x_2010_ == 0)
{
lean_dec_ref(v_str_2007_);
lean_dec_ref(v_str_2006_);
lean_dec_ref(v_str_2005_);
lean_dec_ref(v_args_2004_);
goto v___jp_1991_;
}
else
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__2));
v___x_2012_ = lean_string_dec_eq(v_str_2007_, v___x_2011_);
lean_dec_ref(v_str_2007_);
if (v___x_2012_ == 0)
{
lean_dec_ref(v_str_2006_);
lean_dec_ref(v_str_2005_);
lean_dec_ref(v_args_2004_);
goto v___jp_1991_;
}
else
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__3));
v___x_2014_ = lean_string_dec_eq(v_str_2006_, v___x_2013_);
lean_dec_ref(v_str_2006_);
if (v___x_2014_ == 0)
{
lean_dec_ref(v_str_2005_);
lean_dec_ref(v_args_2004_);
goto v___jp_1991_;
}
else
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__4));
v___x_2016_ = lean_string_dec_eq(v_str_2005_, v___x_2015_);
lean_dec_ref(v_str_2005_);
if (v___x_2016_ == 0)
{
lean_dec_ref(v_args_2004_);
goto v___jp_1991_;
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2017_ = lean_array_get_size(v_args_2004_);
v___x_2018_ = lean_unsigned_to_nat(2u);
v___x_2019_ = lean_nat_dec_eq(v___x_2017_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_dec_ref(v_args_2004_);
goto v___jp_1991_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_unsigned_to_nat(0u);
v___x_2021_ = lean_array_fget(v_args_2004_, v___x_2020_);
lean_dec_ref(v_args_2004_);
if (lean_obj_tag(v___x_2021_) == 2)
{
lean_object* v_val_2022_; lean_object* v___x_2023_; 
lean_dec(v_stx_1987_);
v_val_2022_ = lean_ctor_get(v___x_2021_, 1);
lean_inc_ref(v_val_2022_);
lean_dec_ref_known(v___x_2021_, 2);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v_val_2022_);
return v___x_2023_;
}
else
{
lean_dec(v___x_2021_);
goto v___jp_1991_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2002_, 2);
lean_dec_ref_known(v_pre_2001_, 2);
lean_dec_ref_known(v_pre_2000_, 2);
lean_dec_ref_known(v_kind_1999_, 2);
lean_dec_ref_known(v___x_1998_, 3);
goto v___jp_1991_;
}
}
else
{
lean_dec_ref_known(v_pre_2001_, 2);
lean_dec(v_pre_2002_);
lean_dec_ref_known(v_pre_2000_, 2);
lean_dec_ref_known(v_kind_1999_, 2);
lean_dec_ref_known(v___x_1998_, 3);
goto v___jp_1991_;
}
}
else
{
lean_dec_ref_known(v_pre_2000_, 2);
lean_dec(v_pre_2001_);
lean_dec_ref_known(v_kind_1999_, 2);
lean_dec_ref_known(v___x_1998_, 3);
goto v___jp_1991_;
}
}
else
{
lean_dec_ref_known(v_kind_1999_, 2);
lean_dec(v_pre_2000_);
lean_dec_ref_known(v___x_1998_, 3);
goto v___jp_1991_;
}
}
else
{
lean_dec(v_kind_1999_);
lean_dec_ref_known(v___x_1998_, 3);
goto v___jp_1991_;
}
}
else
{
lean_dec(v___x_1998_);
goto v___jp_1991_;
}
v___jp_1991_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1992_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___closed__1);
lean_inc(v_stx_1987_);
v___x_1993_ = l_Lean_MessageData_ofSyntax(v_stx_1987_);
v___x_1994_ = l_Lean_indentD(v___x_1993_);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1992_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_stx_1987_, v___x_1995_, v___y_1988_, v___y_1989_);
lean_dec(v_stx_1987_);
return v___x_1996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10___boxed(lean_object* v_stx_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_stx_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(lean_object* v_as_2029_, size_t v_sz_2030_, size_t v_i_2031_, lean_object* v_b_2032_){
_start:
{
lean_object* v_a_2034_; uint8_t v___x_2038_; 
v___x_2038_ = lean_usize_dec_lt(v_i_2031_, v_sz_2030_);
if (v___x_2038_ == 0)
{
return v_b_2032_;
}
else
{
lean_object* v_a_2039_; lean_object* v_fst_2040_; lean_object* v_snd_2041_; lean_object* v_out_2042_; uint8_t v___x_2043_; 
v_a_2039_ = lean_array_uget_borrowed(v_as_2029_, v_i_2031_);
v_fst_2040_ = lean_ctor_get(v_a_2039_, 0);
v_snd_2041_ = lean_ctor_get(v_a_2039_, 1);
v_out_2042_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2043_ = lean_string_dec_eq(v_snd_2041_, v_out_2042_);
if (v___x_2043_ == 0)
{
uint8_t v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2044_ = lean_unbox(v_fst_2040_);
v___x_2045_ = l_Lean_Diff_Action_linePrefix(v___x_2044_);
v___x_2046_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__8));
v___x_2047_ = lean_string_append(v___x_2045_, v___x_2046_);
v___x_2048_ = lean_string_append(v___x_2047_, v_snd_2041_);
v___x_2049_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
v___x_2051_ = lean_string_append(v_b_2032_, v___x_2050_);
lean_dec_ref(v___x_2050_);
v_a_2034_ = v___x_2051_;
goto v___jp_2033_;
}
else
{
uint8_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2052_ = lean_unbox(v_fst_2040_);
v___x_2053_ = l_Lean_Diff_Action_linePrefix(v___x_2052_);
v___x_2054_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__0));
v___x_2055_ = lean_string_append(v___x_2053_, v___x_2054_);
v___x_2056_ = lean_string_append(v_b_2032_, v___x_2055_);
lean_dec_ref(v___x_2055_);
v_a_2034_ = v___x_2056_;
goto v___jp_2033_;
}
}
v___jp_2033_:
{
size_t v___x_2035_; size_t v___x_2036_; 
v___x_2035_ = ((size_t)1ULL);
v___x_2036_ = lean_usize_add(v_i_2031_, v___x_2035_);
v_i_2031_ = v___x_2036_;
v_b_2032_ = v_a_2034_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19___boxed(lean_object* v_as_2057_, lean_object* v_sz_2058_, lean_object* v_i_2059_, lean_object* v_b_2060_){
_start:
{
size_t v_sz_boxed_2061_; size_t v_i_boxed_2062_; lean_object* v_res_2063_; 
v_sz_boxed_2061_ = lean_unbox_usize(v_sz_2058_);
lean_dec(v_sz_2058_);
v_i_boxed_2062_ = lean_unbox_usize(v_i_2059_);
lean_dec(v_i_2059_);
v_res_2063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_as_2057_, v_sz_boxed_2061_, v_i_boxed_2062_, v_b_2060_);
lean_dec_ref(v_as_2057_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(lean_object* v_lines_2064_){
_start:
{
lean_object* v_out_2065_; size_t v_sz_2066_; size_t v___x_2067_; lean_object* v___x_2068_; 
v_out_2065_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v_sz_2066_ = lean_array_size(v_lines_2064_);
v___x_2067_ = ((size_t)0ULL);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8_spec__19(v_lines_2064_, v_sz_2066_, v___x_2067_, v_out_2065_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8___boxed(lean_object* v_lines_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v_lines_2069_);
lean_dec_ref(v_lines_2069_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(lean_object* v_filterFn_2071_, lean_object* v_as_x27_2072_, lean_object* v_b_2073_){
_start:
{
if (lean_obj_tag(v_as_x27_2072_) == 0)
{
lean_object* v___x_2075_; 
lean_dec_ref(v_filterFn_2071_);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_b_2073_);
return v___x_2075_;
}
else
{
lean_object* v_head_2076_; uint8_t v_isSilent_2077_; 
v_head_2076_ = lean_ctor_get(v_as_x27_2072_, 0);
v_isSilent_2077_ = lean_ctor_get_uint8(v_head_2076_, sizeof(void*)*5 + 2);
if (v_isSilent_2077_ == 0)
{
lean_object* v_tail_2078_; lean_object* v_fst_2079_; lean_object* v_snd_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2100_; 
v_tail_2078_ = lean_ctor_get(v_as_x27_2072_, 1);
v_fst_2079_ = lean_ctor_get(v_b_2073_, 0);
v_snd_2080_ = lean_ctor_get(v_b_2073_, 1);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_b_2073_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2082_ = v_b_2073_;
v_isShared_2083_ = v_isSharedCheck_2100_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_snd_2080_);
lean_inc(v_fst_2079_);
lean_dec(v_b_2073_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2100_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
lean_inc_ref(v_filterFn_2071_);
lean_inc(v_head_2076_);
v___x_2084_ = lean_apply_1(v_filterFn_2071_, v_head_2076_);
v___x_2085_ = lean_unbox(v___x_2084_);
switch(v___x_2085_)
{
case 0:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_inc(v_head_2076_);
v___x_2086_ = l_Lean_MessageLog_add(v_head_2076_, v_fst_2079_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2086_);
v___x_2088_ = v___x_2082_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_snd_2080_);
v___x_2088_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
v_as_x27_2072_ = v_tail_2078_;
v_b_2073_ = v___x_2088_;
goto _start;
}
}
case 1:
{
lean_object* v___x_2092_; 
if (v_isShared_2083_ == 0)
{
v___x_2092_ = v___x_2082_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_fst_2079_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_snd_2080_);
v___x_2092_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
v_as_x27_2072_ = v_tail_2078_;
v_b_2073_ = v___x_2092_;
goto _start;
}
}
default: 
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
lean_inc(v_head_2076_);
v___x_2095_ = l_Lean_MessageLog_add(v_head_2076_, v_snd_2080_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 1, v___x_2095_);
v___x_2097_ = v___x_2082_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_fst_2079_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
v_as_x27_2072_ = v_tail_2078_;
v_b_2073_ = v___x_2097_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_tail_2101_; lean_object* v_fst_2102_; lean_object* v_snd_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2111_; 
v_tail_2101_ = lean_ctor_get(v_as_x27_2072_, 1);
v_fst_2102_ = lean_ctor_get(v_b_2073_, 0);
v_snd_2103_ = lean_ctor_get(v_b_2073_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_b_2073_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2105_ = v_b_2073_;
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_snd_2103_);
lean_inc(v_fst_2102_);
lean_dec(v_b_2073_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_fst_2102_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_snd_2103_);
v___x_2108_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
v_as_x27_2072_ = v_tail_2101_;
v_b_2073_ = v___x_2108_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg___boxed(lean_object* v_filterFn_2112_, lean_object* v_as_x27_2113_, lean_object* v_b_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_2112_, v_as_x27_2113_, v_b_2114_);
lean_dec(v_as_x27_2113_);
return v_res_2116_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(lean_object* v_s_2117_, lean_object* v_a_2118_, uint8_t v_b_2119_){
_start:
{
uint8_t v___x_2120_; 
v___x_2120_ = 0;
switch(lean_obj_tag(v_a_2118_))
{
case 0:
{
lean_object* v_pos_2121_; lean_object* v_startInclusive_2122_; lean_object* v_endExclusive_2123_; lean_object* v___x_2124_; uint8_t v_decide_2125_; 
v_pos_2121_ = lean_ctor_get(v_a_2118_, 0);
lean_inc(v_pos_2121_);
lean_dec_ref_known(v_a_2118_, 1);
v_startInclusive_2122_ = lean_ctor_get(v_s_2117_, 1);
v_endExclusive_2123_ = lean_ctor_get(v_s_2117_, 2);
v___x_2124_ = lean_nat_sub(v_endExclusive_2123_, v_startInclusive_2122_);
v_decide_2125_ = lean_nat_dec_eq(v_pos_2121_, v___x_2124_);
lean_dec(v___x_2124_);
lean_dec(v_pos_2121_);
if (v_decide_2125_ == 0)
{
uint8_t v___x_2126_; 
v___x_2126_ = 1;
return v___x_2126_;
}
else
{
return v_decide_2125_;
}
}
case 1:
{
lean_object* v_pos_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2140_; 
v_pos_2127_ = lean_ctor_get(v_a_2118_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_a_2118_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2129_ = v_a_2118_;
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_pos_2127_);
lean_dec(v_a_2118_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_str_2131_; lean_object* v_startInclusive_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2137_; 
v_str_2131_ = lean_ctor_get(v_s_2117_, 0);
v_startInclusive_2132_ = lean_ctor_get(v_s_2117_, 1);
v___x_2133_ = lean_nat_add(v_startInclusive_2132_, v_pos_2127_);
lean_dec(v_pos_2127_);
v___x_2134_ = lean_string_utf8_next_fast(v_str_2131_, v___x_2133_);
lean_dec(v___x_2133_);
v___x_2135_ = lean_nat_sub(v___x_2134_, v_startInclusive_2132_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set_tag(v___x_2129_, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2135_);
v___x_2137_ = v___x_2129_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
v_a_2118_ = v___x_2137_;
v_b_2119_ = v___x_2120_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2141_; lean_object* v_table_2142_; lean_object* v_stackPos_2143_; lean_object* v_needlePos_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2199_; 
v_needle_2141_ = lean_ctor_get(v_a_2118_, 0);
v_table_2142_ = lean_ctor_get(v_a_2118_, 1);
v_stackPos_2143_ = lean_ctor_get(v_a_2118_, 2);
v_needlePos_2144_ = lean_ctor_get(v_a_2118_, 3);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_a_2118_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2146_ = v_a_2118_;
v_isShared_2147_ = v_isSharedCheck_2199_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_needlePos_2144_);
lean_inc(v_stackPos_2143_);
lean_inc(v_table_2142_);
lean_inc(v_needle_2141_);
lean_dec(v_a_2118_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2199_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_str_2148_; lean_object* v_startInclusive_2149_; lean_object* v_endExclusive_2150_; lean_object* v_str_2151_; lean_object* v_startInclusive_2152_; lean_object* v_endExclusive_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v_str_2148_ = lean_ctor_get(v_needle_2141_, 0);
v_startInclusive_2149_ = lean_ctor_get(v_needle_2141_, 1);
v_endExclusive_2150_ = lean_ctor_get(v_needle_2141_, 2);
v_str_2151_ = lean_ctor_get(v_s_2117_, 0);
v_startInclusive_2152_ = lean_ctor_get(v_s_2117_, 1);
v_endExclusive_2153_ = lean_ctor_get(v_s_2117_, 2);
v___x_2154_ = lean_nat_sub(v_stackPos_2143_, v_needlePos_2144_);
v___x_2155_ = lean_nat_sub(v_endExclusive_2150_, v_startInclusive_2149_);
v___x_2156_ = lean_nat_add(v___x_2154_, v___x_2155_);
v___x_2157_ = lean_nat_sub(v_endExclusive_2153_, v_startInclusive_2152_);
v___x_2158_ = lean_nat_dec_le(v___x_2156_, v___x_2157_);
lean_dec(v___x_2156_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
lean_dec(v___x_2155_);
lean_del_object(v___x_2146_);
lean_dec(v_needlePos_2144_);
lean_dec(v_stackPos_2143_);
lean_dec_ref(v_table_2142_);
lean_dec_ref(v_needle_2141_);
v___x_2159_ = lean_unsigned_to_nat(1u);
v___x_2160_ = lean_nat_add(v___x_2154_, v___x_2159_);
lean_dec(v___x_2154_);
v___x_2161_ = lean_nat_dec_le(v___x_2160_, v___x_2157_);
lean_dec(v___x_2157_);
lean_dec(v___x_2160_);
if (v___x_2161_ == 0)
{
return v_b_2119_;
}
else
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_box(3);
v_a_2118_ = v___x_2162_;
v_b_2119_ = v___x_2120_;
goto _start;
}
}
else
{
lean_object* v___x_2164_; uint8_t v_stackByte_2165_; lean_object* v___x_2166_; uint8_t v_patByte_2167_; uint8_t v___x_2168_; 
lean_dec(v___x_2157_);
lean_dec(v___x_2154_);
v___x_2164_ = lean_nat_add(v_startInclusive_2152_, v_stackPos_2143_);
v_stackByte_2165_ = lean_string_get_byte_fast(v_str_2151_, v___x_2164_);
v___x_2166_ = lean_nat_add(v_startInclusive_2149_, v_needlePos_2144_);
v_patByte_2167_ = lean_string_get_byte_fast(v_str_2148_, v___x_2166_);
v___x_2168_ = lean_uint8_dec_eq(v_stackByte_2165_, v_patByte_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; uint8_t v_decide_2170_; 
lean_dec(v___x_2155_);
v___x_2169_ = lean_unsigned_to_nat(0u);
v_decide_2170_ = lean_nat_dec_eq(v_needlePos_2144_, v___x_2169_);
if (v_decide_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v_newNeedlePos_2173_; uint8_t v___x_2174_; 
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_sub(v_needlePos_2144_, v___x_2171_);
lean_dec(v_needlePos_2144_);
v_newNeedlePos_2173_ = lean_array_fget_borrowed(v_table_2142_, v___x_2172_);
lean_dec(v___x_2172_);
v___x_2174_ = lean_nat_dec_eq(v_newNeedlePos_2173_, v___x_2169_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2176_; 
lean_inc(v_newNeedlePos_2173_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 3, v_newNeedlePos_2173_);
v___x_2176_ = v___x_2146_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_needle_2141_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_table_2142_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_stackPos_2143_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v_newNeedlePos_2173_);
v___x_2176_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
v_a_2118_ = v___x_2176_;
v_b_2119_ = v___x_2120_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2179_; lean_object* v___x_2181_; 
v_nextStackPos_2179_ = l_String_Slice_posGE___redArg(v_s_2117_, v_stackPos_2143_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 3, v___x_2169_);
lean_ctor_set(v___x_2146_, 2, v_nextStackPos_2179_);
v___x_2181_ = v___x_2146_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_needle_2141_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_table_2142_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v_nextStackPos_2179_);
lean_ctor_set(v_reuseFailAlloc_2183_, 3, v___x_2169_);
v___x_2181_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
v_a_2118_ = v___x_2181_;
v_b_2119_ = v___x_2120_;
goto _start;
}
}
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_nextStackPos_2186_; lean_object* v___x_2188_; 
lean_dec(v_needlePos_2144_);
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = lean_nat_add(v_stackPos_2143_, v___x_2184_);
lean_dec(v_stackPos_2143_);
v_nextStackPos_2186_ = l_String_Slice_posGE___redArg(v_s_2117_, v___x_2185_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 3, v___x_2169_);
lean_ctor_set(v___x_2146_, 2, v_nextStackPos_2186_);
v___x_2188_ = v___x_2146_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_needle_2141_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_table_2142_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_nextStackPos_2186_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v___x_2169_);
v___x_2188_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
v_a_2118_ = v___x_2188_;
v_b_2119_ = v___x_2120_;
goto _start;
}
}
}
else
{
lean_object* v___x_2191_; lean_object* v_nextNeedlePos_2192_; uint8_t v_decide_2193_; 
v___x_2191_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2192_ = lean_nat_add(v_needlePos_2144_, v___x_2191_);
lean_dec(v_needlePos_2144_);
v_decide_2193_ = lean_nat_dec_eq(v_nextNeedlePos_2192_, v___x_2155_);
lean_dec(v___x_2155_);
if (v_decide_2193_ == 0)
{
lean_object* v_nextStackPos_2194_; lean_object* v___x_2196_; 
v_nextStackPos_2194_ = lean_nat_add(v_stackPos_2143_, v___x_2191_);
lean_dec(v_stackPos_2143_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 3, v_nextNeedlePos_2192_);
lean_ctor_set(v___x_2146_, 2, v_nextStackPos_2194_);
v___x_2196_ = v___x_2146_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_needle_2141_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_table_2142_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_nextStackPos_2194_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_nextNeedlePos_2192_);
v___x_2196_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
v_a_2118_ = v___x_2196_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2192_);
lean_del_object(v___x_2146_);
lean_dec(v_stackPos_2143_);
lean_dec_ref(v_table_2142_);
lean_dec_ref(v_needle_2141_);
return v_decide_2193_;
}
}
}
}
}
default: 
{
return v_b_2119_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg___boxed(lean_object* v_s_2200_, lean_object* v_a_2201_, lean_object* v_b_2202_){
_start:
{
uint8_t v_b_boxed_2203_; uint8_t v_res_2204_; lean_object* v_r_2205_; 
v_b_boxed_2203_ = lean_unbox(v_b_2202_);
v_res_2204_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2200_, v_a_2201_, v_b_boxed_2203_);
lean_dec_ref(v_s_2200_);
v_r_2205_ = lean_box(v_res_2204_);
return v_r_2205_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(lean_object* v___x_2208_, lean_object* v_s_2209_){
_start:
{
lean_object* v___y_2211_; lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = lean_string_utf8_byte_size(v___x_2208_);
v___x_2216_ = lean_nat_dec_eq(v___x_2215_, v___x_2214_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2208_);
lean_ctor_set(v___x_2217_, 1, v___x_2214_);
lean_ctor_set(v___x_2217_, 2, v___x_2215_);
v___x_2218_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2217_);
v___x_2219_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2217_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
lean_ctor_set(v___x_2219_, 2, v___x_2214_);
lean_ctor_set(v___x_2219_, 3, v___x_2214_);
v___y_2211_ = v___x_2219_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2220_; 
lean_dec_ref(v___x_2208_);
v___x_2220_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___closed__0));
v___y_2211_ = v___x_2220_;
goto v___jp_2210_;
}
v___jp_2210_:
{
uint8_t v___x_2212_; uint8_t v___x_2213_; 
v___x_2212_ = 0;
v___x_2213_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_2209_, v___y_2211_, v___x_2212_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9___boxed(lean_object* v___x_2221_, lean_object* v_s_2222_){
_start:
{
uint8_t v_res_2223_; lean_object* v_r_2224_; 
v_res_2223_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_2221_, v_s_2222_);
lean_dec_ref(v_s_2222_);
v_r_2224_ = lean_box(v_res_2223_);
return v_r_2224_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(uint8_t v_suppressElabErrors_2225_, lean_object* v_x_2226_){
_start:
{
if (lean_obj_tag(v_x_2226_) == 1)
{
lean_object* v_pre_2227_; 
v_pre_2227_ = lean_ctor_get(v_x_2226_, 0);
if (lean_obj_tag(v_pre_2227_) == 0)
{
lean_object* v_str_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v_str_2228_ = lean_ctor_get(v_x_2226_, 1);
v___x_2229_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterSeverity___redArg___closed__2));
v___x_2230_ = lean_string_dec_eq(v_str_2228_, v___x_2229_);
if (v___x_2230_ == 0)
{
return v___x_2230_;
}
else
{
return v_suppressElabErrors_2225_;
}
}
else
{
uint8_t v___x_2231_; 
v___x_2231_ = 0;
return v___x_2231_;
}
}
else
{
uint8_t v___x_2232_; 
v___x_2232_ = 0;
return v___x_2232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_2233_, lean_object* v_x_2234_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2235_; uint8_t v_res_2236_; lean_object* v_r_2237_; 
v_suppressElabErrors_boxed_2235_ = lean_unbox(v_suppressElabErrors_2233_);
v_res_2236_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0(v_suppressElabErrors_boxed_2235_, v_x_2234_);
lean_dec(v_x_2234_);
v_r_2237_ = lean_box(v_res_2236_);
return v_r_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(lean_object* v_ref_2238_, lean_object* v_msgData_2239_, uint8_t v_severity_2240_, uint8_t v_isSilent_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; uint8_t v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; uint8_t v___y_2252_; lean_object* v___y_2253_; uint8_t v___y_2311_; lean_object* v___y_2312_; uint8_t v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2337_; uint8_t v___y_2338_; uint8_t v___y_2339_; lean_object* v___y_2340_; uint8_t v___y_2344_; uint8_t v___y_2345_; uint8_t v___x_2360_; uint8_t v___y_2362_; uint8_t v___x_2372_; 
v___x_2360_ = 2;
v___x_2372_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2240_, v___x_2360_);
if (v___x_2372_ == 0)
{
v___y_2362_ = v___x_2372_;
goto v___jp_2361_;
}
else
{
uint8_t v___x_2373_; 
lean_inc_ref(v_msgData_2239_);
v___x_2373_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2239_);
if (v___x_2373_ == 0)
{
v___y_2362_ = v___x_2373_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_dec_ref(v_msgData_2239_);
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
return v___x_2375_;
}
}
v___jp_2245_:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_Elab_Command_getScope___redArg(v___y_2253_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v_currNamespace_2256_; lean_object* v___x_2257_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
v_currNamespace_2256_ = lean_ctor_get(v_a_2255_, 2);
lean_inc(v_currNamespace_2256_);
lean_dec(v_a_2255_);
v___x_2257_ = l_Lean_Elab_Command_getScope___redArg(v___y_2253_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2293_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2293_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2293_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v_openDecls_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v_env_2267_; lean_object* v_messages_2268_; lean_object* v_scopes_2269_; lean_object* v_usedQuotCtxts_2270_; lean_object* v_nextMacroScope_2271_; lean_object* v_maxRecDepth_2272_; lean_object* v_ngen_2273_; lean_object* v_auxDeclNGen_2274_; lean_object* v_infoState_2275_; lean_object* v_traceState_2276_; lean_object* v_snapshotTasks_2277_; lean_object* v_prevLinterStates_2278_; lean_object* v_codeQualityEntryTasks_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2292_; 
v_openDecls_2262_ = lean_ctor_get(v_a_2258_, 3);
lean_inc(v_openDecls_2262_);
lean_dec(v_a_2258_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v_currNamespace_2256_);
lean_ctor_set(v___x_2263_, 1, v_openDecls_2262_);
v___x_2264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v___y_2246_);
lean_inc_ref(v___y_2247_);
lean_inc_ref(v___y_2251_);
v___x_2265_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2265_, 0, v___y_2251_);
lean_ctor_set(v___x_2265_, 1, v___y_2248_);
lean_ctor_set(v___x_2265_, 2, v___y_2250_);
lean_ctor_set(v___x_2265_, 3, v___y_2247_);
lean_ctor_set(v___x_2265_, 4, v___x_2264_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*5, v___y_2252_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*5 + 1, v___y_2249_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*5 + 2, v_isSilent_2241_);
v___x_2266_ = lean_st_ref_take(v___y_2253_);
v_env_2267_ = lean_ctor_get(v___x_2266_, 0);
v_messages_2268_ = lean_ctor_get(v___x_2266_, 1);
v_scopes_2269_ = lean_ctor_get(v___x_2266_, 2);
v_usedQuotCtxts_2270_ = lean_ctor_get(v___x_2266_, 3);
v_nextMacroScope_2271_ = lean_ctor_get(v___x_2266_, 4);
v_maxRecDepth_2272_ = lean_ctor_get(v___x_2266_, 5);
v_ngen_2273_ = lean_ctor_get(v___x_2266_, 6);
v_auxDeclNGen_2274_ = lean_ctor_get(v___x_2266_, 7);
v_infoState_2275_ = lean_ctor_get(v___x_2266_, 8);
v_traceState_2276_ = lean_ctor_get(v___x_2266_, 9);
v_snapshotTasks_2277_ = lean_ctor_get(v___x_2266_, 10);
v_prevLinterStates_2278_ = lean_ctor_get(v___x_2266_, 11);
v_codeQualityEntryTasks_2279_ = lean_ctor_get(v___x_2266_, 12);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2281_ = v___x_2266_;
v_isShared_2282_ = v_isSharedCheck_2292_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2279_);
lean_inc(v_prevLinterStates_2278_);
lean_inc(v_snapshotTasks_2277_);
lean_inc(v_traceState_2276_);
lean_inc(v_infoState_2275_);
lean_inc(v_auxDeclNGen_2274_);
lean_inc(v_ngen_2273_);
lean_inc(v_maxRecDepth_2272_);
lean_inc(v_nextMacroScope_2271_);
lean_inc(v_usedQuotCtxts_2270_);
lean_inc(v_scopes_2269_);
lean_inc(v_messages_2268_);
lean_inc(v_env_2267_);
lean_dec(v___x_2266_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2292_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2283_ = lean_box(0);
v___x_2284_ = l_Lean_MessageLog_add(v___x_2265_, v_messages_2268_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 1, v___x_2284_);
v___x_2286_ = v___x_2281_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_env_2267_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v___x_2284_);
lean_ctor_set(v_reuseFailAlloc_2291_, 2, v_scopes_2269_);
lean_ctor_set(v_reuseFailAlloc_2291_, 3, v_usedQuotCtxts_2270_);
lean_ctor_set(v_reuseFailAlloc_2291_, 4, v_nextMacroScope_2271_);
lean_ctor_set(v_reuseFailAlloc_2291_, 5, v_maxRecDepth_2272_);
lean_ctor_set(v_reuseFailAlloc_2291_, 6, v_ngen_2273_);
lean_ctor_set(v_reuseFailAlloc_2291_, 7, v_auxDeclNGen_2274_);
lean_ctor_set(v_reuseFailAlloc_2291_, 8, v_infoState_2275_);
lean_ctor_set(v_reuseFailAlloc_2291_, 9, v_traceState_2276_);
lean_ctor_set(v_reuseFailAlloc_2291_, 10, v_snapshotTasks_2277_);
lean_ctor_set(v_reuseFailAlloc_2291_, 11, v_prevLinterStates_2278_);
lean_ctor_set(v_reuseFailAlloc_2291_, 12, v_codeQualityEntryTasks_2279_);
v___x_2286_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2287_ = lean_st_ref_put(v___y_2253_, v___x_2286_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2283_);
v___x_2289_ = v___x_2260_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2283_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec(v_currNamespace_2256_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2248_);
lean_dec_ref(v___y_2246_);
v_a_2294_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2257_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2257_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2248_);
lean_dec_ref(v___y_2246_);
v_a_2302_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2254_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2254_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
v___jp_2310_:
{
lean_object* v_fileName_2315_; lean_object* v_fileMap_2316_; uint8_t v_suppressElabErrors_2317_; lean_object* v___x_2318_; lean_object* v___f_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2335_; 
v_fileName_2315_ = lean_ctor_get(v___y_2242_, 0);
v_fileMap_2316_ = lean_ctor_get(v___y_2242_, 1);
v_suppressElabErrors_2317_ = lean_ctor_get_uint8(v___y_2242_, sizeof(void*)*10);
v___x_2318_ = lean_box(v_suppressElabErrors_2317_);
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2319_, 0, v___x_2318_);
v___x_2320_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2239_);
v___x_2321_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v___x_2320_, v___y_2243_);
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2335_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2335_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_inc_ref_n(v_fileMap_2316_, 2);
v___x_2326_ = l_Lean_FileMap_toPosition(v_fileMap_2316_, v___y_2312_);
lean_dec(v___y_2312_);
v___x_2327_ = l_Lean_FileMap_toPosition(v_fileMap_2316_, v___y_2314_);
lean_dec(v___y_2314_);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
v___x_2329_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
if (v_suppressElabErrors_2317_ == 0)
{
lean_del_object(v___x_2324_);
lean_dec_ref(v___f_2319_);
v___y_2246_ = v_a_2322_;
v___y_2247_ = v___x_2329_;
v___y_2248_ = v___x_2326_;
v___y_2249_ = v___y_2311_;
v___y_2250_ = v___x_2328_;
v___y_2251_ = v_fileName_2315_;
v___y_2252_ = v___y_2313_;
v___y_2253_ = v___y_2243_;
goto v___jp_2245_;
}
else
{
uint8_t v___x_2330_; 
lean_inc(v_a_2322_);
v___x_2330_ = l_Lean_MessageData_hasTag(v___f_2319_, v_a_2322_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v___x_2333_; 
lean_dec_ref_known(v___x_2328_, 1);
lean_dec_ref(v___x_2326_);
lean_dec(v_a_2322_);
v___x_2331_ = lean_box(0);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2331_);
v___x_2333_ = v___x_2324_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
else
{
lean_del_object(v___x_2324_);
v___y_2246_ = v_a_2322_;
v___y_2247_ = v___x_2329_;
v___y_2248_ = v___x_2326_;
v___y_2249_ = v___y_2311_;
v___y_2250_ = v___x_2328_;
v___y_2251_ = v_fileName_2315_;
v___y_2252_ = v___y_2313_;
v___y_2253_ = v___y_2243_;
goto v___jp_2245_;
}
}
}
}
v___jp_2336_:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_Syntax_getTailPos_x3f(v___y_2337_, v___y_2339_);
lean_dec(v___y_2337_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_inc(v___y_2340_);
v___y_2311_ = v___y_2338_;
v___y_2312_ = v___y_2340_;
v___y_2313_ = v___y_2339_;
v___y_2314_ = v___y_2340_;
goto v___jp_2310_;
}
else
{
lean_object* v_val_2342_; 
v_val_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_val_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___y_2311_ = v___y_2338_;
v___y_2312_ = v___y_2340_;
v___y_2313_ = v___y_2339_;
v___y_2314_ = v_val_2342_;
goto v___jp_2310_;
}
}
v___jp_2343_:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_Elab_Command_getRef___redArg(v___y_2242_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v_ref_2348_; lean_object* v___x_2349_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v_ref_2348_ = l_Lean_replaceRef(v_ref_2238_, v_a_2347_);
lean_dec(v_a_2347_);
v___x_2349_ = l_Lean_Syntax_getPos_x3f(v_ref_2348_, v___y_2344_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_unsigned_to_nat(0u);
v___y_2337_ = v_ref_2348_;
v___y_2338_ = v___y_2345_;
v___y_2339_ = v___y_2344_;
v___y_2340_ = v___x_2350_;
goto v___jp_2336_;
}
else
{
lean_object* v_val_2351_; 
v_val_2351_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_val_2351_);
lean_dec_ref_known(v___x_2349_, 1);
v___y_2337_ = v_ref_2348_;
v___y_2338_ = v___y_2345_;
v___y_2339_ = v___y_2344_;
v___y_2340_ = v_val_2351_;
goto v___jp_2336_;
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v_msgData_2239_);
v_a_2352_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2346_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2346_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
v___jp_2361_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v_scopes_2365_; lean_object* v___x_2366_; lean_object* v_opts_2367_; uint8_t v___x_2368_; uint8_t v___x_2369_; 
v___x_2363_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2364_ = lean_st_ref_get(v___y_2243_);
v_scopes_2365_ = lean_ctor_get(v___x_2364_, 2);
lean_inc(v_scopes_2365_);
lean_dec(v___x_2364_);
v___x_2366_ = l_List_head_x21___redArg(v___x_2363_, v_scopes_2365_);
lean_dec(v_scopes_2365_);
v_opts_2367_ = lean_ctor_get(v___x_2366_, 1);
lean_inc_ref(v_opts_2367_);
lean_dec(v___x_2366_);
v___x_2368_ = 1;
v___x_2369_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2240_, v___x_2368_);
if (v___x_2369_ == 0)
{
lean_dec_ref(v_opts_2367_);
v___y_2344_ = v___y_2362_;
v___y_2345_ = v_severity_2240_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2370_; uint8_t v___x_2371_; 
v___x_2370_ = l_Lean_warningAsError;
v___x_2371_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_2367_, v___x_2370_);
lean_dec_ref(v_opts_2367_);
if (v___x_2371_ == 0)
{
v___y_2344_ = v___y_2362_;
v___y_2345_ = v_severity_2240_;
goto v___jp_2343_;
}
else
{
v___y_2344_ = v___y_2362_;
v___y_2345_ = v___x_2360_;
goto v___jp_2343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2___boxed(lean_object* v_ref_2376_, lean_object* v_msgData_2377_, lean_object* v_severity_2378_, lean_object* v_isSilent_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
uint8_t v_severity_boxed_2383_; uint8_t v_isSilent_boxed_2384_; lean_object* v_res_2385_; 
v_severity_boxed_2383_ = lean_unbox(v_severity_2378_);
v_isSilent_boxed_2384_ = lean_unbox(v_isSilent_2379_);
v_res_2385_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2376_, v_msgData_2377_, v_severity_boxed_2383_, v_isSilent_boxed_2384_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v_ref_2376_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(lean_object* v_ref_2386_, lean_object* v_msgData_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
uint8_t v___x_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = 2;
v___x_2392_ = 0;
v___x_2393_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_ref_2386_, v_msgData_2387_, v___x_2391_, v___x_2392_, v___y_2388_, v___y_2389_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2___boxed(lean_object* v_ref_2394_, lean_object* v_msgData_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v_ref_2394_, v_msgData_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v_ref_2394_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(lean_object* v___x_2400_, lean_object* v___x_2401_, lean_object* v___x_2402_, lean_object* v_a_2403_, lean_object* v_b_2404_){
_start:
{
lean_object* v_it_2406_; lean_object* v_startInclusive_2407_; lean_object* v_endExclusive_2408_; 
if (lean_obj_tag(v_a_2403_) == 0)
{
lean_object* v_currPos_2413_; lean_object* v_searcher_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2443_; 
v_currPos_2413_ = lean_ctor_get(v_a_2403_, 0);
v_searcher_2414_ = lean_ctor_get(v_a_2403_, 1);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_a_2403_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2416_ = v_a_2403_;
v_isShared_2417_ = v_isSharedCheck_2443_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_searcher_2414_);
lean_inc(v_currPos_2413_);
lean_dec(v_a_2403_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2443_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_str_2418_; lean_object* v_startInclusive_2419_; lean_object* v_endExclusive_2420_; lean_object* v___x_2421_; uint8_t v_decide_2422_; 
v_str_2418_ = lean_ctor_get(v___x_2401_, 0);
v_startInclusive_2419_ = lean_ctor_get(v___x_2401_, 1);
v_endExclusive_2420_ = lean_ctor_get(v___x_2401_, 2);
v___x_2421_ = lean_nat_sub(v_endExclusive_2420_, v_startInclusive_2419_);
v_decide_2422_ = lean_nat_dec_eq(v_searcher_2414_, v___x_2421_);
lean_dec(v___x_2421_);
if (v_decide_2422_ == 0)
{
uint32_t v___x_2423_; lean_object* v___x_2424_; uint32_t v___x_2425_; uint8_t v___x_2426_; 
v___x_2423_ = 10;
v___x_2424_ = lean_nat_add(v_startInclusive_2419_, v_searcher_2414_);
v___x_2425_ = lean_string_utf8_get_fast(v_str_2418_, v___x_2424_);
v___x_2426_ = lean_uint32_dec_eq(v___x_2425_, v___x_2423_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
lean_dec(v_searcher_2414_);
v___x_2427_ = lean_string_utf8_next_fast(v_str_2418_, v___x_2424_);
lean_dec(v___x_2424_);
v___x_2428_ = lean_nat_sub(v___x_2427_, v_startInclusive_2419_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v___x_2428_);
v___x_2430_ = v___x_2416_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_currPos_2413_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
v_a_2403_ = v___x_2430_;
goto _start;
}
}
else
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v_slice_2436_; lean_object* v_nextIt_2438_; 
v___x_2433_ = lean_string_utf8_next_fast(v_str_2418_, v___x_2424_);
v___x_2434_ = lean_nat_sub(v___x_2433_, v___x_2424_);
lean_dec(v___x_2424_);
v___x_2435_ = lean_nat_add(v_searcher_2414_, v___x_2434_);
lean_dec(v___x_2434_);
v_slice_2436_ = l_String_Slice_subslice_x21(v___x_2401_, v_currPos_2413_, v_searcher_2414_);
lean_inc(v___x_2435_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v___x_2435_);
lean_ctor_set(v___x_2416_, 0, v___x_2435_);
v_nextIt_2438_ = v___x_2416_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v___x_2435_);
v_nextIt_2438_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v_startInclusive_2439_; lean_object* v_endExclusive_2440_; 
v_startInclusive_2439_ = lean_ctor_get(v_slice_2436_, 0);
lean_inc(v_startInclusive_2439_);
v_endExclusive_2440_ = lean_ctor_get(v_slice_2436_, 1);
lean_inc(v_endExclusive_2440_);
lean_dec_ref(v_slice_2436_);
v_it_2406_ = v_nextIt_2438_;
v_startInclusive_2407_ = v_startInclusive_2439_;
v_endExclusive_2408_ = v_endExclusive_2440_;
goto v___jp_2405_;
}
}
}
else
{
lean_object* v___x_2442_; 
lean_del_object(v___x_2416_);
lean_dec(v_searcher_2414_);
v___x_2442_ = lean_box(1);
lean_inc(v___x_2402_);
v_it_2406_ = v___x_2442_;
v_startInclusive_2407_ = v_currPos_2413_;
v_endExclusive_2408_ = v___x_2402_;
goto v___jp_2405_;
}
}
}
else
{
lean_dec(v___x_2402_);
lean_dec_ref(v___x_2400_);
return v_b_2404_;
}
v___jp_2405_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_inc_ref(v___x_2400_);
v___x_2409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2400_);
lean_ctor_set(v___x_2409_, 1, v_startInclusive_2407_);
lean_ctor_set(v___x_2409_, 2, v_endExclusive_2408_);
v___x_2410_ = l_String_Slice_toString(v___x_2409_);
lean_dec_ref_known(v___x_2409_, 3);
v___x_2411_ = lean_array_push(v_b_2404_, v___x_2410_);
v_a_2403_ = v_it_2406_;
v_b_2404_ = v___x_2411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg___boxed(lean_object* v___x_2444_, lean_object* v___x_2445_, lean_object* v___x_2446_, lean_object* v_a_2447_, lean_object* v_b_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2444_, v___x_2445_, v___x_2446_, v_a_2447_, v_b_2448_);
lean_dec_ref(v___x_2445_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(lean_object* v___x_2450_, lean_object* v___x_2451_, lean_object* v___x_2452_, lean_object* v_a_2453_, lean_object* v_b_2454_){
_start:
{
lean_object* v_it_2456_; lean_object* v_startInclusive_2457_; lean_object* v_endExclusive_2458_; 
if (lean_obj_tag(v_a_2453_) == 0)
{
lean_object* v_currPos_2463_; lean_object* v_searcher_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2493_; 
v_currPos_2463_ = lean_ctor_get(v_a_2453_, 0);
v_searcher_2464_ = lean_ctor_get(v_a_2453_, 1);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_a_2453_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2466_ = v_a_2453_;
v_isShared_2467_ = v_isSharedCheck_2493_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_searcher_2464_);
lean_inc(v_currPos_2463_);
lean_dec(v_a_2453_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2493_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v_str_2468_; lean_object* v_startInclusive_2469_; lean_object* v_endExclusive_2470_; lean_object* v___x_2471_; uint8_t v_decide_2472_; 
v_str_2468_ = lean_ctor_get(v___x_2451_, 0);
v_startInclusive_2469_ = lean_ctor_get(v___x_2451_, 1);
v_endExclusive_2470_ = lean_ctor_get(v___x_2451_, 2);
v___x_2471_ = lean_nat_sub(v_endExclusive_2470_, v_startInclusive_2469_);
v_decide_2472_ = lean_nat_dec_eq(v_searcher_2464_, v___x_2471_);
lean_dec(v___x_2471_);
if (v_decide_2472_ == 0)
{
lean_object* v___x_2473_; uint32_t v___x_2474_; uint32_t v___x_2475_; uint8_t v___x_2476_; 
v___x_2473_ = lean_nat_add(v_startInclusive_2469_, v_searcher_2464_);
v___x_2474_ = lean_string_utf8_get_fast(v_str_2468_, v___x_2473_);
v___x_2475_ = 10;
v___x_2476_ = lean_uint32_dec_eq(v___x_2474_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
lean_dec(v_searcher_2464_);
v___x_2477_ = lean_string_utf8_next_fast(v_str_2468_, v___x_2473_);
lean_dec(v___x_2473_);
v___x_2478_ = lean_nat_sub(v___x_2477_, v_startInclusive_2469_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 1, v___x_2478_);
v___x_2480_ = v___x_2466_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_currPos_2463_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; 
v___x_2481_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2450_, v___x_2451_, v___x_2452_, v___x_2480_, v_b_2454_);
return v___x_2481_;
}
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v_slice_2486_; lean_object* v_nextIt_2488_; 
v___x_2483_ = lean_string_utf8_next_fast(v_str_2468_, v___x_2473_);
v___x_2484_ = lean_nat_sub(v___x_2483_, v___x_2473_);
lean_dec(v___x_2473_);
v___x_2485_ = lean_nat_add(v_searcher_2464_, v___x_2484_);
lean_dec(v___x_2484_);
v_slice_2486_ = l_String_Slice_subslice_x21(v___x_2451_, v_currPos_2463_, v_searcher_2464_);
lean_inc(v___x_2485_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 1, v___x_2485_);
lean_ctor_set(v___x_2466_, 0, v___x_2485_);
v_nextIt_2488_ = v___x_2466_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2485_);
v_nextIt_2488_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v_startInclusive_2489_; lean_object* v_endExclusive_2490_; 
v_startInclusive_2489_ = lean_ctor_get(v_slice_2486_, 0);
lean_inc(v_startInclusive_2489_);
v_endExclusive_2490_ = lean_ctor_get(v_slice_2486_, 1);
lean_inc(v_endExclusive_2490_);
lean_dec_ref(v_slice_2486_);
v_it_2456_ = v_nextIt_2488_;
v_startInclusive_2457_ = v_startInclusive_2489_;
v_endExclusive_2458_ = v_endExclusive_2490_;
goto v___jp_2455_;
}
}
}
else
{
lean_object* v___x_2492_; 
lean_del_object(v___x_2466_);
lean_dec(v_searcher_2464_);
v___x_2492_ = lean_box(1);
lean_inc(v___x_2452_);
v_it_2456_ = v___x_2492_;
v_startInclusive_2457_ = v_currPos_2463_;
v_endExclusive_2458_ = v___x_2452_;
goto v___jp_2455_;
}
}
}
else
{
lean_dec(v___x_2452_);
lean_dec_ref(v___x_2450_);
return v_b_2454_;
}
v___jp_2455_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_inc_ref(v___x_2450_);
v___x_2459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2450_);
lean_ctor_set(v___x_2459_, 1, v_startInclusive_2457_);
lean_ctor_set(v___x_2459_, 2, v_endExclusive_2458_);
v___x_2460_ = l_String_Slice_toString(v___x_2459_);
lean_dec_ref_known(v___x_2459_, 3);
v___x_2461_ = lean_array_push(v_b_2454_, v___x_2460_);
v___x_2462_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_2450_, v___x_2451_, v___x_2452_, v_it_2456_, v___x_2461_);
return v___x_2462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg___boxed(lean_object* v___x_2494_, lean_object* v___x_2495_, lean_object* v___x_2496_, lean_object* v_a_2497_, lean_object* v_b_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_2494_, v___x_2495_, v___x_2496_, v_a_2497_, v_b_2498_);
lean_dec_ref(v___x_2495_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(lean_object* v_t_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v___x_2503_; lean_object* v_infoState_2504_; uint8_t v_enabled_2505_; 
v___x_2503_ = lean_st_ref_get(v___y_2501_);
v_infoState_2504_ = lean_ctor_get(v___x_2503_, 8);
lean_inc_ref(v_infoState_2504_);
lean_dec(v___x_2503_);
v_enabled_2505_ = lean_ctor_get_uint8(v_infoState_2504_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2504_);
if (v_enabled_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec_ref(v_t_2500_);
v___x_2506_ = lean_box(0);
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
else
{
lean_object* v___x_2508_; lean_object* v_infoState_2509_; lean_object* v_env_2510_; lean_object* v_messages_2511_; lean_object* v_scopes_2512_; lean_object* v_usedQuotCtxts_2513_; lean_object* v_nextMacroScope_2514_; lean_object* v_maxRecDepth_2515_; lean_object* v_ngen_2516_; lean_object* v_auxDeclNGen_2517_; lean_object* v_traceState_2518_; lean_object* v_snapshotTasks_2519_; lean_object* v_prevLinterStates_2520_; lean_object* v_codeQualityEntryTasks_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2543_; 
v___x_2508_ = lean_st_ref_take(v___y_2501_);
v_infoState_2509_ = lean_ctor_get(v___x_2508_, 8);
v_env_2510_ = lean_ctor_get(v___x_2508_, 0);
v_messages_2511_ = lean_ctor_get(v___x_2508_, 1);
v_scopes_2512_ = lean_ctor_get(v___x_2508_, 2);
v_usedQuotCtxts_2513_ = lean_ctor_get(v___x_2508_, 3);
v_nextMacroScope_2514_ = lean_ctor_get(v___x_2508_, 4);
v_maxRecDepth_2515_ = lean_ctor_get(v___x_2508_, 5);
v_ngen_2516_ = lean_ctor_get(v___x_2508_, 6);
v_auxDeclNGen_2517_ = lean_ctor_get(v___x_2508_, 7);
v_traceState_2518_ = lean_ctor_get(v___x_2508_, 9);
v_snapshotTasks_2519_ = lean_ctor_get(v___x_2508_, 10);
v_prevLinterStates_2520_ = lean_ctor_get(v___x_2508_, 11);
v_codeQualityEntryTasks_2521_ = lean_ctor_get(v___x_2508_, 12);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2523_ = v___x_2508_;
v_isShared_2524_ = v_isSharedCheck_2543_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2521_);
lean_inc(v_prevLinterStates_2520_);
lean_inc(v_snapshotTasks_2519_);
lean_inc(v_traceState_2518_);
lean_inc(v_infoState_2509_);
lean_inc(v_auxDeclNGen_2517_);
lean_inc(v_ngen_2516_);
lean_inc(v_maxRecDepth_2515_);
lean_inc(v_nextMacroScope_2514_);
lean_inc(v_usedQuotCtxts_2513_);
lean_inc(v_scopes_2512_);
lean_inc(v_messages_2511_);
lean_inc(v_env_2510_);
lean_dec(v___x_2508_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2543_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
uint8_t v_enabled_2525_; lean_object* v_assignment_2526_; lean_object* v_lazyAssignment_2527_; lean_object* v_trees_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2542_; 
v_enabled_2525_ = lean_ctor_get_uint8(v_infoState_2509_, sizeof(void*)*3);
v_assignment_2526_ = lean_ctor_get(v_infoState_2509_, 0);
v_lazyAssignment_2527_ = lean_ctor_get(v_infoState_2509_, 1);
v_trees_2528_ = lean_ctor_get(v_infoState_2509_, 2);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_infoState_2509_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2530_ = v_infoState_2509_;
v_isShared_2531_ = v_isSharedCheck_2542_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_trees_2528_);
lean_inc(v_lazyAssignment_2527_);
lean_inc(v_assignment_2526_);
lean_dec(v_infoState_2509_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2542_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2532_ = lean_box(0);
v___x_2533_ = l_Lean_PersistentArray_push___redArg(v_trees_2528_, v_t_2500_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 2, v___x_2533_);
v___x_2535_ = v___x_2530_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_assignment_2526_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_lazyAssignment_2527_);
lean_ctor_set(v_reuseFailAlloc_2541_, 2, v___x_2533_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, sizeof(void*)*3, v_enabled_2525_);
v___x_2535_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2537_; 
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 8, v___x_2535_);
v___x_2537_ = v___x_2523_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_env_2510_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_messages_2511_);
lean_ctor_set(v_reuseFailAlloc_2540_, 2, v_scopes_2512_);
lean_ctor_set(v_reuseFailAlloc_2540_, 3, v_usedQuotCtxts_2513_);
lean_ctor_set(v_reuseFailAlloc_2540_, 4, v_nextMacroScope_2514_);
lean_ctor_set(v_reuseFailAlloc_2540_, 5, v_maxRecDepth_2515_);
lean_ctor_set(v_reuseFailAlloc_2540_, 6, v_ngen_2516_);
lean_ctor_set(v_reuseFailAlloc_2540_, 7, v_auxDeclNGen_2517_);
lean_ctor_set(v_reuseFailAlloc_2540_, 8, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2540_, 9, v_traceState_2518_);
lean_ctor_set(v_reuseFailAlloc_2540_, 10, v_snapshotTasks_2519_);
lean_ctor_set(v_reuseFailAlloc_2540_, 11, v_prevLinterStates_2520_);
lean_ctor_set(v_reuseFailAlloc_2540_, 12, v_codeQualityEntryTasks_2521_);
v___x_2537_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_st_ref_put(v___y_2501_, v___x_2537_);
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2532_);
return v___x_2539_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg___boxed(lean_object* v_t_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_2544_, v___y_2545_);
lean_dec(v___y_2545_);
return v_res_2547_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = lean_unsigned_to_nat(32u);
v___x_2549_ = lean_mk_empty_array_with_capacity(v___x_2548_);
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1(void){
_start:
{
size_t v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2551_ = ((size_t)5ULL);
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = lean_unsigned_to_nat(32u);
v___x_2554_ = lean_mk_empty_array_with_capacity(v___x_2553_);
v___x_2555_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__0);
v___x_2556_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
lean_ctor_set(v___x_2556_, 1, v___x_2554_);
lean_ctor_set(v___x_2556_, 2, v___x_2552_);
lean_ctor_set(v___x_2556_, 3, v___x_2552_);
lean_ctor_set_usize(v___x_2556_, 4, v___x_2551_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(lean_object* v_t_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; lean_object* v_infoState_2562_; uint8_t v_enabled_2563_; 
v___x_2561_ = lean_st_ref_get(v___y_2559_);
v_infoState_2562_ = lean_ctor_get(v___x_2561_, 8);
lean_inc_ref(v_infoState_2562_);
lean_dec(v___x_2561_);
v_enabled_2563_ = lean_ctor_get_uint8(v_infoState_2562_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2562_);
if (v_enabled_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec_ref(v_t_2557_);
v___x_2564_ = lean_box(0);
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
return v___x_2565_;
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___closed__1);
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v_t_2557_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v___x_2567_, v___y_2559_);
return v___x_2568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3___boxed(lean_object* v_t_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v_t_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(lean_object* v___x_2574_, lean_object* v_edited_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_fst_2578_; lean_object* v_snd_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2603_; 
v_fst_2578_ = lean_ctor_get(v_a_2577_, 0);
v_snd_2579_ = lean_ctor_get(v_a_2577_, 1);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_a_2577_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2581_ = v_a_2577_;
v_isShared_2582_ = v_isSharedCheck_2603_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_snd_2579_);
lean_inc(v_fst_2578_);
lean_dec(v_a_2577_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2603_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_nat_dec_lt(v_snd_2579_, v___x_2574_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2585_; 
if (v_isShared_2582_ == 0)
{
v___x_2585_ = v___x_2581_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_fst_2578_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_snd_2579_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2587_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___x_2588_ = lean_array_get_borrowed(v___x_2587_, v_edited_2575_, v_snd_2579_);
v___x_2589_ = lean_string_dec_eq(v___x_2588_, v_a_2576_);
if (v___x_2589_ == 0)
{
uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2590_ = 0;
v___x_2591_ = lean_box(v___x_2590_);
lean_inc(v___x_2588_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 1, v___x_2588_);
lean_ctor_set(v___x_2581_, 0, v___x_2591_);
v___x_2593_ = v___x_2581_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v___x_2588_);
v___x_2593_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2594_ = lean_array_push(v_fst_2578_, v___x_2593_);
v___x_2595_ = lean_unsigned_to_nat(1u);
v___x_2596_ = lean_nat_add(v_snd_2579_, v___x_2595_);
lean_dec(v_snd_2579_);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2594_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v_a_2577_ = v___x_2597_;
goto _start;
}
}
else
{
lean_object* v___x_2601_; 
if (v_isShared_2582_ == 0)
{
v___x_2601_ = v___x_2581_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_fst_2578_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_snd_2579_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg___boxed(lean_object* v___x_2604_, lean_object* v_edited_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2604_, v_edited_2605_, v_a_2606_, v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec_ref(v_edited_2605_);
lean_dec(v___x_2604_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(lean_object* v___x_2609_, lean_object* v_original_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_){
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
v___x_2623_ = lean_array_get_borrowed(v___x_2622_, v_original_2610_, v_snd_2614_);
v___x_2624_ = lean_string_dec_eq(v___x_2623_, v_a_2611_);
if (v___x_2624_ == 0)
{
uint8_t v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2625_ = 1;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg___boxed(lean_object* v___x_2639_, lean_object* v_original_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2639_, v_original_2640_, v_a_2641_, v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec_ref(v_original_2640_);
lean_dec(v___x_2639_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(lean_object* v___x_2644_, lean_object* v_original_2645_, lean_object* v___x_2646_, lean_object* v_edited_2647_, lean_object* v_as_2648_, size_t v_sz_2649_, size_t v_i_2650_, lean_object* v_b_2651_){
_start:
{
uint8_t v___x_2652_; 
v___x_2652_ = lean_usize_dec_lt(v_i_2650_, v_sz_2649_);
if (v___x_2652_ == 0)
{
return v_b_2651_;
}
else
{
lean_object* v_snd_2653_; lean_object* v_fst_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2701_; 
v_snd_2653_ = lean_ctor_get(v_b_2651_, 1);
v_fst_2654_ = lean_ctor_get(v_b_2651_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_b_2651_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2656_ = v_b_2651_;
v_isShared_2657_ = v_isSharedCheck_2701_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_snd_2653_);
lean_inc(v_fst_2654_);
lean_dec(v_b_2651_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2701_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2700_; 
v_fst_2658_ = lean_ctor_get(v_snd_2653_, 0);
v_snd_2659_ = lean_ctor_get(v_snd_2653_, 1);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_snd_2653_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2661_ = v_snd_2653_;
v_isShared_2662_ = v_isSharedCheck_2700_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_snd_2659_);
lean_inc(v_fst_2658_);
lean_dec(v_snd_2653_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2700_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_a_2663_; lean_object* v___x_2665_; 
v_a_2663_ = lean_array_uget_borrowed(v_as_2648_, v_i_2650_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v_fst_2658_);
lean_ctor_set(v___x_2661_, 0, v_fst_2654_);
v___x_2665_ = v___x_2661_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_fst_2654_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_fst_2658_);
v___x_2665_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2666_; lean_object* v_fst_2667_; lean_object* v_snd_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2698_; 
v___x_2666_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2644_, v_original_2645_, v_a_2663_, v___x_2665_);
v_fst_2667_ = lean_ctor_get(v___x_2666_, 0);
v_snd_2668_ = lean_ctor_get(v___x_2666_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2670_ = v___x_2666_;
v_isShared_2671_ = v_isSharedCheck_2698_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_snd_2668_);
lean_inc(v_fst_2667_);
lean_dec(v___x_2666_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2698_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v_snd_2659_);
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_fst_2667_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_snd_2659_);
v___x_2673_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v_fst_2675_; lean_object* v_snd_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2696_; 
v___x_2674_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2646_, v_edited_2647_, v_a_2663_, v___x_2673_);
v_fst_2675_ = lean_ctor_get(v___x_2674_, 0);
v_snd_2676_ = lean_ctor_get(v___x_2674_, 1);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2678_ = v___x_2674_;
v_isShared_2679_ = v_isSharedCheck_2696_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_snd_2676_);
lean_inc(v_fst_2675_);
lean_dec(v___x_2674_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2696_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
uint8_t v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2680_ = 2;
v___x_2681_ = lean_box(v___x_2680_);
lean_inc(v_a_2663_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v_a_2663_);
lean_ctor_set(v___x_2678_, 0, v___x_2681_);
v___x_2683_ = v___x_2678_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_a_2663_);
v___x_2683_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2684_ = lean_array_push(v_fst_2675_, v___x_2683_);
v___x_2685_ = lean_unsigned_to_nat(1u);
v___x_2686_ = lean_nat_add(v_snd_2668_, v___x_2685_);
lean_dec(v_snd_2668_);
v___x_2687_ = lean_nat_add(v_snd_2676_, v___x_2685_);
lean_dec(v_snd_2676_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 1, v___x_2687_);
lean_ctor_set(v___x_2656_, 0, v___x_2686_);
v___x_2689_ = v___x_2656_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; size_t v___x_2691_; size_t v___x_2692_; 
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2684_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = ((size_t)1ULL);
v___x_2692_ = lean_usize_add(v_i_2650_, v___x_2691_);
v_i_2650_ = v___x_2692_;
v_b_2651_ = v___x_2690_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24___boxed(lean_object* v___x_2702_, lean_object* v_original_2703_, lean_object* v___x_2704_, lean_object* v_edited_2705_, lean_object* v_as_2706_, lean_object* v_sz_2707_, lean_object* v_i_2708_, lean_object* v_b_2709_){
_start:
{
size_t v_sz_boxed_2710_; size_t v_i_boxed_2711_; lean_object* v_res_2712_; 
v_sz_boxed_2710_ = lean_unbox_usize(v_sz_2707_);
lean_dec(v_sz_2707_);
v_i_boxed_2711_ = lean_unbox_usize(v_i_2708_);
lean_dec(v_i_2708_);
v_res_2712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2702_, v_original_2703_, v___x_2704_, v_edited_2705_, v_as_2706_, v_sz_boxed_2710_, v_i_boxed_2711_, v_b_2709_);
lean_dec_ref(v_as_2706_);
lean_dec_ref(v_edited_2705_);
lean_dec(v___x_2704_);
lean_dec_ref(v_original_2703_);
lean_dec(v___x_2702_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(lean_object* v___x_2713_, lean_object* v_edited_2714_, lean_object* v___x_2715_, lean_object* v_original_2716_, lean_object* v_as_2717_, size_t v_sz_2718_, size_t v_i_2719_, lean_object* v_b_2720_){
_start:
{
uint8_t v___x_2721_; 
v___x_2721_ = lean_usize_dec_lt(v_i_2719_, v_sz_2718_);
if (v___x_2721_ == 0)
{
return v_b_2720_;
}
else
{
lean_object* v_snd_2722_; lean_object* v_fst_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2770_; 
v_snd_2722_ = lean_ctor_get(v_b_2720_, 1);
v_fst_2723_ = lean_ctor_get(v_b_2720_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_b_2720_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2725_ = v_b_2720_;
v_isShared_2726_ = v_isSharedCheck_2770_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_snd_2722_);
lean_inc(v_fst_2723_);
lean_dec(v_b_2720_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2770_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v_fst_2727_; lean_object* v_snd_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2769_; 
v_fst_2727_ = lean_ctor_get(v_snd_2722_, 0);
v_snd_2728_ = lean_ctor_get(v_snd_2722_, 1);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_snd_2722_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2730_ = v_snd_2722_;
v_isShared_2731_ = v_isSharedCheck_2769_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_snd_2728_);
lean_inc(v_fst_2727_);
lean_dec(v_snd_2722_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2769_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v_a_2732_; lean_object* v___x_2734_; 
v_a_2732_ = lean_array_uget_borrowed(v_as_2717_, v_i_2719_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 1, v_fst_2727_);
lean_ctor_set(v___x_2730_, 0, v_fst_2723_);
v___x_2734_ = v___x_2730_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_fst_2723_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_fst_2727_);
v___x_2734_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2735_; lean_object* v_fst_2736_; lean_object* v_snd_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2767_; 
v___x_2735_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_2715_, v_original_2716_, v_a_2732_, v___x_2734_);
v_fst_2736_ = lean_ctor_get(v___x_2735_, 0);
v_snd_2737_ = lean_ctor_get(v___x_2735_, 1);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2739_ = v___x_2735_;
v_isShared_2740_ = v_isSharedCheck_2767_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_snd_2737_);
lean_inc(v_fst_2736_);
lean_dec(v___x_2735_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2767_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 1, v_snd_2728_);
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_fst_2736_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_snd_2728_);
v___x_2742_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; lean_object* v_fst_2744_; lean_object* v_snd_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2765_; 
v___x_2743_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_2713_, v_edited_2714_, v_a_2732_, v___x_2742_);
v_fst_2744_ = lean_ctor_get(v___x_2743_, 0);
v_snd_2745_ = lean_ctor_get(v___x_2743_, 1);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2747_ = v___x_2743_;
v_isShared_2748_ = v_isSharedCheck_2765_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_snd_2745_);
lean_inc(v_fst_2744_);
lean_dec(v___x_2743_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2765_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2749_ = 2;
v___x_2750_ = lean_box(v___x_2749_);
lean_inc(v_a_2732_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 1, v_a_2732_);
lean_ctor_set(v___x_2747_, 0, v___x_2750_);
v___x_2752_ = v___x_2747_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_a_2732_);
v___x_2752_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2753_ = lean_array_push(v_fst_2744_, v___x_2752_);
v___x_2754_ = lean_unsigned_to_nat(1u);
v___x_2755_ = lean_nat_add(v_snd_2737_, v___x_2754_);
lean_dec(v_snd_2737_);
v___x_2756_ = lean_nat_add(v_snd_2745_, v___x_2754_);
lean_dec(v_snd_2745_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 1, v___x_2756_);
lean_ctor_set(v___x_2725_, 0, v___x_2755_);
v___x_2758_ = v___x_2725_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; size_t v___x_2760_; size_t v___x_2761_; lean_object* v___x_2762_; 
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2753_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = ((size_t)1ULL);
v___x_2761_ = lean_usize_add(v_i_2719_, v___x_2760_);
v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13_spec__24(v___x_2715_, v_original_2716_, v___x_2713_, v_edited_2714_, v_as_2717_, v_sz_2718_, v___x_2761_, v___x_2759_);
return v___x_2762_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13___boxed(lean_object* v___x_2771_, lean_object* v_edited_2772_, lean_object* v___x_2773_, lean_object* v_original_2774_, lean_object* v_as_2775_, lean_object* v_sz_2776_, lean_object* v_i_2777_, lean_object* v_b_2778_){
_start:
{
size_t v_sz_boxed_2779_; size_t v_i_boxed_2780_; lean_object* v_res_2781_; 
v_sz_boxed_2779_ = lean_unbox_usize(v_sz_2776_);
lean_dec(v_sz_2776_);
v_i_boxed_2780_ = lean_unbox_usize(v_i_2777_);
lean_dec(v_i_2777_);
v_res_2781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_2771_, v_edited_2772_, v___x_2773_, v_original_2774_, v_as_2775_, v_sz_boxed_2779_, v_i_boxed_2780_, v_b_2778_);
lean_dec_ref(v_as_2775_);
lean_dec_ref(v_original_2774_);
lean_dec(v___x_2773_);
lean_dec_ref(v_edited_2772_);
lean_dec(v___x_2771_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(lean_object* v___x_2782_, lean_object* v_original_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_fst_2785_; lean_object* v_snd_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2805_; 
v_fst_2785_ = lean_ctor_get(v_a_2784_, 0);
v_snd_2786_ = lean_ctor_get(v_a_2784_, 1);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_a_2784_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2788_ = v_a_2784_;
v_isShared_2789_ = v_isSharedCheck_2805_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_snd_2786_);
lean_inc(v_fst_2785_);
lean_dec(v_a_2784_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2805_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
uint8_t v___x_2790_; 
v___x_2790_ = lean_nat_dec_lt(v_snd_2786_, v___x_2782_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2792_; 
if (v_isShared_2789_ == 0)
{
v___x_2792_ = v___x_2788_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_fst_2785_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_snd_2786_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
else
{
uint8_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2794_ = 1;
v___x_2795_ = lean_array_fget_borrowed(v_original_2783_, v_snd_2786_);
v___x_2796_ = lean_box(v___x_2794_);
lean_inc(v___x_2795_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 1, v___x_2795_);
lean_ctor_set(v___x_2788_, 0, v___x_2796_);
v___x_2798_ = v___x_2788_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v___x_2795_);
v___x_2798_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2799_ = lean_array_push(v_fst_2785_, v___x_2798_);
v___x_2800_ = lean_unsigned_to_nat(1u);
v___x_2801_ = lean_nat_add(v_snd_2786_, v___x_2800_);
lean_dec(v_snd_2786_);
v___x_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2799_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v_a_2784_ = v___x_2802_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg___boxed(lean_object* v___x_2806_, lean_object* v_original_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_2806_, v_original_2807_, v_a_2808_);
lean_dec_ref(v_original_2807_);
lean_dec(v___x_2806_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(size_t v_sz_2810_, size_t v_i_2811_, lean_object* v_bs_2812_){
_start:
{
uint8_t v___x_2813_; 
v___x_2813_ = lean_usize_dec_lt(v_i_2811_, v_sz_2810_);
if (v___x_2813_ == 0)
{
return v_bs_2812_;
}
else
{
lean_object* v_v_2814_; lean_object* v___x_2815_; lean_object* v_bs_x27_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; size_t v___x_2820_; size_t v___x_2821_; lean_object* v___x_2822_; 
v_v_2814_ = lean_array_uget(v_bs_2812_, v_i_2811_);
v___x_2815_ = lean_unsigned_to_nat(0u);
v_bs_x27_2816_ = lean_array_uset(v_bs_2812_, v_i_2811_, v___x_2815_);
v___x_2817_ = 0;
v___x_2818_ = lean_box(v___x_2817_);
v___x_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
lean_ctor_set(v___x_2819_, 1, v_v_2814_);
v___x_2820_ = ((size_t)1ULL);
v___x_2821_ = lean_usize_add(v_i_2811_, v___x_2820_);
v___x_2822_ = lean_array_uset(v_bs_x27_2816_, v_i_2811_, v___x_2819_);
v_i_2811_ = v___x_2821_;
v_bs_2812_ = v___x_2822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17___boxed(lean_object* v_sz_2824_, lean_object* v_i_2825_, lean_object* v_bs_2826_){
_start:
{
size_t v_sz_boxed_2827_; size_t v_i_boxed_2828_; lean_object* v_res_2829_; 
v_sz_boxed_2827_ = lean_unbox_usize(v_sz_2824_);
lean_dec(v_sz_2824_);
v_i_boxed_2828_ = lean_unbox_usize(v_i_2825_);
lean_dec(v_i_2825_);
v_res_2829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_boxed_2827_, v_i_boxed_2828_, v_bs_2826_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(lean_object* v___x_2830_, lean_object* v_edited_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v_fst_2833_; lean_object* v_snd_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2853_; 
v_fst_2833_ = lean_ctor_get(v_a_2832_, 0);
v_snd_2834_ = lean_ctor_get(v_a_2832_, 1);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_a_2832_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2836_ = v_a_2832_;
v_isShared_2837_ = v_isSharedCheck_2853_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_snd_2834_);
lean_inc(v_fst_2833_);
lean_dec(v_a_2832_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2853_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
uint8_t v___x_2838_; 
v___x_2838_ = lean_nat_dec_lt(v_snd_2834_, v___x_2830_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2840_; 
if (v_isShared_2837_ == 0)
{
v___x_2840_ = v___x_2836_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_fst_2833_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_snd_2834_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
else
{
uint8_t v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2842_ = 0;
v___x_2843_ = lean_array_fget_borrowed(v_edited_2831_, v_snd_2834_);
v___x_2844_ = lean_box(v___x_2842_);
lean_inc(v___x_2843_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 1, v___x_2843_);
lean_ctor_set(v___x_2836_, 0, v___x_2844_);
v___x_2846_ = v___x_2836_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2844_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v___x_2843_);
v___x_2846_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2847_ = lean_array_push(v_fst_2833_, v___x_2846_);
v___x_2848_ = lean_unsigned_to_nat(1u);
v___x_2849_ = lean_nat_add(v_snd_2834_, v___x_2848_);
lean_dec(v_snd_2834_);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2847_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
v_a_2832_ = v___x_2850_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg___boxed(lean_object* v___x_2854_, lean_object* v_edited_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_2854_, v_edited_2855_, v_a_2856_);
lean_dec_ref(v_edited_2855_);
lean_dec(v___x_2854_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(lean_object* v_x_2858_, lean_object* v_x_2859_){
_start:
{
if (lean_obj_tag(v_x_2859_) == 0)
{
lean_inc(v_x_2858_);
return v_x_2858_;
}
else
{
lean_object* v_key_2860_; lean_object* v_value_2861_; lean_object* v_tail_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_key_2860_ = lean_ctor_get(v_x_2859_, 0);
v_value_2861_ = lean_ctor_get(v_x_2859_, 1);
v_tail_2862_ = lean_ctor_get(v_x_2859_, 2);
v___x_2863_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2858_, v_tail_2862_);
lean_inc(v_value_2861_);
lean_inc(v_key_2860_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v_key_2860_);
lean_ctor_set(v___x_2864_, 1, v_value_2861_);
v___x_2865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
lean_ctor_set(v___x_2865_, 1, v___x_2863_);
return v___x_2865_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17___boxed(lean_object* v_x_2866_, lean_object* v_x_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_x_2866_, v_x_2867_);
lean_dec(v_x_2867_);
lean_dec(v_x_2866_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(lean_object* v_as_2869_, size_t v_i_2870_, size_t v_stop_2871_, lean_object* v_b_2872_){
_start:
{
uint8_t v___x_2873_; 
v___x_2873_ = lean_usize_dec_eq(v_i_2870_, v_stop_2871_);
if (v___x_2873_ == 0)
{
size_t v___x_2874_; size_t v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2874_ = ((size_t)1ULL);
v___x_2875_ = lean_usize_sub(v_i_2870_, v___x_2874_);
v___x_2876_ = lean_array_uget_borrowed(v_as_2869_, v___x_2875_);
v___x_2877_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__17(v_b_2872_, v___x_2876_);
lean_dec(v_b_2872_);
v_i_2870_ = v___x_2875_;
v_b_2872_ = v___x_2877_;
goto _start;
}
else
{
return v_b_2872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18___boxed(lean_object* v_as_2879_, lean_object* v_i_2880_, lean_object* v_stop_2881_, lean_object* v_b_2882_){
_start:
{
size_t v_i_boxed_2883_; size_t v_stop_boxed_2884_; lean_object* v_res_2885_; 
v_i_boxed_2883_ = lean_unbox_usize(v_i_2880_);
lean_dec(v_i_2880_);
v_stop_boxed_2884_ = lean_unbox_usize(v_stop_2881_);
lean_dec(v_stop_2881_);
v_res_2885_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_as_2879_, v_i_boxed_2883_, v_stop_boxed_2884_, v_b_2882_);
lean_dec_ref(v_as_2879_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(lean_object* v_left_2886_, lean_object* v_right_2887_, lean_object* v_pref_2888_){
_start:
{
lean_object* v_start_2889_; lean_object* v_stop_2890_; lean_object* v_i_2891_; lean_object* v___x_2897_; uint8_t v___x_2898_; 
v_start_2889_ = lean_ctor_get(v_left_2886_, 1);
v_stop_2890_ = lean_ctor_get(v_left_2886_, 2);
v_i_2891_ = lean_array_get_size(v_pref_2888_);
v___x_2897_ = lean_nat_sub(v_stop_2890_, v_start_2889_);
v___x_2898_ = lean_nat_dec_lt(v_i_2891_, v___x_2897_);
lean_dec(v___x_2897_);
if (v___x_2898_ == 0)
{
goto v___jp_2892_;
}
else
{
lean_object* v_start_2899_; lean_object* v_stop_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v_start_2899_ = lean_ctor_get(v_right_2887_, 1);
v_stop_2900_ = lean_ctor_get(v_right_2887_, 2);
v___x_2901_ = lean_nat_sub(v_stop_2900_, v_start_2899_);
v___x_2902_ = lean_nat_dec_lt(v_i_2891_, v___x_2901_);
lean_dec(v___x_2901_);
if (v___x_2902_ == 0)
{
goto v___jp_2892_;
}
else
{
lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2903_ = l_Subarray_get___redArg(v_left_2886_, v_i_2891_);
v___x_2904_ = l_Subarray_get___redArg(v_right_2887_, v_i_2891_);
v___x_2905_ = lean_string_dec_eq(v___x_2903_, v___x_2904_);
lean_dec(v___x_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
lean_dec(v___x_2903_);
v___x_2906_ = l_Subarray_drop___redArg(v_left_2886_, v_i_2891_);
v___x_2907_ = l_Subarray_drop___redArg(v_right_2887_, v_i_2891_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v_pref_2888_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
return v___x_2909_;
}
else
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_array_push(v_pref_2888_, v___x_2903_);
v_pref_2888_ = v___x_2910_;
goto _start;
}
}
}
v___jp_2892_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2893_ = l_Subarray_drop___redArg(v_left_2886_, v_i_2891_);
v___x_2894_ = l_Subarray_drop___redArg(v_right_2887_, v_i_2891_);
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2893_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v_pref_2888_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(lean_object* v_left_2914_, lean_object* v_right_2915_){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_2917_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14_spec__18(v_left_2914_, v_right_2915_, v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(lean_object* v_a_2918_, lean_object* v_b_2919_, lean_object* v_x_2920_){
_start:
{
if (lean_obj_tag(v_x_2920_) == 0)
{
lean_dec(v_b_2919_);
lean_dec_ref(v_a_2918_);
return v_x_2920_;
}
else
{
lean_object* v_key_2921_; lean_object* v_value_2922_; lean_object* v_tail_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2935_; 
v_key_2921_ = lean_ctor_get(v_x_2920_, 0);
v_value_2922_ = lean_ctor_get(v_x_2920_, 1);
v_tail_2923_ = lean_ctor_get(v_x_2920_, 2);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_x_2920_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2925_ = v_x_2920_;
v_isShared_2926_ = v_isSharedCheck_2935_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_tail_2923_);
lean_inc(v_value_2922_);
lean_inc(v_key_2921_);
lean_dec(v_x_2920_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2935_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_string_dec_eq(v_key_2921_, v_a_2918_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2928_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_2918_, v_b_2919_, v_tail_2923_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 2, v___x_2928_);
v___x_2930_ = v___x_2925_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_key_2921_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_value_2922_);
lean_ctor_set(v_reuseFailAlloc_2931_, 2, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
else
{
lean_object* v___x_2933_; 
lean_dec(v_value_2922_);
lean_dec(v_key_2921_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v_b_2919_);
lean_ctor_set(v___x_2925_, 0, v_a_2918_);
v___x_2933_ = v___x_2925_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2918_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_b_2919_);
lean_ctor_set(v_reuseFailAlloc_2934_, 2, v_tail_2923_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(lean_object* v_x_2936_, lean_object* v_x_2937_){
_start:
{
if (lean_obj_tag(v_x_2937_) == 0)
{
return v_x_2936_;
}
else
{
lean_object* v_key_2938_; lean_object* v_value_2939_; lean_object* v_tail_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2963_; 
v_key_2938_ = lean_ctor_get(v_x_2937_, 0);
v_value_2939_ = lean_ctor_get(v_x_2937_, 1);
v_tail_2940_ = lean_ctor_get(v_x_2937_, 2);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_x_2937_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2942_ = v_x_2937_;
v_isShared_2943_ = v_isSharedCheck_2963_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_tail_2940_);
lean_inc(v_value_2939_);
lean_inc(v_key_2938_);
lean_dec(v_x_2937_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2963_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; uint64_t v___x_2945_; uint64_t v___x_2946_; uint64_t v___x_2947_; uint64_t v_fold_2948_; uint64_t v___x_2949_; uint64_t v___x_2950_; uint64_t v___x_2951_; size_t v___x_2952_; size_t v___x_2953_; size_t v___x_2954_; size_t v___x_2955_; size_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2944_ = lean_array_get_size(v_x_2936_);
v___x_2945_ = lean_string_hash(v_key_2938_);
v___x_2946_ = 32ULL;
v___x_2947_ = lean_uint64_shift_right(v___x_2945_, v___x_2946_);
v_fold_2948_ = lean_uint64_xor(v___x_2945_, v___x_2947_);
v___x_2949_ = 16ULL;
v___x_2950_ = lean_uint64_shift_right(v_fold_2948_, v___x_2949_);
v___x_2951_ = lean_uint64_xor(v_fold_2948_, v___x_2950_);
v___x_2952_ = lean_uint64_to_usize(v___x_2951_);
v___x_2953_ = lean_usize_of_nat(v___x_2944_);
v___x_2954_ = ((size_t)1ULL);
v___x_2955_ = lean_usize_sub(v___x_2953_, v___x_2954_);
v___x_2956_ = lean_usize_land(v___x_2952_, v___x_2955_);
v___x_2957_ = lean_array_uget_borrowed(v_x_2936_, v___x_2956_);
lean_inc(v___x_2957_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 2, v___x_2957_);
v___x_2959_ = v___x_2942_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_key_2938_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v_value_2939_);
lean_ctor_set(v_reuseFailAlloc_2962_, 2, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_array_uset(v_x_2936_, v___x_2956_, v___x_2959_);
v_x_2936_ = v___x_2960_;
v_x_2937_ = v_tail_2940_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(lean_object* v_i_2964_, lean_object* v_source_2965_, lean_object* v_target_2966_){
_start:
{
lean_object* v___x_2967_; uint8_t v___x_2968_; 
v___x_2967_ = lean_array_get_size(v_source_2965_);
v___x_2968_ = lean_nat_dec_lt(v_i_2964_, v___x_2967_);
if (v___x_2968_ == 0)
{
lean_dec_ref(v_source_2965_);
lean_dec(v_i_2964_);
return v_target_2966_;
}
else
{
lean_object* v_es_2969_; lean_object* v___x_2970_; lean_object* v_source_2971_; lean_object* v_target_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v_es_2969_ = lean_array_fget(v_source_2965_, v_i_2964_);
v___x_2970_ = lean_box(0);
v_source_2971_ = lean_array_fset(v_source_2965_, v_i_2964_, v___x_2970_);
v_target_2972_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_target_2966_, v_es_2969_);
v___x_2973_ = lean_unsigned_to_nat(1u);
v___x_2974_ = lean_nat_add(v_i_2964_, v___x_2973_);
lean_dec(v_i_2964_);
v_i_2964_ = v___x_2974_;
v_source_2965_ = v_source_2971_;
v_target_2966_ = v_target_2972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(lean_object* v_data_2976_){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v_nbuckets_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2977_ = lean_array_get_size(v_data_2976_);
v___x_2978_ = lean_unsigned_to_nat(2u);
v_nbuckets_2979_ = lean_nat_mul(v___x_2977_, v___x_2978_);
v___x_2980_ = lean_unsigned_to_nat(0u);
v___x_2981_ = lean_box(0);
v___x_2982_ = lean_mk_array(v_nbuckets_2979_, v___x_2981_);
v___x_2983_ = lean_array_propagate_mark(v_data_2976_, v___x_2982_);
v___x_2984_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v___x_2980_, v_data_2976_, v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(lean_object* v_a_2985_, lean_object* v_x_2986_){
_start:
{
if (lean_obj_tag(v_x_2986_) == 0)
{
uint8_t v___x_2987_; 
v___x_2987_ = 0;
return v___x_2987_;
}
else
{
lean_object* v_key_2988_; lean_object* v_tail_2989_; uint8_t v___x_2990_; 
v_key_2988_ = lean_ctor_get(v_x_2986_, 0);
v_tail_2989_ = lean_ctor_get(v_x_2986_, 2);
v___x_2990_ = lean_string_dec_eq(v_key_2988_, v_a_2985_);
if (v___x_2990_ == 0)
{
v_x_2986_ = v_tail_2989_;
goto _start;
}
else
{
return v___x_2990_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg___boxed(lean_object* v_a_2992_, lean_object* v_x_2993_){
_start:
{
uint8_t v_res_2994_; lean_object* v_r_2995_; 
v_res_2994_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_2992_, v_x_2993_);
lean_dec(v_x_2993_);
lean_dec_ref(v_a_2992_);
v_r_2995_ = lean_box(v_res_2994_);
return v_r_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(lean_object* v_m_2996_, lean_object* v_a_2997_, lean_object* v_b_2998_){
_start:
{
lean_object* v_size_2999_; lean_object* v_buckets_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3043_; 
v_size_2999_ = lean_ctor_get(v_m_2996_, 0);
v_buckets_3000_ = lean_ctor_get(v_m_2996_, 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_m_2996_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3002_ = v_m_2996_;
v_isShared_3003_ = v_isSharedCheck_3043_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_buckets_3000_);
lean_inc(v_size_2999_);
lean_dec(v_m_2996_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3043_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; uint64_t v___x_3005_; uint64_t v___x_3006_; uint64_t v___x_3007_; uint64_t v_fold_3008_; uint64_t v___x_3009_; uint64_t v___x_3010_; uint64_t v___x_3011_; size_t v___x_3012_; size_t v___x_3013_; size_t v___x_3014_; size_t v___x_3015_; size_t v___x_3016_; lean_object* v_bkt_3017_; uint8_t v___x_3018_; 
v___x_3004_ = lean_array_get_size(v_buckets_3000_);
v___x_3005_ = lean_string_hash(v_a_2997_);
v___x_3006_ = 32ULL;
v___x_3007_ = lean_uint64_shift_right(v___x_3005_, v___x_3006_);
v_fold_3008_ = lean_uint64_xor(v___x_3005_, v___x_3007_);
v___x_3009_ = 16ULL;
v___x_3010_ = lean_uint64_shift_right(v_fold_3008_, v___x_3009_);
v___x_3011_ = lean_uint64_xor(v_fold_3008_, v___x_3010_);
v___x_3012_ = lean_uint64_to_usize(v___x_3011_);
v___x_3013_ = lean_usize_of_nat(v___x_3004_);
v___x_3014_ = ((size_t)1ULL);
v___x_3015_ = lean_usize_sub(v___x_3013_, v___x_3014_);
v___x_3016_ = lean_usize_land(v___x_3012_, v___x_3015_);
v_bkt_3017_ = lean_array_uget_borrowed(v_buckets_3000_, v___x_3016_);
v___x_3018_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_2997_, v_bkt_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v_size_x27_3020_; lean_object* v___x_3021_; lean_object* v_buckets_x27_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v___x_3019_ = lean_unsigned_to_nat(1u);
v_size_x27_3020_ = lean_nat_add(v_size_2999_, v___x_3019_);
lean_dec(v_size_2999_);
lean_inc(v_bkt_3017_);
v___x_3021_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3021_, 0, v_a_2997_);
lean_ctor_set(v___x_3021_, 1, v_b_2998_);
lean_ctor_set(v___x_3021_, 2, v_bkt_3017_);
v_buckets_x27_3022_ = lean_array_uset(v_buckets_3000_, v___x_3016_, v___x_3021_);
v___x_3023_ = lean_unsigned_to_nat(4u);
v___x_3024_ = lean_nat_mul(v_size_x27_3020_, v___x_3023_);
v___x_3025_ = lean_unsigned_to_nat(3u);
v___x_3026_ = lean_nat_div(v___x_3024_, v___x_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_array_get_size(v_buckets_x27_3022_);
v___x_3028_ = lean_nat_dec_le(v___x_3026_, v___x_3027_);
lean_dec(v___x_3026_);
if (v___x_3028_ == 0)
{
lean_object* v_val_3029_; lean_object* v___x_3031_; 
v_val_3029_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_buckets_x27_3022_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 1, v_val_3029_);
lean_ctor_set(v___x_3002_, 0, v_size_x27_3020_);
v___x_3031_ = v___x_3002_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_size_x27_3020_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_val_3029_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
else
{
lean_object* v___x_3034_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 1, v_buckets_x27_3022_);
lean_ctor_set(v___x_3002_, 0, v_size_x27_3020_);
v___x_3034_ = v___x_3002_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_size_x27_3020_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_buckets_x27_3022_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
else
{
lean_object* v___x_3036_; lean_object* v_buckets_x27_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
lean_inc(v_bkt_3017_);
v___x_3036_ = lean_box(0);
v_buckets_x27_3037_ = lean_array_uset(v_buckets_3000_, v___x_3016_, v___x_3036_);
v___x_3038_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_2997_, v_b_2998_, v_bkt_3017_);
v___x_3039_ = lean_array_uset(v_buckets_x27_3037_, v___x_3016_, v___x_3038_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 1, v___x_3039_);
v___x_3041_ = v___x_3002_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_size_2999_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(lean_object* v_a_3044_, lean_object* v_x_3045_){
_start:
{
if (lean_obj_tag(v_x_3045_) == 0)
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_box(0);
return v___x_3046_;
}
else
{
lean_object* v_key_3047_; lean_object* v_value_3048_; lean_object* v_tail_3049_; uint8_t v___x_3050_; 
v_key_3047_ = lean_ctor_get(v_x_3045_, 0);
v_value_3048_ = lean_ctor_get(v_x_3045_, 1);
v_tail_3049_ = lean_ctor_get(v_x_3045_, 2);
v___x_3050_ = lean_string_dec_eq(v_key_3047_, v_a_3044_);
if (v___x_3050_ == 0)
{
v_x_3045_ = v_tail_3049_;
goto _start;
}
else
{
lean_object* v___x_3052_; 
lean_inc(v_value_3048_);
v___x_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3052_, 0, v_value_3048_);
return v___x_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg___boxed(lean_object* v_a_3053_, lean_object* v_x_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3053_, v_x_3054_);
lean_dec(v_x_3054_);
lean_dec_ref(v_a_3053_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(lean_object* v_m_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v_buckets_3058_; lean_object* v___x_3059_; uint64_t v___x_3060_; uint64_t v___x_3061_; uint64_t v___x_3062_; uint64_t v_fold_3063_; uint64_t v___x_3064_; uint64_t v___x_3065_; uint64_t v___x_3066_; size_t v___x_3067_; size_t v___x_3068_; size_t v___x_3069_; size_t v___x_3070_; size_t v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_buckets_3058_ = lean_ctor_get(v_m_3056_, 1);
v___x_3059_ = lean_array_get_size(v_buckets_3058_);
v___x_3060_ = lean_string_hash(v_a_3057_);
v___x_3061_ = 32ULL;
v___x_3062_ = lean_uint64_shift_right(v___x_3060_, v___x_3061_);
v_fold_3063_ = lean_uint64_xor(v___x_3060_, v___x_3062_);
v___x_3064_ = 16ULL;
v___x_3065_ = lean_uint64_shift_right(v_fold_3063_, v___x_3064_);
v___x_3066_ = lean_uint64_xor(v_fold_3063_, v___x_3065_);
v___x_3067_ = lean_uint64_to_usize(v___x_3066_);
v___x_3068_ = lean_usize_of_nat(v___x_3059_);
v___x_3069_ = ((size_t)1ULL);
v___x_3070_ = lean_usize_sub(v___x_3068_, v___x_3069_);
v___x_3071_ = lean_usize_land(v___x_3067_, v___x_3070_);
v___x_3072_ = lean_array_uget_borrowed(v_buckets_3058_, v___x_3071_);
v___x_3073_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_3057_, v___x_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg___boxed(lean_object* v_m_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_3074_, v_a_3075_);
lean_dec_ref(v_a_3075_);
lean_dec_ref(v_m_3074_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(lean_object* v_histogram_3077_, lean_object* v_index_3078_, lean_object* v_val_3079_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3077_, v_val_3079_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3081_ = lean_unsigned_to_nat(1u);
v___x_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3082_, 0, v_index_3078_);
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3081_);
lean_ctor_set(v___x_3085_, 1, v___x_3082_);
lean_ctor_set(v___x_3085_, 2, v___x_3083_);
lean_ctor_set(v___x_3085_, 3, v___x_3084_);
v___x_3086_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3077_, v_val_3079_, v___x_3085_);
return v___x_3086_;
}
else
{
lean_object* v_val_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3108_; 
v_val_3087_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3089_ = v___x_3080_;
v_isShared_3090_ = v_isSharedCheck_3108_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_val_3087_);
lean_dec(v___x_3080_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3108_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v_leftCount_3091_; lean_object* v_rightCount_3092_; lean_object* v_rightIndex_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3106_; 
v_leftCount_3091_ = lean_ctor_get(v_val_3087_, 0);
v_rightCount_3092_ = lean_ctor_get(v_val_3087_, 2);
v_rightIndex_3093_ = lean_ctor_get(v_val_3087_, 3);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_val_3087_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; 
v_unused_3107_ = lean_ctor_get(v_val_3087_, 1);
lean_dec(v_unused_3107_);
v___x_3095_ = v_val_3087_;
v_isShared_3096_ = v_isSharedCheck_3106_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_rightIndex_3093_);
lean_inc(v_rightCount_3092_);
lean_inc(v_leftCount_3091_);
lean_dec(v_val_3087_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3106_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3097_ = lean_unsigned_to_nat(1u);
v___x_3098_ = lean_nat_add(v_leftCount_3091_, v___x_3097_);
lean_dec(v_leftCount_3091_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v_index_3078_);
v___x_3100_ = v___x_3089_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_index_3078_);
v___x_3100_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
lean_object* v___x_3102_; 
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 1, v___x_3100_);
lean_ctor_set(v___x_3095_, 0, v___x_3098_);
v___x_3102_ = v___x_3095_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_rightCount_3092_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_rightIndex_3093_);
v___x_3102_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3077_, v_val_3079_, v___x_3102_);
return v___x_3103_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(lean_object* v_upperBound_3109_, lean_object* v_fst_3110_, lean_object* v___x_3111_, lean_object* v_fst_3112_, lean_object* v_a_3113_, lean_object* v_b_3114_){
_start:
{
uint8_t v___x_3115_; 
v___x_3115_ = lean_nat_dec_lt(v_a_3113_, v_upperBound_3109_);
if (v___x_3115_ == 0)
{
lean_dec(v_a_3113_);
return v_b_3114_;
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3116_ = l_Subarray_get___redArg(v_fst_3112_, v_a_3113_);
lean_inc(v_a_3113_);
v___x_3117_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_b_3114_, v_a_3113_, v___x_3116_);
v___x_3118_ = lean_unsigned_to_nat(1u);
v___x_3119_ = lean_nat_add(v_a_3113_, v___x_3118_);
lean_dec(v_a_3113_);
v_a_3113_ = v___x_3119_;
v_b_3114_ = v___x_3117_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_upperBound_3121_, lean_object* v_fst_3122_, lean_object* v___x_3123_, lean_object* v_fst_3124_, lean_object* v_a_3125_, lean_object* v_b_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3121_, v_fst_3122_, v___x_3123_, v_fst_3124_, v_a_3125_, v_b_3126_);
lean_dec_ref(v_fst_3124_);
lean_dec(v___x_3123_);
lean_dec_ref(v_fst_3122_);
lean_dec(v_upperBound_3121_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(lean_object* v_as_x27_3128_, lean_object* v_b_3129_){
_start:
{
if (lean_obj_tag(v_as_x27_3128_) == 0)
{
return v_b_3129_;
}
else
{
lean_object* v_head_3130_; lean_object* v_snd_3131_; lean_object* v_leftIndex_3132_; 
v_head_3130_ = lean_ctor_get(v_as_x27_3128_, 0);
v_snd_3131_ = lean_ctor_get(v_head_3130_, 1);
v_leftIndex_3132_ = lean_ctor_get(v_snd_3131_, 1);
if (lean_obj_tag(v_leftIndex_3132_) == 1)
{
lean_object* v_rightIndex_3133_; 
v_rightIndex_3133_ = lean_ctor_get(v_snd_3131_, 3);
if (lean_obj_tag(v_rightIndex_3133_) == 1)
{
if (lean_obj_tag(v_b_3129_) == 0)
{
lean_object* v_tail_3134_; lean_object* v_fst_3135_; lean_object* v_leftCount_3136_; lean_object* v_rightCount_3137_; lean_object* v_val_3138_; lean_object* v_val_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v_tail_3134_ = lean_ctor_get(v_as_x27_3128_, 1);
v_fst_3135_ = lean_ctor_get(v_head_3130_, 0);
v_leftCount_3136_ = lean_ctor_get(v_snd_3131_, 0);
v_rightCount_3137_ = lean_ctor_get(v_snd_3131_, 2);
v_val_3138_ = lean_ctor_get(v_leftIndex_3132_, 0);
v_val_3139_ = lean_ctor_get(v_rightIndex_3133_, 0);
v___x_3140_ = lean_nat_add(v_leftCount_3136_, v_rightCount_3137_);
lean_inc(v_val_3139_);
lean_inc(v_val_3138_);
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v_val_3138_);
lean_ctor_set(v___x_3141_, 1, v_val_3139_);
lean_inc(v_fst_3135_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_fst_3135_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3140_);
lean_ctor_set(v___x_3143_, 1, v___x_3142_);
v___x_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
v_as_x27_3128_ = v_tail_3134_;
v_b_3129_ = v___x_3144_;
goto _start;
}
else
{
lean_object* v_val_3146_; lean_object* v_tail_3147_; lean_object* v_fst_3148_; lean_object* v_leftCount_3149_; lean_object* v_rightCount_3150_; lean_object* v_val_3151_; lean_object* v_val_3152_; lean_object* v_fst_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3174_; 
v_val_3146_ = lean_ctor_get(v_b_3129_, 0);
lean_inc(v_val_3146_);
v_tail_3147_ = lean_ctor_get(v_as_x27_3128_, 1);
v_fst_3148_ = lean_ctor_get(v_head_3130_, 0);
v_leftCount_3149_ = lean_ctor_get(v_snd_3131_, 0);
v_rightCount_3150_ = lean_ctor_get(v_snd_3131_, 2);
v_val_3151_ = lean_ctor_get(v_leftIndex_3132_, 0);
v_val_3152_ = lean_ctor_get(v_rightIndex_3133_, 0);
v_fst_3153_ = lean_ctor_get(v_val_3146_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_val_3146_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v_val_3146_, 1);
lean_dec(v_unused_3175_);
v___x_3155_ = v_val_3146_;
v_isShared_3156_ = v_isSharedCheck_3174_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_fst_3153_);
lean_dec(v_val_3146_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3174_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3157_ = lean_nat_add(v_leftCount_3149_, v_rightCount_3150_);
v___x_3158_ = lean_nat_dec_lt(v___x_3157_, v_fst_3153_);
lean_dec(v_fst_3153_);
if (v___x_3158_ == 0)
{
lean_dec(v___x_3157_);
lean_del_object(v___x_3155_);
v_as_x27_3128_ = v_tail_3147_;
goto _start;
}
else
{
lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3172_; 
v_isSharedCheck_3172_ = !lean_is_exclusive(v_b_3129_);
if (v_isSharedCheck_3172_ == 0)
{
lean_object* v_unused_3173_; 
v_unused_3173_ = lean_ctor_get(v_b_3129_, 0);
lean_dec(v_unused_3173_);
v___x_3161_ = v_b_3129_;
v_isShared_3162_ = v_isSharedCheck_3172_;
goto v_resetjp_3160_;
}
else
{
lean_dec(v_b_3129_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3172_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
lean_inc(v_val_3152_);
lean_inc(v_val_3151_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 1, v_val_3152_);
lean_ctor_set(v___x_3155_, 0, v_val_3151_);
v___x_3164_ = v___x_3155_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_val_3151_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_val_3152_);
v___x_3164_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
lean_inc(v_fst_3148_);
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v_fst_3148_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3157_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3166_);
v___x_3168_ = v___x_3161_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
v_as_x27_3128_ = v_tail_3147_;
v_b_3129_ = v___x_3168_;
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
lean_object* v_tail_3176_; 
v_tail_3176_ = lean_ctor_get(v_as_x27_3128_, 1);
v_as_x27_3128_ = v_tail_3176_;
goto _start;
}
}
else
{
lean_object* v_tail_3178_; 
v_tail_3178_ = lean_ctor_get(v_as_x27_3128_, 1);
v_as_x27_3128_ = v_tail_3178_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg___boxed(lean_object* v_as_x27_3180_, lean_object* v_b_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3180_, v_b_3181_);
lean_dec(v_as_x27_3180_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(lean_object* v_histogram_3183_, lean_object* v_index_3184_, lean_object* v_val_3185_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_histogram_3183_, v_val_3185_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3187_ = lean_unsigned_to_nat(0u);
v___x_3188_ = lean_box(0);
v___x_3189_ = lean_unsigned_to_nat(1u);
v___x_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3190_, 0, v_index_3184_);
v___x_3191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3187_);
lean_ctor_set(v___x_3191_, 1, v___x_3188_);
lean_ctor_set(v___x_3191_, 2, v___x_3189_);
lean_ctor_set(v___x_3191_, 3, v___x_3190_);
v___x_3192_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3183_, v_val_3185_, v___x_3191_);
return v___x_3192_;
}
else
{
lean_object* v_val_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3214_; 
v_val_3193_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3195_ = v___x_3186_;
v_isShared_3196_ = v_isSharedCheck_3214_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_val_3193_);
lean_dec(v___x_3186_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3214_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_leftCount_3197_; lean_object* v_leftIndex_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3211_; 
v_leftCount_3197_ = lean_ctor_get(v_val_3193_, 0);
v_leftIndex_3198_ = lean_ctor_get(v_val_3193_, 1);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_val_3193_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; lean_object* v_unused_3213_; 
v_unused_3212_ = lean_ctor_get(v_val_3193_, 3);
lean_dec(v_unused_3212_);
v_unused_3213_ = lean_ctor_get(v_val_3193_, 2);
lean_dec(v_unused_3213_);
v___x_3200_ = v_val_3193_;
v_isShared_3201_ = v_isSharedCheck_3211_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_leftIndex_3198_);
lean_inc(v_leftCount_3197_);
lean_dec(v_val_3193_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3211_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3202_ = lean_unsigned_to_nat(1u);
v___x_3203_ = lean_nat_add(v_leftCount_3197_, v___x_3202_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v_index_3184_);
v___x_3205_ = v___x_3195_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_index_3184_);
v___x_3205_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3207_; 
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 3, v___x_3205_);
lean_ctor_set(v___x_3200_, 2, v___x_3203_);
v___x_3207_ = v___x_3200_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_leftCount_3197_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v_leftIndex_3198_);
lean_ctor_set(v_reuseFailAlloc_3209_, 2, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3209_, 3, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_histogram_3183_, v_val_3185_, v___x_3207_);
return v___x_3208_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(lean_object* v_upperBound_3215_, lean_object* v___x_3216_, lean_object* v_fst_3217_, lean_object* v___x_3218_, lean_object* v_a_3219_, lean_object* v_b_3220_){
_start:
{
uint8_t v___x_3221_; 
v___x_3221_ = lean_nat_dec_lt(v_a_3219_, v_upperBound_3215_);
if (v___x_3221_ == 0)
{
lean_dec(v_a_3219_);
return v_b_3220_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3222_ = l_Subarray_get___redArg(v_fst_3217_, v_a_3219_);
lean_inc(v_a_3219_);
v___x_3223_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_b_3220_, v_a_3219_, v___x_3222_);
v___x_3224_ = lean_unsigned_to_nat(1u);
v___x_3225_ = lean_nat_add(v_a_3219_, v___x_3224_);
lean_dec(v_a_3219_);
v_a_3219_ = v___x_3225_;
v_b_3220_ = v___x_3223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg___boxed(lean_object* v_upperBound_3227_, lean_object* v___x_3228_, lean_object* v_fst_3229_, lean_object* v___x_3230_, lean_object* v_a_3231_, lean_object* v_b_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3227_, v___x_3228_, v_fst_3229_, v___x_3230_, v_a_3231_, v_b_3232_);
lean_dec(v___x_3230_);
lean_dec_ref(v_fst_3229_);
lean_dec(v___x_3228_);
lean_dec(v_upperBound_3227_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(lean_object* v_a_3234_, lean_object* v_b_3235_){
_start:
{
lean_object* v_array_3236_; lean_object* v_start_3237_; lean_object* v_stop_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3251_; 
v_array_3236_ = lean_ctor_get(v_a_3234_, 0);
v_start_3237_ = lean_ctor_get(v_a_3234_, 1);
v_stop_3238_ = lean_ctor_get(v_a_3234_, 2);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_a_3234_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3240_ = v_a_3234_;
v_isShared_3241_ = v_isSharedCheck_3251_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_stop_3238_);
lean_inc(v_start_3237_);
lean_inc(v_array_3236_);
lean_dec(v_a_3234_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3251_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
uint8_t v___x_3242_; 
v___x_3242_ = lean_nat_dec_lt(v_start_3237_, v_stop_3238_);
if (v___x_3242_ == 0)
{
lean_del_object(v___x_3240_);
lean_dec(v_stop_3238_);
lean_dec(v_start_3237_);
lean_dec_ref(v_array_3236_);
return v_b_3235_;
}
else
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3243_ = lean_unsigned_to_nat(1u);
v___x_3244_ = lean_nat_add(v_start_3237_, v___x_3243_);
lean_inc_ref(v_array_3236_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 1, v___x_3244_);
v___x_3246_ = v___x_3240_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_array_3236_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3250_, 2, v_stop_3238_);
v___x_3246_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = lean_array_fget(v_array_3236_, v_start_3237_);
lean_dec(v_start_3237_);
lean_dec_ref(v_array_3236_);
v___x_3248_ = lean_array_push(v_b_3235_, v___x_3247_);
v_a_3234_ = v___x_3246_;
v_b_3235_ = v___x_3248_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(lean_object* v_left_3252_, lean_object* v_right_3253_, lean_object* v_i_3254_){
_start:
{
lean_object* v_start_3255_; lean_object* v_stop_3256_; lean_object* v___x_3257_; uint8_t v___x_3271_; 
v_start_3255_ = lean_ctor_get(v_left_3252_, 1);
v_stop_3256_ = lean_ctor_get(v_left_3252_, 2);
v___x_3257_ = lean_nat_sub(v_stop_3256_, v_start_3255_);
v___x_3271_ = lean_nat_dec_lt(v_i_3254_, v___x_3257_);
if (v___x_3271_ == 0)
{
goto v___jp_3258_;
}
else
{
lean_object* v_start_3272_; lean_object* v_stop_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; 
v_start_3272_ = lean_ctor_get(v_right_3253_, 1);
v_stop_3273_ = lean_ctor_get(v_right_3253_, 2);
v___x_3274_ = lean_nat_sub(v_stop_3273_, v_start_3272_);
v___x_3275_ = lean_nat_dec_lt(v_i_3254_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_dec(v___x_3274_);
goto v___jp_3258_;
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3276_ = lean_nat_sub(v___x_3257_, v_i_3254_);
lean_dec(v___x_3257_);
v___x_3277_ = lean_unsigned_to_nat(1u);
v___x_3278_ = lean_nat_sub(v___x_3276_, v___x_3277_);
v___x_3279_ = l_Subarray_get___redArg(v_left_3252_, v___x_3278_);
lean_dec(v___x_3278_);
v___x_3280_ = lean_nat_sub(v___x_3274_, v_i_3254_);
lean_dec(v___x_3274_);
v___x_3281_ = lean_nat_sub(v___x_3280_, v___x_3277_);
v___x_3282_ = l_Subarray_get___redArg(v_right_3253_, v___x_3281_);
lean_dec(v___x_3281_);
v___x_3283_ = lean_string_dec_eq(v___x_3279_, v___x_3282_);
lean_dec(v___x_3282_);
lean_dec(v___x_3279_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec(v_i_3254_);
lean_inc_ref(v_left_3252_);
v___x_3284_ = l_Subarray_take___redArg(v_left_3252_, v___x_3276_);
v___x_3285_ = l_Subarray_take___redArg(v_right_3253_, v___x_3280_);
lean_dec(v___x_3280_);
v___x_3286_ = l_Subarray_drop___redArg(v_left_3252_, v___x_3276_);
lean_dec(v___x_3276_);
v___x_3287_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3288_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3286_, v___x_3287_);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3285_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3284_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
return v___x_3290_;
}
else
{
lean_object* v___x_3291_; 
lean_dec(v___x_3280_);
lean_dec(v___x_3276_);
v___x_3291_ = lean_nat_add(v_i_3254_, v___x_3277_);
lean_dec(v_i_3254_);
v_i_3254_ = v___x_3291_;
goto _start;
}
}
}
v___jp_3258_:
{
lean_object* v_start_3259_; lean_object* v_stop_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v_start_3259_ = lean_ctor_get(v_right_3253_, 1);
v_stop_3260_ = lean_ctor_get(v_right_3253_, 2);
v___x_3261_ = lean_nat_sub(v___x_3257_, v_i_3254_);
lean_dec(v___x_3257_);
lean_inc_ref(v_left_3252_);
v___x_3262_ = l_Subarray_take___redArg(v_left_3252_, v___x_3261_);
v___x_3263_ = lean_nat_sub(v_stop_3260_, v_start_3259_);
v___x_3264_ = lean_nat_sub(v___x_3263_, v_i_3254_);
lean_dec(v_i_3254_);
lean_dec(v___x_3263_);
v___x_3265_ = l_Subarray_take___redArg(v_right_3253_, v___x_3264_);
lean_dec(v___x_3264_);
v___x_3266_ = l_Subarray_drop___redArg(v_left_3252_, v___x_3261_);
lean_dec(v___x_3261_);
v___x_3267_ = ((lean_object*)(l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14___closed__0));
v___x_3268_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v___x_3266_, v___x_3267_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3265_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3262_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
return v___x_3270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(lean_object* v_left_3293_, lean_object* v_right_3294_){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = lean_unsigned_to_nat(0u);
v___x_3296_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20(v_left_3293_, v_right_3294_, v___x_3295_);
return v___x_3296_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = lean_box(0);
v___x_3298_ = lean_unsigned_to_nat(16u);
v___x_3299_ = lean_mk_array(v___x_3298_, v___x_3297_);
return v___x_3299_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v_hist_3302_; 
v___x_3300_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__0);
v___x_3301_ = lean_unsigned_to_nat(0u);
v_hist_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_3302_, 0, v___x_3301_);
lean_ctor_set(v_hist_3302_, 1, v___x_3300_);
return v_hist_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(lean_object* v_left_3303_, lean_object* v_right_3304_){
_start:
{
lean_object* v___x_3305_; lean_object* v_snd_3306_; lean_object* v_fst_3307_; lean_object* v_fst_3308_; lean_object* v_snd_3309_; lean_object* v___x_3310_; lean_object* v_snd_3311_; lean_object* v_fst_3312_; lean_object* v_fst_3313_; lean_object* v_snd_3314_; lean_object* v_start_3315_; lean_object* v_stop_3316_; lean_object* v___x_3317_; lean_object* v_hist_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v_start_3321_; lean_object* v_stop_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v_buckets_3325_; lean_object* v___x_3326_; lean_object* v___y_3328_; lean_object* v___x_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v___x_3305_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__14(v_left_3303_, v_right_3304_);
v_snd_3306_ = lean_ctor_get(v___x_3305_, 1);
lean_inc(v_snd_3306_);
v_fst_3307_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_fst_3307_);
lean_dec_ref(v___x_3305_);
v_fst_3308_ = lean_ctor_get(v_snd_3306_, 0);
lean_inc(v_fst_3308_);
v_snd_3309_ = lean_ctor_get(v_snd_3306_, 1);
lean_inc(v_snd_3309_);
lean_dec(v_snd_3306_);
v___x_3310_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15(v_fst_3308_, v_snd_3309_);
v_snd_3311_ = lean_ctor_get(v___x_3310_, 1);
lean_inc(v_snd_3311_);
v_fst_3312_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_fst_3312_);
lean_dec_ref(v___x_3310_);
v_fst_3313_ = lean_ctor_get(v_snd_3311_, 0);
lean_inc(v_fst_3313_);
v_snd_3314_ = lean_ctor_get(v_snd_3311_, 1);
lean_inc(v_snd_3314_);
lean_dec(v_snd_3311_);
v_start_3315_ = lean_ctor_get(v_fst_3312_, 1);
v_stop_3316_ = lean_ctor_get(v_fst_3312_, 2);
v___x_3317_ = lean_unsigned_to_nat(0u);
v_hist_3318_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12___closed__1);
v___x_3319_ = lean_nat_sub(v_stop_3316_, v_start_3315_);
v___x_3320_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v___x_3319_, v_fst_3313_, v___x_3319_, v_fst_3312_, v___x_3317_, v_hist_3318_);
v_start_3321_ = lean_ctor_get(v_fst_3313_, 1);
v_stop_3322_ = lean_ctor_get(v_fst_3313_, 2);
v___x_3323_ = lean_nat_sub(v_stop_3322_, v_start_3321_);
v___x_3324_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v___x_3323_, v___x_3323_, v_fst_3313_, v___x_3319_, v___x_3317_, v___x_3320_);
lean_dec(v___x_3319_);
lean_dec(v___x_3323_);
v_buckets_3325_ = lean_ctor_get(v___x_3324_, 1);
lean_inc_ref(v_buckets_3325_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = lean_box(0);
v___x_3354_ = lean_box(0);
v___x_3355_ = lean_array_get_size(v_buckets_3325_);
v___x_3356_ = lean_nat_dec_lt(v___x_3317_, v___x_3355_);
if (v___x_3356_ == 0)
{
lean_dec_ref(v_buckets_3325_);
v___y_3328_ = v___x_3354_;
goto v___jp_3327_;
}
else
{
size_t v___x_3357_; size_t v___x_3358_; lean_object* v___x_3359_; 
v___x_3357_ = lean_usize_of_nat(v___x_3355_);
v___x_3358_ = ((size_t)0ULL);
v___x_3359_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__18(v_buckets_3325_, v___x_3357_, v___x_3358_, v___x_3354_);
lean_dec_ref(v_buckets_3325_);
v___y_3328_ = v___x_3359_;
goto v___jp_3327_;
}
v___jp_3327_:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v___y_3328_, v___x_3326_);
lean_dec(v___y_3328_);
if (lean_obj_tag(v___x_3329_) == 1)
{
lean_object* v_val_3330_; lean_object* v_snd_3331_; lean_object* v_snd_3332_; lean_object* v_fst_3333_; lean_object* v_fst_3334_; lean_object* v_snd_3335_; lean_object* v___x_3336_; lean_object* v_fst_3337_; lean_object* v_snd_3338_; lean_object* v___x_3339_; lean_object* v_fst_3340_; lean_object* v_snd_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_val_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_val_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v_snd_3331_ = lean_ctor_get(v_val_3330_, 1);
lean_inc(v_snd_3331_);
lean_dec(v_val_3330_);
v_snd_3332_ = lean_ctor_get(v_snd_3331_, 1);
lean_inc(v_snd_3332_);
v_fst_3333_ = lean_ctor_get(v_snd_3331_, 0);
lean_inc(v_fst_3333_);
lean_dec(v_snd_3331_);
v_fst_3334_ = lean_ctor_get(v_snd_3332_, 0);
lean_inc(v_fst_3334_);
v_snd_3335_ = lean_ctor_get(v_snd_3332_, 1);
lean_inc(v_snd_3335_);
lean_dec(v_snd_3332_);
v___x_3336_ = l_Subarray_split___redArg(v_fst_3312_, v_fst_3334_);
lean_dec(v_fst_3334_);
v_fst_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_fst_3337_);
v_snd_3338_ = lean_ctor_get(v___x_3336_, 1);
lean_inc(v_snd_3338_);
lean_dec_ref(v___x_3336_);
v___x_3339_ = l_Subarray_split___redArg(v_fst_3313_, v_snd_3335_);
lean_dec(v_snd_3335_);
v_fst_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_fst_3340_);
v_snd_3341_ = lean_ctor_get(v___x_3339_, 1);
lean_inc(v_snd_3341_);
lean_dec_ref(v___x_3339_);
v___x_3342_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v_fst_3337_, v_fst_3340_);
v___x_3343_ = l_Array_append___redArg(v_fst_3307_, v___x_3342_);
lean_dec_ref(v___x_3342_);
v___x_3344_ = lean_unsigned_to_nat(1u);
v___x_3345_ = lean_mk_empty_array_with_capacity(v___x_3344_);
v___x_3346_ = lean_array_push(v___x_3345_, v_fst_3333_);
v___x_3347_ = l_Array_append___redArg(v___x_3343_, v___x_3346_);
lean_dec_ref(v___x_3346_);
v___x_3348_ = l_Subarray_drop___redArg(v_snd_3338_, v___x_3344_);
v___x_3349_ = l_Subarray_drop___redArg(v_snd_3341_, v___x_3344_);
v___x_3350_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3348_, v___x_3349_);
v___x_3351_ = l_Array_append___redArg(v___x_3347_, v___x_3350_);
lean_dec_ref(v___x_3350_);
v___x_3352_ = l_Array_append___redArg(v___x_3351_, v_snd_3314_);
lean_dec(v_snd_3314_);
return v___x_3352_;
}
else
{
lean_object* v___x_3353_; 
lean_dec(v___x_3329_);
lean_dec(v_fst_3313_);
lean_dec(v_fst_3312_);
v___x_3353_ = l_Array_append___redArg(v_fst_3307_, v_snd_3314_);
lean_dec(v_snd_3314_);
return v___x_3353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(size_t v_sz_3360_, size_t v_i_3361_, lean_object* v_bs_3362_){
_start:
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_usize_dec_lt(v_i_3361_, v_sz_3360_);
if (v___x_3363_ == 0)
{
return v_bs_3362_;
}
else
{
lean_object* v_v_3364_; lean_object* v___x_3365_; lean_object* v_bs_x27_3366_; uint8_t v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; size_t v___x_3370_; size_t v___x_3371_; lean_object* v___x_3372_; 
v_v_3364_ = lean_array_uget(v_bs_3362_, v_i_3361_);
v___x_3365_ = lean_unsigned_to_nat(0u);
v_bs_x27_3366_ = lean_array_uset(v_bs_3362_, v_i_3361_, v___x_3365_);
v___x_3367_ = 1;
v___x_3368_ = lean_box(v___x_3367_);
v___x_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
lean_ctor_set(v___x_3369_, 1, v_v_3364_);
v___x_3370_ = ((size_t)1ULL);
v___x_3371_ = lean_usize_add(v_i_3361_, v___x_3370_);
v___x_3372_ = lean_array_uset(v_bs_x27_3366_, v_i_3361_, v___x_3369_);
v_i_3361_ = v___x_3371_;
v_bs_3362_ = v___x_3372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16___boxed(lean_object* v_sz_3374_, lean_object* v_i_3375_, lean_object* v_bs_3376_){
_start:
{
size_t v_sz_boxed_3377_; size_t v_i_boxed_3378_; lean_object* v_res_3379_; 
v_sz_boxed_3377_ = lean_unbox_usize(v_sz_3374_);
lean_dec(v_sz_3374_);
v_i_boxed_3378_ = lean_unbox_usize(v_i_3375_);
lean_dec(v_i_3375_);
v_res_3379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_boxed_3377_, v_i_boxed_3378_, v_bs_3376_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(lean_object* v_original_3387_, lean_object* v_edited_3388_){
_start:
{
lean_object* v_i_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v_i_3389_ = lean_unsigned_to_nat(0u);
v___x_3390_ = lean_array_get_size(v_original_3387_);
v___x_3391_ = lean_nat_dec_lt(v_i_3389_, v___x_3390_);
if (v___x_3391_ == 0)
{
size_t v_sz_3392_; size_t v___x_3393_; lean_object* v___x_3394_; 
lean_dec_ref(v_original_3387_);
v_sz_3392_ = lean_array_size(v_edited_3388_);
v___x_3393_ = ((size_t)0ULL);
v___x_3394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__17(v_sz_3392_, v___x_3393_, v_edited_3388_);
return v___x_3394_;
}
else
{
lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3395_ = lean_array_get_size(v_edited_3388_);
v___x_3396_ = lean_nat_dec_lt(v_i_3389_, v___x_3395_);
if (v___x_3396_ == 0)
{
size_t v_sz_3397_; size_t v___x_3398_; lean_object* v___x_3399_; 
lean_dec_ref(v_edited_3388_);
v_sz_3397_ = lean_array_size(v_original_3387_);
v___x_3398_ = ((size_t)0ULL);
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__16(v_sz_3397_, v___x_3398_, v_original_3387_);
return v___x_3399_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v_ds_3402_; lean_object* v___x_3403_; size_t v_sz_3404_; size_t v___x_3405_; lean_object* v___x_3406_; lean_object* v_snd_3407_; lean_object* v_fst_3408_; lean_object* v_fst_3409_; lean_object* v_snd_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3429_; 
lean_inc_ref(v_original_3387_);
v___x_3400_ = l_Array_toSubarray___redArg(v_original_3387_, v_i_3389_, v___x_3390_);
lean_inc_ref(v_edited_3388_);
v___x_3401_ = l_Array_toSubarray___redArg(v_edited_3388_, v_i_3389_, v___x_3395_);
v_ds_3402_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12(v___x_3400_, v___x_3401_);
v___x_3403_ = ((lean_object*)(l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7___closed__2));
v_sz_3404_ = lean_array_size(v_ds_3402_);
v___x_3405_ = ((size_t)0ULL);
v___x_3406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__13(v___x_3395_, v_edited_3388_, v___x_3390_, v_original_3387_, v_ds_3402_, v_sz_3404_, v___x_3405_, v___x_3403_);
lean_dec_ref(v_ds_3402_);
v_snd_3407_ = lean_ctor_get(v___x_3406_, 1);
lean_inc(v_snd_3407_);
v_fst_3408_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_fst_3408_);
lean_dec_ref(v___x_3406_);
v_fst_3409_ = lean_ctor_get(v_snd_3407_, 0);
v_snd_3410_ = lean_ctor_get(v_snd_3407_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_snd_3407_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3412_ = v_snd_3407_;
v_isShared_3413_ = v_isSharedCheck_3429_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_snd_3410_);
lean_inc(v_fst_3409_);
lean_dec(v_snd_3407_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3429_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 1, v_fst_3409_);
lean_ctor_set(v___x_3412_, 0, v_fst_3408_);
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_fst_3408_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_fst_3409_);
v___x_3415_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3416_; lean_object* v_fst_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3426_; 
v___x_3416_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3390_, v_original_3387_, v___x_3415_);
lean_dec_ref(v_original_3387_);
v_fst_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; 
v_unused_3427_ = lean_ctor_get(v___x_3416_, 1);
lean_dec(v_unused_3427_);
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3426_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_fst_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3426_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 1, v_snd_3410_);
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_fst_3417_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_snd_3410_);
v___x_3422_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; lean_object* v_fst_3424_; 
v___x_3423_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3395_, v_edited_3388_, v___x_3422_);
lean_dec_ref(v_edited_3388_);
v_fst_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_fst_3424_);
lean_dec_ref(v___x_3423_);
return v_fst_3424_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(lean_object* v___y_3430_, lean_object* v_x_3431_, lean_object* v_x_3432_){
_start:
{
if (lean_obj_tag(v_x_3431_) == 0)
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = l_List_reverse___redArg(v_x_3432_);
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
return v___x_3435_;
}
else
{
lean_object* v_head_3436_; lean_object* v_tail_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3446_; 
v_head_3436_ = lean_ctor_get(v_x_3431_, 0);
v_tail_3437_ = lean_ctor_get(v_x_3431_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_x_3431_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3439_ = v_x_3431_;
v_isShared_3440_ = v_isSharedCheck_3446_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_tail_3437_);
lean_inc(v_head_3436_);
lean_dec(v_x_3431_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3446_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3441_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString(v_head_3436_, v___y_3430_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v_x_3432_);
lean_ctor_set(v___x_3439_, 0, v___x_3441_);
v___x_3443_ = v___x_3439_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v_x_3432_);
v___x_3443_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
v_x_3431_ = v_tail_3437_;
v_x_3432_ = v___x_3443_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg___boxed(lean_object* v___y_3447_, lean_object* v_x_3448_, lean_object* v_x_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3447_, v_x_3448_, v_x_3449_);
lean_dec(v___y_3447_);
return v_res_3451_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3(void){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__2));
v___x_3458_ = l_Lean_stringToMessageData(v___x_3457_);
return v___x_3458_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5(void){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = l_Lean_MessageLog_empty;
v___x_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(lean_object* v_x_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3472_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
lean_inc(v_x_3468_);
v___x_3473_ = l_Lean_Syntax_isOfKind(v_x_3468_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; 
lean_dec(v_x_3468_);
v___x_3474_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3474_;
}
else
{
lean_object* v___x_3475_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; uint8_t v___y_3516_; uint8_t v___y_3581_; lean_object* v___y_3582_; uint8_t v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; uint8_t v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v_dc_x3f_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___x_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; 
v___x_3475_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_3724_ = lean_unsigned_to_nat(0u);
v___x_3725_ = l_Lean_Syntax_getArg(v_x_3468_, v___x_3724_);
v___x_3726_ = l_Lean_Syntax_isNone(v___x_3725_);
if (v___x_3726_ == 0)
{
lean_object* v___x_3727_; uint8_t v___x_3728_; 
v___x_3727_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3725_);
v___x_3728_ = l_Lean_Syntax_matchesNull(v___x_3725_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
lean_dec(v___x_3725_);
lean_dec(v_x_3468_);
v___x_3729_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3729_;
}
else
{
lean_object* v_dc_x3f_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; 
v_dc_x3f_3730_ = l_Lean_Syntax_getArg(v___x_3725_, v___x_3724_);
lean_dec(v___x_3725_);
v___x_3731_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__7));
lean_inc(v_dc_x3f_3730_);
v___x_3732_ = l_Lean_Syntax_isOfKind(v_dc_x3f_3730_, v___x_3731_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; 
lean_dec(v_dc_x3f_3730_);
lean_dec(v_x_3468_);
v___x_3733_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_3733_;
}
else
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3734_, 0, v_dc_x3f_3730_);
v_dc_x3f_3705_ = v___x_3734_;
v___y_3706_ = v_a_3469_;
v___y_3707_ = v_a_3470_;
goto v___jp_3704_;
}
}
}
else
{
lean_object* v___x_3735_; 
lean_dec(v___x_3725_);
v___x_3735_ = lean_box(0);
v_dc_x3f_3705_ = v___x_3735_;
v___y_3706_ = v_a_3469_;
v___y_3707_ = v_a_3470_;
goto v___jp_3704_;
}
v___jp_3476_:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3482_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__3);
v___x_3483_ = l_Lean_stringToMessageData(v___y_3481_);
v___x_3484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3482_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = l_Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2(v___y_3477_, v___x_3484_, v___y_3480_, v___y_3478_);
lean_dec(v___y_3477_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3505_; 
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3505_ == 0)
{
lean_object* v_unused_3506_; 
v_unused_3506_ = lean_ctor_get(v___x_3485_, 0);
lean_dec(v_unused_3506_);
v___x_3487_ = v___x_3485_;
v_isShared_3488_ = v_isSharedCheck_3505_;
goto v_resetjp_3486_;
}
else
{
lean_dec(v___x_3485_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3505_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_Elab_Command_getRef___redArg(v___y_3480_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3494_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3475_);
lean_ctor_set(v___x_3491_, 1, v___y_3479_);
v___x_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3492_, 0, v_a_3490_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set_tag(v___x_3487_, 10);
lean_ctor_set(v___x_3487_, 0, v___x_3492_);
v___x_3494_ = v___x_3487_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3(v___x_3494_, v___y_3480_, v___y_3478_);
return v___x_3495_;
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_del_object(v___x_3487_);
lean_dec_ref(v___y_3479_);
v_a_3497_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3489_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3489_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3479_);
return v___x_3485_;
}
}
v___jp_3507_:
{
if (v___y_3516_ == 0)
{
lean_object* v___x_3517_; lean_object* v_env_3518_; lean_object* v_scopes_3519_; lean_object* v_usedQuotCtxts_3520_; lean_object* v_nextMacroScope_3521_; lean_object* v_maxRecDepth_3522_; lean_object* v_ngen_3523_; lean_object* v_auxDeclNGen_3524_; lean_object* v_infoState_3525_; lean_object* v_traceState_3526_; lean_object* v_snapshotTasks_3527_; lean_object* v_prevLinterStates_3528_; lean_object* v_codeQualityEntryTasks_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3554_; 
lean_dec(v___y_3509_);
v___x_3517_ = lean_st_ref_take(v___y_3510_);
v_env_3518_ = lean_ctor_get(v___x_3517_, 0);
v_scopes_3519_ = lean_ctor_get(v___x_3517_, 2);
v_usedQuotCtxts_3520_ = lean_ctor_get(v___x_3517_, 3);
v_nextMacroScope_3521_ = lean_ctor_get(v___x_3517_, 4);
v_maxRecDepth_3522_ = lean_ctor_get(v___x_3517_, 5);
v_ngen_3523_ = lean_ctor_get(v___x_3517_, 6);
v_auxDeclNGen_3524_ = lean_ctor_get(v___x_3517_, 7);
v_infoState_3525_ = lean_ctor_get(v___x_3517_, 8);
v_traceState_3526_ = lean_ctor_get(v___x_3517_, 9);
v_snapshotTasks_3527_ = lean_ctor_get(v___x_3517_, 10);
v_prevLinterStates_3528_ = lean_ctor_get(v___x_3517_, 11);
v_codeQualityEntryTasks_3529_ = lean_ctor_get(v___x_3517_, 12);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3554_ == 0)
{
lean_object* v_unused_3555_; 
v_unused_3555_ = lean_ctor_get(v___x_3517_, 1);
lean_dec(v_unused_3555_);
v___x_3531_ = v___x_3517_;
v_isShared_3532_ = v_isSharedCheck_3554_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3529_);
lean_inc(v_prevLinterStates_3528_);
lean_inc(v_snapshotTasks_3527_);
lean_inc(v_traceState_3526_);
lean_inc(v_infoState_3525_);
lean_inc(v_auxDeclNGen_3524_);
lean_inc(v_ngen_3523_);
lean_inc(v_maxRecDepth_3522_);
lean_inc(v_nextMacroScope_3521_);
lean_inc(v_usedQuotCtxts_3520_);
lean_inc(v_scopes_3519_);
lean_inc(v_env_3518_);
lean_dec(v___x_3517_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3554_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 1, v___y_3514_);
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_env_3518_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v___y_3514_);
lean_ctor_set(v_reuseFailAlloc_3553_, 2, v_scopes_3519_);
lean_ctor_set(v_reuseFailAlloc_3553_, 3, v_usedQuotCtxts_3520_);
lean_ctor_set(v_reuseFailAlloc_3553_, 4, v_nextMacroScope_3521_);
lean_ctor_set(v_reuseFailAlloc_3553_, 5, v_maxRecDepth_3522_);
lean_ctor_set(v_reuseFailAlloc_3553_, 6, v_ngen_3523_);
lean_ctor_set(v_reuseFailAlloc_3553_, 7, v_auxDeclNGen_3524_);
lean_ctor_set(v_reuseFailAlloc_3553_, 8, v_infoState_3525_);
lean_ctor_set(v_reuseFailAlloc_3553_, 9, v_traceState_3526_);
lean_ctor_set(v_reuseFailAlloc_3553_, 10, v_snapshotTasks_3527_);
lean_ctor_set(v_reuseFailAlloc_3553_, 11, v_prevLinterStates_3528_);
lean_ctor_set(v_reuseFailAlloc_3553_, 12, v_codeQualityEntryTasks_3529_);
v___x_3534_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v_scopes_3538_; lean_object* v___x_3539_; lean_object* v_opts_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3535_ = lean_st_ref_put(v___y_3510_, v___x_3534_);
v___x_3536_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3537_ = lean_st_ref_get(v___y_3510_);
v_scopes_3538_ = lean_ctor_get(v___x_3537_, 2);
lean_inc(v_scopes_3538_);
lean_dec(v___x_3537_);
v___x_3539_ = l_List_head_x21___redArg(v___x_3536_, v_scopes_3538_);
lean_dec(v_scopes_3538_);
v_opts_3540_ = lean_ctor_get(v___x_3539_, 1);
lean_inc_ref(v_opts_3540_);
lean_dec(v___x_3539_);
v___x_3541_ = l_Lean_guard__msgs_diff;
v___x_3542_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__4(v_opts_3540_, v___x_3541_);
lean_dec_ref(v_opts_3540_);
if (v___x_3542_ == 0)
{
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_inc_ref(v___y_3513_);
v___y_3477_ = v___y_3508_;
v___y_3478_ = v___y_3510_;
v___y_3479_ = v___y_3513_;
v___y_3480_ = v___y_3515_;
v___y_3481_ = v___y_3513_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3543_ = lean_string_utf8_byte_size(v___y_3512_);
lean_inc(v___y_3511_);
lean_inc_ref(v___y_3512_);
v___x_3544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3544_, 0, v___y_3512_);
lean_ctor_set(v___x_3544_, 1, v___y_3511_);
lean_ctor_set(v___x_3544_, 2, v___x_3543_);
v___x_3545_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__5___closed__0);
v___x_3546_ = lean_mk_empty_array_with_capacity(v___y_3511_);
lean_inc_ref(v___x_3546_);
v___x_3547_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3512_, v___x_3544_, v___x_3543_, v___x_3545_, v___x_3546_);
lean_dec_ref_known(v___x_3544_, 3);
v___x_3548_ = lean_string_utf8_byte_size(v___y_3513_);
lean_inc_ref_n(v___y_3513_, 2);
v___x_3549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3549_, 0, v___y_3513_);
lean_ctor_set(v___x_3549_, 1, v___y_3511_);
lean_ctor_set(v___x_3549_, 2, v___x_3548_);
v___x_3550_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___y_3513_, v___x_3549_, v___x_3548_, v___x_3545_, v___x_3546_);
lean_dec_ref_known(v___x_3549_, 3);
v___x_3551_ = l_Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7(v___x_3547_, v___x_3550_);
v___x_3552_ = l_Lean_Diff_linesToString___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__8(v___x_3551_);
lean_dec_ref(v___x_3551_);
v___y_3477_ = v___y_3508_;
v___y_3478_ = v___y_3510_;
v___y_3479_ = v___y_3513_;
v___y_3480_ = v___y_3515_;
v___y_3481_ = v___x_3552_;
goto v___jp_3476_;
}
}
}
}
else
{
lean_object* v___x_3556_; lean_object* v_env_3557_; lean_object* v_scopes_3558_; lean_object* v_usedQuotCtxts_3559_; lean_object* v_nextMacroScope_3560_; lean_object* v_maxRecDepth_3561_; lean_object* v_ngen_3562_; lean_object* v_auxDeclNGen_3563_; lean_object* v_infoState_3564_; lean_object* v_traceState_3565_; lean_object* v_snapshotTasks_3566_; lean_object* v_prevLinterStates_3567_; lean_object* v_codeQualityEntryTasks_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3578_; 
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec(v___y_3508_);
v___x_3556_ = lean_st_ref_take(v___y_3510_);
v_env_3557_ = lean_ctor_get(v___x_3556_, 0);
v_scopes_3558_ = lean_ctor_get(v___x_3556_, 2);
v_usedQuotCtxts_3559_ = lean_ctor_get(v___x_3556_, 3);
v_nextMacroScope_3560_ = lean_ctor_get(v___x_3556_, 4);
v_maxRecDepth_3561_ = lean_ctor_get(v___x_3556_, 5);
v_ngen_3562_ = lean_ctor_get(v___x_3556_, 6);
v_auxDeclNGen_3563_ = lean_ctor_get(v___x_3556_, 7);
v_infoState_3564_ = lean_ctor_get(v___x_3556_, 8);
v_traceState_3565_ = lean_ctor_get(v___x_3556_, 9);
v_snapshotTasks_3566_ = lean_ctor_get(v___x_3556_, 10);
v_prevLinterStates_3567_ = lean_ctor_get(v___x_3556_, 11);
v_codeQualityEntryTasks_3568_ = lean_ctor_get(v___x_3556_, 12);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3578_ == 0)
{
lean_object* v_unused_3579_; 
v_unused_3579_ = lean_ctor_get(v___x_3556_, 1);
lean_dec(v_unused_3579_);
v___x_3570_ = v___x_3556_;
v_isShared_3571_ = v_isSharedCheck_3578_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3568_);
lean_inc(v_prevLinterStates_3567_);
lean_inc(v_snapshotTasks_3566_);
lean_inc(v_traceState_3565_);
lean_inc(v_infoState_3564_);
lean_inc(v_auxDeclNGen_3563_);
lean_inc(v_ngen_3562_);
lean_inc(v_maxRecDepth_3561_);
lean_inc(v_nextMacroScope_3560_);
lean_inc(v_usedQuotCtxts_3559_);
lean_inc(v_scopes_3558_);
lean_inc(v_env_3557_);
lean_dec(v___x_3556_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3578_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3572_ = lean_box(0);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 1, v___y_3509_);
v___x_3574_ = v___x_3570_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_env_3557_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v___y_3509_);
lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_scopes_3558_);
lean_ctor_set(v_reuseFailAlloc_3577_, 3, v_usedQuotCtxts_3559_);
lean_ctor_set(v_reuseFailAlloc_3577_, 4, v_nextMacroScope_3560_);
lean_ctor_set(v_reuseFailAlloc_3577_, 5, v_maxRecDepth_3561_);
lean_ctor_set(v_reuseFailAlloc_3577_, 6, v_ngen_3562_);
lean_ctor_set(v_reuseFailAlloc_3577_, 7, v_auxDeclNGen_3563_);
lean_ctor_set(v_reuseFailAlloc_3577_, 8, v_infoState_3564_);
lean_ctor_set(v_reuseFailAlloc_3577_, 9, v_traceState_3565_);
lean_ctor_set(v_reuseFailAlloc_3577_, 10, v_snapshotTasks_3566_);
lean_ctor_set(v_reuseFailAlloc_3577_, 11, v_prevLinterStates_3567_);
lean_ctor_set(v_reuseFailAlloc_3577_, 12, v_codeQualityEntryTasks_3568_);
v___x_3574_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = lean_st_ref_put(v___y_3510_, v___x_3574_);
v___x_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3572_);
return v___x_3576_;
}
}
}
}
v___jp_3580_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v_a_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v_str_3603_; lean_object* v_startInclusive_3604_; lean_object* v_endExclusive_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3620_; 
v___x_3593_ = l_Lean_MessageLog_toList(v___y_3588_);
lean_dec(v___y_3588_);
v___x_3594_ = lean_box(0);
v___x_3595_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3592_, v___x_3593_, v___x_3594_);
lean_dec(v___y_3592_);
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___x_3595_);
v___x_3597_ = l_Lean_Elab_Tactic_GuardMsgs_MessageOrdering_apply(v___y_3581_, v_a_3596_);
v___x_3598_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__4));
v___x_3599_ = l_String_intercalate(v___x_3598_, v___x_3597_);
v___x_3600_ = lean_string_utf8_byte_size(v___x_3599_);
lean_inc(v___y_3586_);
v___x_3601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3599_);
lean_ctor_set(v___x_3601_, 1, v___y_3586_);
lean_ctor_set(v___x_3601_, 2, v___x_3600_);
v___x_3602_ = l_String_Slice_trimAscii(v___x_3601_);
v_str_3603_ = lean_ctor_get(v___x_3602_, 0);
v_startInclusive_3604_ = lean_ctor_get(v___x_3602_, 1);
v_endExclusive_3605_ = lean_ctor_get(v___x_3602_, 2);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3607_ = v___x_3602_;
v_isShared_3608_ = v_isSharedCheck_3620_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_endExclusive_3605_);
lean_inc(v_startInclusive_3604_);
lean_inc(v_str_3603_);
lean_dec(v___x_3602_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3620_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; 
v___x_3609_ = lean_string_utf8_extract_fast(v_str_3603_, v_startInclusive_3604_, v_endExclusive_3605_);
lean_dec(v_endExclusive_3605_);
lean_dec(v_startInclusive_3604_);
lean_dec_ref(v_str_3603_);
if (v___y_3590_ == 0)
{
lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
lean_del_object(v___x_3607_);
lean_inc_ref(v___y_3587_);
v___x_3610_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3583_, v___y_3587_);
lean_inc_ref(v___x_3609_);
v___x_3611_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3583_, v___x_3609_);
v___x_3612_ = lean_string_dec_eq(v___x_3610_, v___x_3611_);
lean_dec_ref(v___x_3611_);
lean_dec_ref(v___x_3610_);
v___y_3508_ = v___y_3582_;
v___y_3509_ = v___y_3584_;
v___y_3510_ = v___y_3585_;
v___y_3511_ = v___y_3586_;
v___y_3512_ = v___y_3587_;
v___y_3513_ = v___x_3609_;
v___y_3514_ = v___y_3589_;
v___y_3515_ = v___y_3591_;
v___y_3516_ = v___x_3612_;
goto v___jp_3507_;
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3617_; 
lean_inc_ref(v___x_3609_);
v___x_3613_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3583_, v___x_3609_);
lean_inc_ref(v___y_3587_);
v___x_3614_ = l_Lean_Elab_Tactic_GuardMsgs_WhitespaceMode_apply(v___y_3583_, v___y_3587_);
v___x_3615_ = lean_string_utf8_byte_size(v___x_3613_);
lean_inc(v___y_3586_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 2, v___x_3615_);
lean_ctor_set(v___x_3607_, 1, v___y_3586_);
lean_ctor_set(v___x_3607_, 0, v___x_3613_);
v___x_3617_ = v___x_3607_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3613_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v___y_3586_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
uint8_t v___x_3618_; 
v___x_3618_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9(v___x_3614_, v___x_3617_);
lean_dec_ref(v___x_3617_);
v___y_3508_ = v___y_3582_;
v___y_3509_ = v___y_3584_;
v___y_3510_ = v___y_3585_;
v___y_3511_ = v___y_3586_;
v___y_3512_ = v___y_3587_;
v___y_3513_ = v___x_3609_;
v___y_3514_ = v___y_3589_;
v___y_3515_ = v___y_3591_;
v___y_3516_ = v___x_3618_;
goto v___jp_3507_;
}
}
}
}
v___jp_3621_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v_str_3632_; lean_object* v_startInclusive_3633_; lean_object* v_endExclusive_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3628_ = lean_unsigned_to_nat(0u);
v___x_3629_ = lean_string_utf8_byte_size(v___y_3627_);
v___x_3630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3630_, 0, v___y_3627_);
lean_ctor_set(v___x_3630_, 1, v___x_3628_);
lean_ctor_set(v___x_3630_, 2, v___x_3629_);
v___x_3631_ = l_String_Slice_trimAscii(v___x_3630_);
v_str_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc_ref(v_str_3632_);
v_startInclusive_3633_ = lean_ctor_get(v___x_3631_, 1);
lean_inc(v_startInclusive_3633_);
v_endExclusive_3634_ = lean_ctor_get(v___x_3631_, 2);
lean_inc(v_endExclusive_3634_);
lean_dec_ref(v___x_3631_);
v___x_3635_ = lean_string_utf8_extract_fast(v_str_3632_, v_startInclusive_3633_, v_endExclusive_3634_);
lean_dec(v_endExclusive_3634_);
lean_dec(v_startInclusive_3633_);
lean_dec_ref(v_str_3632_);
v___x_3636_ = l_Lean_Elab_Tactic_GuardMsgs_removeTrailingWhitespaceMarker(v___x_3635_);
v___x_3637_ = l_Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsSpec(v___y_3622_, v___y_3626_, v___y_3625_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v_filterFn_3639_; uint8_t v_whitespace_3640_; uint8_t v_ordering_3641_; uint8_t v_reportPositions_3642_; uint8_t v_substring_3643_; lean_object* v___x_3644_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v_filterFn_3639_ = lean_ctor_get(v_a_3638_, 0);
lean_inc_ref(v_filterFn_3639_);
v_whitespace_3640_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*1);
v_ordering_3641_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*1 + 1);
v_reportPositions_3642_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*1 + 2);
v_substring_3643_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*1 + 3);
lean_dec(v_a_3638_);
v___x_3644_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___y_3624_, v___y_3626_, v___y_3625_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v_a_3649_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v___x_3646_ = l_Lean_MessageLog_toList(v_a_3645_);
v___x_3647_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__5);
v___x_3648_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3639_, v___x_3646_, v___x_3647_);
lean_dec(v___x_3646_);
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref(v___x_3648_);
if (v_reportPositions_3642_ == 0)
{
lean_object* v_fst_3650_; lean_object* v_snd_3651_; lean_object* v___x_3652_; 
v_fst_3650_ = lean_ctor_get(v_a_3649_, 0);
lean_inc(v_fst_3650_);
v_snd_3651_ = lean_ctor_get(v_a_3649_, 1);
lean_inc(v_snd_3651_);
lean_dec(v_a_3649_);
v___x_3652_ = lean_box(0);
v___y_3581_ = v_ordering_3641_;
v___y_3582_ = v___y_3623_;
v___y_3583_ = v_whitespace_3640_;
v___y_3584_ = v_snd_3651_;
v___y_3585_ = v___y_3625_;
v___y_3586_ = v___x_3628_;
v___y_3587_ = v___x_3636_;
v___y_3588_ = v_fst_3650_;
v___y_3589_ = v_a_3645_;
v___y_3590_ = v_substring_3643_;
v___y_3591_ = v___y_3626_;
v___y_3592_ = v___x_3652_;
goto v___jp_3580_;
}
else
{
lean_object* v_fst_3653_; lean_object* v_snd_3654_; uint8_t v___x_3655_; lean_object* v___x_3656_; 
v_fst_3653_ = lean_ctor_get(v_a_3649_, 0);
lean_inc(v_fst_3653_);
v_snd_3654_ = lean_ctor_get(v_a_3649_, 1);
lean_inc(v_snd_3654_);
lean_dec(v_a_3649_);
v___x_3655_ = 0;
v___x_3656_ = l_Lean_Syntax_getPos_x3f(v___y_3623_, v___x_3655_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v___x_3657_; 
v___x_3657_ = lean_box(0);
v___y_3581_ = v_ordering_3641_;
v___y_3582_ = v___y_3623_;
v___y_3583_ = v_whitespace_3640_;
v___y_3584_ = v_snd_3654_;
v___y_3585_ = v___y_3625_;
v___y_3586_ = v___x_3628_;
v___y_3587_ = v___x_3636_;
v___y_3588_ = v_fst_3653_;
v___y_3589_ = v_a_3645_;
v___y_3590_ = v_substring_3643_;
v___y_3591_ = v___y_3626_;
v___y_3592_ = v___x_3657_;
goto v___jp_3580_;
}
else
{
lean_object* v_val_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3668_; 
v_val_3658_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3660_ = v___x_3656_;
v_isShared_3661_ = v_isSharedCheck_3668_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_val_3658_);
lean_dec(v___x_3656_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3668_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v_fileMap_3662_; lean_object* v___x_3663_; lean_object* v_line_3664_; lean_object* v___x_3666_; 
v_fileMap_3662_ = lean_ctor_get(v___y_3626_, 1);
lean_inc_ref(v_fileMap_3662_);
v___x_3663_ = l_Lean_FileMap_toPosition(v_fileMap_3662_, v_val_3658_);
lean_dec(v_val_3658_);
v_line_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_line_3664_);
lean_dec_ref(v___x_3663_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v_line_3664_);
v___x_3666_ = v___x_3660_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_line_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
v___y_3581_ = v_ordering_3641_;
v___y_3582_ = v___y_3623_;
v___y_3583_ = v_whitespace_3640_;
v___y_3584_ = v_snd_3654_;
v___y_3585_ = v___y_3625_;
v___y_3586_ = v___x_3628_;
v___y_3587_ = v___x_3636_;
v___y_3588_ = v_fst_3653_;
v___y_3589_ = v_a_3645_;
v___y_3590_ = v_substring_3643_;
v___y_3591_ = v___y_3626_;
v___y_3592_ = v___x_3666_;
goto v___jp_3580_;
}
}
}
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_dec_ref(v_filterFn_3639_);
lean_dec_ref(v___x_3636_);
lean_dec(v___y_3623_);
v_a_3669_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3644_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3644_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec_ref(v___x_3636_);
lean_dec(v___y_3624_);
lean_dec(v___y_3623_);
v_a_3677_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3637_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3637_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
v___jp_3685_:
{
if (lean_obj_tag(v___y_3688_) == 0)
{
lean_object* v___x_3692_; 
v___x_3692_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_3622_ = v___y_3691_;
v___y_3623_ = v___y_3686_;
v___y_3624_ = v___y_3687_;
v___y_3625_ = v___y_3689_;
v___y_3626_ = v___y_3690_;
v___y_3627_ = v___x_3692_;
goto v___jp_3621_;
}
else
{
lean_object* v_val_3693_; lean_object* v___x_3694_; 
v_val_3693_ = lean_ctor_get(v___y_3688_, 0);
lean_inc(v_val_3693_);
lean_dec_ref_known(v___y_3688_, 1);
v___x_3694_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10(v_val_3693_, v___y_3690_, v___y_3689_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3694_, 1);
v___y_3622_ = v___y_3691_;
v___y_3623_ = v___y_3686_;
v___y_3624_ = v___y_3687_;
v___y_3625_ = v___y_3689_;
v___y_3626_ = v___y_3690_;
v___y_3627_ = v_a_3695_;
goto v___jp_3621_;
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v___y_3691_);
lean_dec(v___y_3687_);
lean_dec(v___y_3686_);
v_a_3696_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3694_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3694_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
v___jp_3704_:
{
lean_object* v___x_3708_; lean_object* v_tk_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3708_ = lean_unsigned_to_nat(1u);
v_tk_3709_ = l_Lean_Syntax_getArg(v_x_3468_, v___x_3708_);
v___x_3710_ = lean_unsigned_to_nat(2u);
v___x_3711_ = l_Lean_Syntax_getArg(v_x_3468_, v___x_3710_);
v___x_3712_ = lean_unsigned_to_nat(4u);
v___x_3713_ = l_Lean_Syntax_getArg(v_x_3468_, v___x_3712_);
lean_dec(v_x_3468_);
v___x_3714_ = l_Lean_Syntax_getOptional_x3f(v___x_3711_);
lean_dec(v___x_3711_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v___x_3715_; 
v___x_3715_ = lean_box(0);
v___y_3686_ = v_tk_3709_;
v___y_3687_ = v___x_3713_;
v___y_3688_ = v_dc_x3f_3705_;
v___y_3689_ = v___y_3707_;
v___y_3690_ = v___y_3706_;
v___y_3691_ = v___x_3715_;
goto v___jp_3685_;
}
else
{
lean_object* v_val_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
v_val_3716_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3714_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_val_3716_);
lean_dec(v___x_3714_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_val_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
v___y_3686_ = v_tk_3709_;
v___y_3687_ = v___x_3713_;
v___y_3688_ = v_dc_x3f_3705_;
v___y_3689_ = v___y_3707_;
v___y_3690_ = v___y_3706_;
v___y_3691_ = v___x_3721_;
goto v___jp_3685_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed(lean_object* v_x_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs(v_x_3736_, v_a_3737_, v_a_3738_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(lean_object* v_filterFn_3741_, lean_object* v_as_3742_, lean_object* v_as_x27_3743_, lean_object* v_b_3744_, lean_object* v_a_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___redArg(v_filterFn_3741_, v_as_x27_3743_, v_b_3744_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0___boxed(lean_object* v_filterFn_3750_, lean_object* v_as_3751_, lean_object* v_as_x27_3752_, lean_object* v_b_3753_, lean_object* v_a_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__0(v_filterFn_3750_, v_as_3751_, v_as_x27_3752_, v_b_3753_, v_a_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v_as_x27_3752_);
lean_dec(v_as_3751_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(lean_object* v___y_3759_, lean_object* v_x_3760_, lean_object* v_x_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___redArg(v___y_3759_, v_x_3760_, v_x_3761_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1___boxed(lean_object* v___y_3766_, lean_object* v_x_3767_, lean_object* v_x_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__1(v___y_3766_, v_x_3767_, v_x_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3766_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(lean_object* v_t_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___redArg(v_t_3773_, v___y_3775_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4___boxed(lean_object* v_t_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__3_spec__4(v_t_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(lean_object* v___x_3783_, lean_object* v___x_3784_, lean_object* v___x_3785_, lean_object* v_inst_3786_, lean_object* v_R_3787_, lean_object* v_a_3788_, lean_object* v_b_3789_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___redArg(v___x_3783_, v___x_3784_, v___x_3785_, v_a_3788_, v_b_3789_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6___boxed(lean_object* v___x_3791_, lean_object* v___x_3792_, lean_object* v___x_3793_, lean_object* v_inst_3794_, lean_object* v_R_3795_, lean_object* v_a_3796_, lean_object* v_b_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6(v___x_3791_, v___x_3792_, v___x_3793_, v_inst_3794_, v_R_3795_, v_a_3796_, v_b_3797_);
lean_dec_ref(v___x_3792_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(lean_object* v_msgData_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___redArg(v_msgData_3799_, v___y_3801_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2_spec__5(v_msgData_3804_, v___y_3805_, v___y_3806_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(lean_object* v___x_3809_, lean_object* v___x_3810_, lean_object* v___x_3811_, lean_object* v_inst_3812_, lean_object* v_R_3813_, lean_object* v_a_3814_, lean_object* v_b_3815_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___redArg(v___x_3809_, v___x_3810_, v___x_3811_, v_a_3814_, v_b_3815_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8___boxed(lean_object* v___x_3817_, lean_object* v___x_3818_, lean_object* v___x_3819_, lean_object* v_inst_3820_, lean_object* v_R_3821_, lean_object* v_a_3822_, lean_object* v_b_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__6_spec__8(v___x_3817_, v___x_3818_, v___x_3819_, v_inst_3820_, v_R_3821_, v_a_3822_, v_b_3823_);
lean_dec_ref(v___x_3818_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(lean_object* v___x_3825_, lean_object* v_original_3826_, lean_object* v_a_3827_, lean_object* v_inst_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___redArg(v___x_3825_, v_original_3826_, v_a_3827_, v_a_3829_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10___boxed(lean_object* v___x_3831_, lean_object* v_original_3832_, lean_object* v_a_3833_, lean_object* v_inst_3834_, lean_object* v_a_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__10(v___x_3831_, v_original_3832_, v_a_3833_, v_inst_3834_, v_a_3835_);
lean_dec_ref(v_a_3833_);
lean_dec_ref(v_original_3832_);
lean_dec(v___x_3831_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(lean_object* v___x_3837_, lean_object* v_edited_3838_, lean_object* v_a_3839_, lean_object* v_inst_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___redArg(v___x_3837_, v_edited_3838_, v_a_3839_, v_a_3841_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11___boxed(lean_object* v___x_3843_, lean_object* v_edited_3844_, lean_object* v_a_3845_, lean_object* v_inst_3846_, lean_object* v_a_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__11(v___x_3843_, v_edited_3844_, v_a_3845_, v_inst_3846_, v_a_3847_);
lean_dec_ref(v_a_3845_);
lean_dec_ref(v_edited_3844_);
lean_dec(v___x_3843_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(lean_object* v___x_3849_, lean_object* v_original_3850_, lean_object* v_inst_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v___x_3853_; 
v___x_3853_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___redArg(v___x_3849_, v_original_3850_, v_a_3852_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14___boxed(lean_object* v___x_3854_, lean_object* v_original_3855_, lean_object* v_inst_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__14(v___x_3854_, v_original_3855_, v_inst_3856_, v_a_3857_);
lean_dec_ref(v_original_3855_);
lean_dec(v___x_3854_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(lean_object* v___x_3859_, lean_object* v_edited_3860_, lean_object* v_inst_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___redArg(v___x_3859_, v_edited_3860_, v_a_3862_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15___boxed(lean_object* v___x_3864_, lean_object* v_edited_3865_, lean_object* v_inst_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__15(v___x_3864_, v_edited_3865_, v_inst_3866_, v_a_3867_);
lean_dec_ref(v_edited_3865_);
lean_dec(v___x_3864_);
return v_res_3868_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(lean_object* v_s_3869_, lean_object* v_inst_3870_, lean_object* v_R_3871_, lean_object* v_a_3872_, uint8_t v_b_3873_, lean_object* v_c_3874_){
_start:
{
uint8_t v___x_3875_; 
v___x_3875_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_3869_, v_a_3872_, v_b_3873_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___boxed(lean_object* v_s_3876_, lean_object* v_inst_3877_, lean_object* v_R_3878_, lean_object* v_a_3879_, lean_object* v_b_3880_, lean_object* v_c_3881_){
_start:
{
uint8_t v_b_boxed_3882_; uint8_t v_res_3883_; lean_object* v_r_3884_; 
v_b_boxed_3882_ = lean_unbox(v_b_3880_);
v_res_3883_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21(v_s_3876_, v_inst_3877_, v_R_3878_, v_a_3879_, v_b_boxed_3882_, v_c_3881_);
lean_dec_ref(v_s_3876_);
v_r_3884_ = lean_box(v_res_3883_);
return v_r_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(lean_object* v_00_u03b1_3885_, lean_object* v_ref_3886_, lean_object* v_msg_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___redArg(v_ref_3886_, v_msg_3887_, v___y_3888_, v___y_3889_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23___boxed(lean_object* v_00_u03b1_3892_, lean_object* v_ref_3893_, lean_object* v_msg_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23(v_00_u03b1_3892_, v_ref_3893_, v_msg_3894_, v___y_3895_, v___y_3896_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v_ref_3893_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(lean_object* v_as_3899_, lean_object* v_as_x27_3900_, lean_object* v_b_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v___x_3903_; 
v___x_3903_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___redArg(v_as_x27_3900_, v_b_3901_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16___boxed(lean_object* v_as_3904_, lean_object* v_as_x27_3905_, lean_object* v_b_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__16(v_as_3904_, v_as_x27_3905_, v_b_3906_, v_a_3907_);
lean_dec(v_as_x27_3905_);
lean_dec(v_as_3904_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(lean_object* v_lsize_3909_, lean_object* v_rsize_3910_, lean_object* v_histogram_3911_, lean_object* v_index_3912_, lean_object* v_val_3913_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___redArg(v_histogram_3911_, v_index_3912_, v_val_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19___boxed(lean_object* v_lsize_3915_, lean_object* v_rsize_3916_, lean_object* v_histogram_3917_, lean_object* v_index_3918_, lean_object* v_val_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19(v_lsize_3915_, v_rsize_3916_, v_histogram_3917_, v_index_3918_, v_val_3919_);
lean_dec(v_rsize_3916_);
lean_dec(v_lsize_3915_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(lean_object* v_upperBound_3921_, lean_object* v___x_3922_, lean_object* v_fst_3923_, lean_object* v___x_3924_, lean_object* v_inst_3925_, lean_object* v_R_3926_, lean_object* v_a_3927_, lean_object* v_b_3928_, lean_object* v_c_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___redArg(v_upperBound_3921_, v___x_3922_, v_fst_3923_, v___x_3924_, v_a_3927_, v_b_3928_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20___boxed(lean_object* v_upperBound_3931_, lean_object* v___x_3932_, lean_object* v_fst_3933_, lean_object* v___x_3934_, lean_object* v_inst_3935_, lean_object* v_R_3936_, lean_object* v_a_3937_, lean_object* v_b_3938_, lean_object* v_c_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__20(v_upperBound_3931_, v___x_3932_, v_fst_3933_, v___x_3934_, v_inst_3935_, v_R_3936_, v_a_3937_, v_b_3938_, v_c_3939_);
lean_dec(v___x_3934_);
lean_dec_ref(v_fst_3933_);
lean_dec(v___x_3932_);
lean_dec(v_upperBound_3931_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(lean_object* v_lsize_3941_, lean_object* v_rsize_3942_, lean_object* v_histogram_3943_, lean_object* v_index_3944_, lean_object* v_val_3945_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___redArg(v_histogram_3943_, v_index_3944_, v_val_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21___boxed(lean_object* v_lsize_3947_, lean_object* v_rsize_3948_, lean_object* v_histogram_3949_, lean_object* v_index_3950_, lean_object* v_val_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__21(v_lsize_3947_, v_rsize_3948_, v_histogram_3949_, v_index_3950_, v_val_3951_);
lean_dec(v_rsize_3948_);
lean_dec(v_lsize_3947_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(lean_object* v_upperBound_3953_, lean_object* v_fst_3954_, lean_object* v___x_3955_, lean_object* v_fst_3956_, lean_object* v_inst_3957_, lean_object* v_R_3958_, lean_object* v_a_3959_, lean_object* v_b_3960_, lean_object* v_c_3961_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___redArg(v_upperBound_3953_, v_fst_3954_, v___x_3955_, v_fst_3956_, v_a_3959_, v_b_3960_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22___boxed(lean_object* v_upperBound_3963_, lean_object* v_fst_3964_, lean_object* v___x_3965_, lean_object* v_fst_3966_, lean_object* v_inst_3967_, lean_object* v_R_3968_, lean_object* v_a_3969_, lean_object* v_b_3970_, lean_object* v_c_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__22(v_upperBound_3963_, v_fst_3964_, v___x_3965_, v_fst_3966_, v_inst_3967_, v_R_3968_, v_a_3969_, v_b_3970_, v_c_3971_);
lean_dec_ref(v_fst_3966_);
lean_dec(v___x_3965_);
lean_dec_ref(v_fst_3964_);
lean_dec(v_upperBound_3963_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(lean_object* v_00_u03b1_3973_, lean_object* v_msg_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___redArg(v_msg_3974_, v___y_3975_, v___y_3976_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35___boxed(lean_object* v_00_u03b1_3979_, lean_object* v_msg_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35(v_00_u03b1_3979_, v_msg_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(lean_object* v_00_u03b2_3985_, lean_object* v_m_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___redArg(v_m_3986_, v_a_3987_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3989_, lean_object* v_m_3990_, lean_object* v_a_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25(v_00_u03b2_3989_, v_m_3990_, v_a_3991_);
lean_dec_ref(v_a_3991_);
lean_dec_ref(v_m_3990_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26(lean_object* v_00_u03b2_3993_, lean_object* v_m_3994_, lean_object* v_a_3995_, lean_object* v_b_3996_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26___redArg(v_m_3994_, v_a_3995_, v_b_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(lean_object* v_msgData_3998_, lean_object* v_macroStack_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___redArg(v_msgData_3998_, v_macroStack_3999_, v___y_4001_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40___boxed(lean_object* v_msgData_4004_, lean_object* v_macroStack_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__10_spec__23_spec__35_spec__40(v_msgData_4004_, v_macroStack_4005_, v___y_4006_, v___y_4007_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29(lean_object* v_inst_4010_, lean_object* v_R_4011_, lean_object* v_a_4012_, lean_object* v_b_4013_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__15_spec__20_spec__29___redArg(v_a_4012_, v_b_4013_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(lean_object* v_00_u03b2_4015_, lean_object* v_a_4016_, lean_object* v_x_4017_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___redArg(v_a_4016_, v_x_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35___boxed(lean_object* v_00_u03b2_4019_, lean_object* v_a_4020_, lean_object* v_x_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__25_spec__35(v_00_u03b2_4019_, v_a_4020_, v_x_4021_);
lean_dec(v_x_4021_);
lean_dec_ref(v_a_4020_);
return v_res_4022_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(lean_object* v_00_u03b2_4023_, lean_object* v_a_4024_, lean_object* v_x_4025_){
_start:
{
uint8_t v___x_4026_; 
v___x_4026_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___redArg(v_a_4024_, v_x_4025_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37___boxed(lean_object* v_00_u03b2_4027_, lean_object* v_a_4028_, lean_object* v_x_4029_){
_start:
{
uint8_t v_res_4030_; lean_object* v_r_4031_; 
v_res_4030_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__37(v_00_u03b2_4027_, v_a_4028_, v_x_4029_);
lean_dec(v_x_4029_);
lean_dec_ref(v_a_4028_);
v_r_4031_ = lean_box(v_res_4030_);
return v_r_4031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38(lean_object* v_00_u03b2_4032_, lean_object* v_data_4033_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38___redArg(v_data_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39(lean_object* v_00_u03b2_4035_, lean_object* v_a_4036_, lean_object* v_b_4037_, lean_object* v_x_4038_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__39___redArg(v_a_4036_, v_b_4037_, v_x_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44(lean_object* v_00_u03b2_4040_, lean_object* v_i_4041_, lean_object* v_source_4042_, lean_object* v_target_4043_){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44___redArg(v_i_4041_, v_source_4042_, v_target_4043_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46(lean_object* v_00_u03b2_4045_, lean_object* v_x_4046_, lean_object* v_x_4047_){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__7_spec__12_spec__19_spec__26_spec__38_spec__44_spec__46___redArg(v_x_4046_, v_x_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1(){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4057_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4058_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___closed__1));
v___x_4059_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4060_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___boxed), 4, 0);
v___x_4061_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4057_, v___x_4058_, v___x_4059_, v___x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___boxed(lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1();
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3(){
_start:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4090_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs__1___closed__1));
v___x_4091_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___closed__6));
v___x_4092_ = l_Lean_addBuiltinDeclarationRanges(v___x_4090_, v___x_4091_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3___boxed(lean_object* v_a_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_declRange__3();
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(lean_object* v___y_4095_){
_start:
{
lean_object* v_doc_4097_; lean_object* v___x_4098_; 
v_doc_4097_ = lean_ctor_get(v___y_4095_, 1);
lean_inc_ref(v_doc_4097_);
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v_doc_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1___boxed(lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v___y_4099_);
lean_dec_ref(v___y_4099_);
return v_res_4101_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(lean_object* v_s_4102_, lean_object* v_a_4103_, uint8_t v_b_4104_){
_start:
{
lean_object* v_str_4105_; lean_object* v_startInclusive_4106_; lean_object* v_endExclusive_4107_; lean_object* v___x_4108_; uint8_t v_decide_4109_; 
v_str_4105_ = lean_ctor_get(v_s_4102_, 0);
v_startInclusive_4106_ = lean_ctor_get(v_s_4102_, 1);
v_endExclusive_4107_ = lean_ctor_get(v_s_4102_, 2);
v___x_4108_ = lean_nat_sub(v_endExclusive_4107_, v_startInclusive_4106_);
v_decide_4109_ = lean_nat_dec_eq(v_a_4103_, v___x_4108_);
lean_dec(v___x_4108_);
if (v_decide_4109_ == 0)
{
lean_object* v___x_4110_; uint32_t v___x_4111_; uint32_t v___x_4112_; uint8_t v___x_4113_; 
v___x_4110_ = lean_nat_add(v_startInclusive_4106_, v_a_4103_);
lean_dec(v_a_4103_);
v___x_4111_ = lean_string_utf8_get_fast(v_str_4105_, v___x_4110_);
v___x_4112_ = 10;
v___x_4113_ = lean_uint32_dec_eq(v___x_4111_, v___x_4112_);
if (v___x_4113_ == 0)
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4114_ = lean_string_utf8_next_fast(v_str_4105_, v___x_4110_);
lean_dec(v___x_4110_);
v___x_4115_ = lean_nat_sub(v___x_4114_, v_startInclusive_4106_);
v_a_4103_ = v___x_4115_;
v_b_4104_ = v___x_4113_;
goto _start;
}
else
{
lean_dec(v___x_4110_);
return v___x_4113_;
}
}
else
{
lean_dec(v_a_4103_);
return v_b_4104_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg___boxed(lean_object* v_s_4117_, lean_object* v_a_4118_, lean_object* v_b_4119_){
_start:
{
uint8_t v_b_boxed_4120_; uint8_t v_res_4121_; lean_object* v_r_4122_; 
v_b_boxed_4120_ = lean_unbox(v_b_4119_);
v_res_4121_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4117_, v_a_4118_, v_b_boxed_4120_);
lean_dec_ref(v_s_4117_);
v_r_4122_ = lean_box(v_res_4121_);
return v_r_4122_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(lean_object* v_s_4123_){
_start:
{
lean_object* v_searcher_4124_; uint8_t v___x_4125_; uint8_t v___x_4126_; 
v_searcher_4124_ = lean_unsigned_to_nat(0u);
v___x_4125_ = 0;
v___x_4126_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4123_, v_searcher_4124_, v___x_4125_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2___boxed(lean_object* v_s_4127_){
_start:
{
uint8_t v_res_4128_; lean_object* v_r_4129_; 
v_res_4128_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v_s_4127_);
lean_dec_ref(v_s_4127_);
v_r_4129_ = lean_box(v_res_4128_);
return v_r_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(lean_object* v___x_4141_, lean_object* v_fst_4142_, uint8_t v___x_4143_, lean_object* v_a_4144_, lean_object* v___x_4145_, lean_object* v___x_4146_, lean_object* v___x_4147_, lean_object* v___x_4148_, lean_object* v___x_4149_, lean_object* v___x_4150_, lean_object* v___x_4151_, lean_object* v___x_4152_, lean_object* v_snd_4153_, lean_object* v___x_4154_){
_start:
{
if (lean_obj_tag(v___x_4141_) == 1)
{
lean_object* v_val_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4217_; 
v_val_4156_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4158_ = v___x_4141_;
v_isShared_4159_ = v_isSharedCheck_4217_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_val_4156_);
lean_dec(v___x_4141_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4217_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4160_ = lean_unsigned_to_nat(0u);
v___x_4161_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__2));
v___x_4162_ = l_Lean_Syntax_setArg(v_fst_4142_, v___x_4160_, v___x_4161_);
v___x_4163_ = l_Lean_Syntax_getPos_x3f(v___x_4162_, v___x_4143_);
lean_dec(v___x_4162_);
if (lean_obj_tag(v___x_4163_) == 1)
{
lean_object* v_val_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4213_; 
lean_dec_ref(v___x_4154_);
v_val_4164_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4166_ = v___x_4163_;
v_isShared_4167_ = v_isSharedCheck_4213_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_val_4164_);
lean_dec(v___x_4163_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4213_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___y_4169_; lean_object* v___x_4195_; lean_object* v___x_4201_; uint8_t v___x_4202_; 
v___x_4195_ = l_Lean_Elab_Tactic_GuardMsgs_revealTrailingWhitespace(v_snd_4153_);
v___x_4201_ = lean_string_utf8_byte_size(v___x_4195_);
v___x_4202_ = lean_nat_dec_eq(v___x_4201_, v___x_4160_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; 
v___x_4203_ = lean_string_length(v___x_4195_);
v___x_4204_ = lean_unsigned_to_nat(93u);
v___x_4205_ = lean_nat_dec_le(v___x_4203_, v___x_4204_);
if (v___x_4205_ == 0)
{
goto v___jp_4196_;
}
else
{
lean_object* v___x_4206_; uint8_t v___x_4207_; 
lean_inc_ref(v___x_4195_);
v___x_4206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4195_);
lean_ctor_set(v___x_4206_, 1, v___x_4160_);
lean_ctor_set(v___x_4206_, 2, v___x_4201_);
v___x_4207_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2(v___x_4206_);
lean_dec_ref_known(v___x_4206_, 3);
if (v___x_4207_ == 0)
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4208_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__5));
v___x_4209_ = lean_string_append(v___x_4208_, v___x_4195_);
lean_dec_ref(v___x_4195_);
v___x_4210_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__6));
v___x_4211_ = lean_string_append(v___x_4209_, v___x_4210_);
v___y_4169_ = v___x_4211_;
goto v___jp_4168_;
}
else
{
goto v___jp_4196_;
}
}
}
else
{
lean_object* v___x_4212_; 
lean_dec_ref(v___x_4195_);
v___x_4212_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_messageToString___closed__9));
v___y_4169_ = v___x_4212_;
goto v___jp_4168_;
}
v___jp_4168_:
{
lean_object* v_toEditableDocumentCore_4170_; lean_object* v_meta_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4191_; 
v_toEditableDocumentCore_4170_ = lean_ctor_get(v_a_4144_, 0);
lean_inc_ref(v_toEditableDocumentCore_4170_);
v_meta_4171_ = lean_ctor_get(v_toEditableDocumentCore_4170_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v_toEditableDocumentCore_4170_);
if (v_isSharedCheck_4191_ == 0)
{
lean_object* v_unused_4192_; lean_object* v_unused_4193_; lean_object* v_unused_4194_; 
v_unused_4192_ = lean_ctor_get(v_toEditableDocumentCore_4170_, 3);
lean_dec(v_unused_4192_);
v_unused_4193_ = lean_ctor_get(v_toEditableDocumentCore_4170_, 2);
lean_dec(v_unused_4193_);
v_unused_4194_ = lean_ctor_get(v_toEditableDocumentCore_4170_, 1);
lean_dec(v_unused_4194_);
v___x_4173_ = v_toEditableDocumentCore_4170_;
v_isShared_4174_ = v_isSharedCheck_4191_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_meta_4171_);
lean_dec(v_toEditableDocumentCore_4170_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4191_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v_text_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4181_; 
v_text_4175_ = lean_ctor_get(v_meta_4171_, 3);
lean_inc_ref(v_text_4175_);
lean_dec_ref(v_meta_4171_);
v___x_4176_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_4144_);
v___x_4177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4177_, 0, v_val_4156_);
lean_ctor_set(v___x_4177_, 1, v_val_4164_);
v___x_4178_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_4175_, v___x_4177_);
v___x_4179_ = lean_box(0);
lean_inc(v___x_4145_);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 3, v___x_4145_);
lean_ctor_set(v___x_4173_, 2, v___x_4179_);
lean_ctor_set(v___x_4173_, 1, v___y_4169_);
lean_ctor_set(v___x_4173_, 0, v___x_4178_);
v___x_4181_ = v___x_4173_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4178_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v___y_4169_);
lean_ctor_set(v_reuseFailAlloc_4190_, 2, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4190_, 3, v___x_4145_);
v___x_4181_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
lean_object* v___x_4182_; lean_object* v___x_4184_; 
v___x_4182_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_4176_, v___x_4181_);
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 0, v___x_4182_);
v___x_4184_ = v___x_4166_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4182_);
v___x_4184_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
lean_object* v___x_4185_; lean_object* v___x_4187_; 
lean_inc(v___x_4145_);
v___x_4185_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4145_);
lean_ctor_set(v___x_4185_, 1, v___x_4145_);
lean_ctor_set(v___x_4185_, 2, v___x_4146_);
lean_ctor_set(v___x_4185_, 3, v___x_4147_);
lean_ctor_set(v___x_4185_, 4, v___x_4148_);
lean_ctor_set(v___x_4185_, 5, v___x_4149_);
lean_ctor_set(v___x_4185_, 6, v___x_4150_);
lean_ctor_set(v___x_4185_, 7, v___x_4184_);
lean_ctor_set(v___x_4185_, 8, v___x_4151_);
lean_ctor_set(v___x_4185_, 9, v___x_4152_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set_tag(v___x_4158_, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4185_);
v___x_4187_ = v___x_4158_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4185_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
}
v___jp_4196_:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4197_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__3));
v___x_4198_ = lean_string_append(v___x_4197_, v___x_4195_);
lean_dec_ref(v___x_4195_);
v___x_4199_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___closed__4));
v___x_4200_ = lean_string_append(v___x_4198_, v___x_4199_);
v___y_4169_ = v___x_4200_;
goto v___jp_4168_;
}
}
}
else
{
lean_object* v___x_4215_; 
lean_dec(v___x_4163_);
lean_dec(v_val_4156_);
lean_dec_ref(v_snd_4153_);
lean_dec(v___x_4152_);
lean_dec(v___x_4151_);
lean_dec(v___x_4150_);
lean_dec(v___x_4149_);
lean_dec(v___x_4148_);
lean_dec(v___x_4147_);
lean_dec_ref(v___x_4146_);
lean_dec(v___x_4145_);
lean_dec_ref(v_a_4144_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set_tag(v___x_4158_, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4154_);
v___x_4215_ = v___x_4158_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4154_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
else
{
lean_object* v___x_4218_; 
lean_dec_ref(v_snd_4153_);
lean_dec(v___x_4152_);
lean_dec(v___x_4151_);
lean_dec(v___x_4150_);
lean_dec(v___x_4149_);
lean_dec(v___x_4148_);
lean_dec(v___x_4147_);
lean_dec_ref(v___x_4146_);
lean_dec(v___x_4145_);
lean_dec_ref(v_a_4144_);
lean_dec(v_fst_4142_);
lean_dec(v___x_4141_);
v___x_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4154_);
return v___x_4218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed(lean_object* v___x_4219_, lean_object* v_fst_4220_, lean_object* v___x_4221_, lean_object* v_a_4222_, lean_object* v___x_4223_, lean_object* v___x_4224_, lean_object* v___x_4225_, lean_object* v___x_4226_, lean_object* v___x_4227_, lean_object* v___x_4228_, lean_object* v___x_4229_, lean_object* v___x_4230_, lean_object* v_snd_4231_, lean_object* v___x_4232_, lean_object* v___y_4233_){
_start:
{
uint8_t v___x_4482__boxed_4234_; lean_object* v_res_4235_; 
v___x_4482__boxed_4234_ = lean_unbox(v___x_4221_);
v_res_4235_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0(v___x_4219_, v_fst_4220_, v___x_4482__boxed_4234_, v_a_4222_, v___x_4223_, v___x_4224_, v___x_4225_, v___x_4226_, v___x_4227_, v___x_4228_, v___x_4229_, v___x_4230_, v_snd_4231_, v___x_4232_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(lean_object* v_as_4239_, size_t v_sz_4240_, size_t v_i_4241_, lean_object* v_b_4242_){
_start:
{
lean_object* v_a_4244_; uint8_t v___x_4248_; 
v___x_4248_ = lean_usize_dec_lt(v_i_4241_, v_sz_4240_);
if (v___x_4248_ == 0)
{
lean_inc_ref(v_b_4242_);
return v_b_4242_;
}
else
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v_a_4251_; 
v___x_4249_ = lean_box(0);
v___x_4250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4251_ = lean_array_uget(v_as_4239_, v_i_4241_);
if (lean_obj_tag(v_a_4251_) == 1)
{
lean_object* v_i_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4286_; 
v_i_4252_ = lean_ctor_get(v_a_4251_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v_a_4251_);
if (v_isSharedCheck_4286_ == 0)
{
lean_object* v_unused_4287_; 
v_unused_4287_ = lean_ctor_get(v_a_4251_, 1);
lean_dec(v_unused_4287_);
v___x_4254_ = v_a_4251_;
v_isShared_4255_ = v_isSharedCheck_4286_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_i_4252_);
lean_dec(v_a_4251_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4286_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
if (lean_obj_tag(v_i_4252_) == 10)
{
lean_object* v_i_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4285_; 
v_i_4256_ = lean_ctor_get(v_i_4252_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v_i_4252_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4258_ = v_i_4252_;
v_isShared_4259_ = v_isSharedCheck_4285_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_i_4256_);
lean_dec(v_i_4252_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4285_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v_stx_4260_; lean_object* v_value_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4284_; 
v_stx_4260_ = lean_ctor_get(v_i_4256_, 0);
v_value_4261_ = lean_ctor_get(v_i_4256_, 1);
v_isSharedCheck_4284_ = !lean_is_exclusive(v_i_4256_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4263_ = v_i_4256_;
v_isShared_4264_ = v_isSharedCheck_4284_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_value_4261_);
lean_inc(v_stx_4260_);
lean_dec(v_i_4256_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4284_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4265_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4266_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4261_, v___x_4265_);
lean_dec(v_value_4261_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_del_object(v___x_4263_);
lean_dec(v_stx_4260_);
lean_del_object(v___x_4258_);
lean_del_object(v___x_4254_);
v_a_4244_ = v___x_4250_;
goto v___jp_4243_;
}
else
{
lean_object* v_val_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4283_; 
v_val_4267_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4269_ = v___x_4266_;
v_isShared_4270_ = v_isSharedCheck_4283_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_val_4267_);
lean_dec(v___x_4266_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4283_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 1, v_val_4267_);
v___x_4272_ = v___x_4263_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_stx_4260_);
lean_ctor_set(v_reuseFailAlloc_4282_, 1, v_val_4267_);
v___x_4272_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
lean_object* v___x_4274_; 
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 0, v___x_4272_);
v___x_4274_ = v___x_4269_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4272_);
v___x_4274_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
lean_object* v___x_4276_; 
if (v_isShared_4259_ == 0)
{
lean_ctor_set_tag(v___x_4258_, 1);
lean_ctor_set(v___x_4258_, 0, v___x_4274_);
v___x_4276_ = v___x_4258_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4274_);
v___x_4276_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
lean_object* v___x_4278_; 
if (v_isShared_4255_ == 0)
{
lean_ctor_set_tag(v___x_4254_, 0);
lean_ctor_set(v___x_4254_, 1, v___x_4249_);
lean_ctor_set(v___x_4254_, 0, v___x_4276_);
v___x_4278_ = v___x_4254_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4276_);
lean_ctor_set(v_reuseFailAlloc_4279_, 1, v___x_4249_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
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
lean_del_object(v___x_4254_);
lean_dec_ref(v_i_4252_);
v_a_4244_ = v___x_4250_;
goto v___jp_4243_;
}
}
}
else
{
lean_dec(v_a_4251_);
v_a_4244_ = v___x_4250_;
goto v___jp_4243_;
}
}
v___jp_4243_:
{
size_t v___x_4245_; size_t v___x_4246_; 
v___x_4245_ = ((size_t)1ULL);
v___x_4246_ = lean_usize_add(v_i_4241_, v___x_4245_);
v_i_4241_ = v___x_4246_;
v_b_4242_ = v_a_4244_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4288_, lean_object* v_sz_4289_, lean_object* v_i_4290_, lean_object* v_b_4291_){
_start:
{
size_t v_sz_boxed_4292_; size_t v_i_boxed_4293_; lean_object* v_res_4294_; 
v_sz_boxed_4292_ = lean_unbox_usize(v_sz_4289_);
lean_dec(v_sz_4289_);
v_i_boxed_4293_ = lean_unbox_usize(v_i_4290_);
lean_dec(v_i_4290_);
v_res_4294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4288_, v_sz_boxed_4292_, v_i_boxed_4293_, v_b_4291_);
lean_dec_ref(v_b_4291_);
lean_dec_ref(v_as_4288_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(lean_object* v_as_4295_, size_t v_sz_4296_, size_t v_i_4297_, lean_object* v_b_4298_){
_start:
{
lean_object* v_a_4300_; uint8_t v___x_4304_; 
v___x_4304_ = lean_usize_dec_lt(v_i_4297_, v_sz_4296_);
if (v___x_4304_ == 0)
{
lean_inc_ref(v_b_4298_);
return v_b_4298_;
}
else
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v_a_4307_; 
v___x_4305_ = lean_box(0);
v___x_4306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_a_4307_ = lean_array_uget(v_as_4295_, v_i_4297_);
if (lean_obj_tag(v_a_4307_) == 1)
{
lean_object* v_i_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4342_; 
v_i_4308_ = lean_ctor_get(v_a_4307_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v_a_4307_);
if (v_isSharedCheck_4342_ == 0)
{
lean_object* v_unused_4343_; 
v_unused_4343_ = lean_ctor_get(v_a_4307_, 1);
lean_dec(v_unused_4343_);
v___x_4310_ = v_a_4307_;
v_isShared_4311_ = v_isSharedCheck_4342_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_i_4308_);
lean_dec(v_a_4307_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4342_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
if (lean_obj_tag(v_i_4308_) == 10)
{
lean_object* v_i_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4341_; 
v_i_4312_ = lean_ctor_get(v_i_4308_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v_i_4308_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4314_ = v_i_4308_;
v_isShared_4315_ = v_isSharedCheck_4341_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_i_4312_);
lean_dec(v_i_4308_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4341_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v_stx_4316_; lean_object* v_value_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4340_; 
v_stx_4316_ = lean_ctor_get(v_i_4312_, 0);
v_value_4317_ = lean_ctor_get(v_i_4312_, 1);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_i_4312_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4319_ = v_i_4312_;
v_isShared_4320_ = v_isSharedCheck_4340_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_value_4317_);
lean_inc(v_stx_4316_);
lean_dec(v_i_4312_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4340_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_instImpl_00___x40_Lean_Elab_GuardMsgs_1707083452____hygCtx___hyg_8_));
v___x_4322_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_4317_, v___x_4321_);
lean_dec(v_value_4317_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_del_object(v___x_4319_);
lean_dec(v_stx_4316_);
lean_del_object(v___x_4314_);
lean_del_object(v___x_4310_);
v_a_4300_ = v___x_4306_;
goto v___jp_4299_;
}
else
{
lean_object* v_val_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4339_; 
v_val_4323_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4325_ = v___x_4322_;
v_isShared_4326_ = v_isSharedCheck_4339_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_val_4323_);
lean_dec(v___x_4322_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4339_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4320_ == 0)
{
lean_ctor_set(v___x_4319_, 1, v_val_4323_);
v___x_4328_ = v___x_4319_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_stx_4316_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v_val_4323_);
v___x_4328_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
lean_object* v___x_4330_; 
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 0, v___x_4328_);
v___x_4330_ = v___x_4325_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4328_);
v___x_4330_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
lean_object* v___x_4332_; 
if (v_isShared_4315_ == 0)
{
lean_ctor_set_tag(v___x_4314_, 1);
lean_ctor_set(v___x_4314_, 0, v___x_4330_);
v___x_4332_ = v___x_4314_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4330_);
v___x_4332_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
lean_object* v___x_4334_; 
if (v_isShared_4311_ == 0)
{
lean_ctor_set_tag(v___x_4310_, 0);
lean_ctor_set(v___x_4310_, 1, v___x_4305_);
lean_ctor_set(v___x_4310_, 0, v___x_4332_);
v___x_4334_ = v___x_4310_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4332_);
lean_ctor_set(v_reuseFailAlloc_4335_, 1, v___x_4305_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
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
lean_del_object(v___x_4310_);
lean_dec_ref(v_i_4308_);
v_a_4300_ = v___x_4306_;
goto v___jp_4299_;
}
}
}
else
{
lean_dec(v_a_4307_);
v_a_4300_ = v___x_4306_;
goto v___jp_4299_;
}
}
v___jp_4299_:
{
size_t v___x_4301_; size_t v___x_4302_; lean_object* v___x_4303_; 
v___x_4301_ = ((size_t)1ULL);
v___x_4302_ = lean_usize_add(v_i_4297_, v___x_4301_);
v___x_4303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4(v_as_4295_, v_sz_4296_, v___x_4302_, v_a_4300_);
return v___x_4303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1___boxed(lean_object* v_as_4344_, lean_object* v_sz_4345_, lean_object* v_i_4346_, lean_object* v_b_4347_){
_start:
{
size_t v_sz_boxed_4348_; size_t v_i_boxed_4349_; lean_object* v_res_4350_; 
v_sz_boxed_4348_ = lean_unbox_usize(v_sz_4345_);
lean_dec(v_sz_4345_);
v_i_boxed_4349_ = lean_unbox_usize(v_i_4346_);
lean_dec(v_i_4346_);
v_res_4350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_as_4344_, v_sz_boxed_4348_, v_i_boxed_4349_, v_b_4347_);
lean_dec_ref(v_b_4347_);
lean_dec_ref(v_as_4344_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(lean_object* v_x_4351_){
_start:
{
if (lean_obj_tag(v_x_4351_) == 0)
{
lean_object* v_cs_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; size_t v_sz_4355_; size_t v___x_4356_; lean_object* v___x_4357_; lean_object* v_fst_4358_; 
v_cs_4352_ = lean_ctor_get(v_x_4351_, 0);
v___x_4353_ = lean_box(0);
v___x_4354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4355_ = lean_array_size(v_cs_4352_);
v___x_4356_ = ((size_t)0ULL);
v___x_4357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_cs_4352_, v_sz_4355_, v___x_4356_, v___x_4354_);
v_fst_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_fst_4358_);
lean_dec_ref(v___x_4357_);
if (lean_obj_tag(v_fst_4358_) == 0)
{
return v___x_4353_;
}
else
{
lean_object* v_val_4359_; 
v_val_4359_ = lean_ctor_get(v_fst_4358_, 0);
lean_inc(v_val_4359_);
lean_dec_ref_known(v_fst_4358_, 1);
return v_val_4359_;
}
}
else
{
lean_object* v_vs_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; size_t v_sz_4363_; size_t v___x_4364_; lean_object* v___x_4365_; lean_object* v_fst_4366_; 
v_vs_4360_ = lean_ctor_get(v_x_4351_, 0);
v___x_4361_ = lean_box(0);
v___x_4362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4363_ = lean_array_size(v_vs_4360_);
v___x_4364_ = ((size_t)0ULL);
v___x_4365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_vs_4360_, v_sz_4363_, v___x_4364_, v___x_4362_);
v_fst_4366_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_fst_4366_);
lean_dec_ref(v___x_4365_);
if (lean_obj_tag(v_fst_4366_) == 0)
{
return v___x_4361_;
}
else
{
lean_object* v_val_4367_; 
v_val_4367_ = lean_ctor_get(v_fst_4366_, 0);
lean_inc(v_val_4367_);
lean_dec_ref_known(v_fst_4366_, 1);
return v_val_4367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(lean_object* v_as_4368_, size_t v_sz_4369_, size_t v_i_4370_, lean_object* v_b_4371_){
_start:
{
uint8_t v___x_4372_; 
v___x_4372_ = lean_usize_dec_lt(v_i_4370_, v_sz_4369_);
if (v___x_4372_ == 0)
{
lean_inc_ref(v_b_4371_);
return v_b_4371_;
}
else
{
lean_object* v___x_4373_; lean_object* v_a_4374_; lean_object* v___x_4375_; 
v___x_4373_ = lean_box(0);
v_a_4374_ = lean_array_uget_borrowed(v_as_4368_, v_i_4370_);
v___x_4375_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_a_4374_);
if (lean_obj_tag(v___x_4375_) == 1)
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
v___x_4377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
lean_ctor_set(v___x_4377_, 1, v___x_4373_);
return v___x_4377_;
}
else
{
lean_object* v___x_4378_; size_t v___x_4379_; size_t v___x_4380_; 
lean_dec(v___x_4375_);
v___x_4378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v___x_4379_ = ((size_t)1ULL);
v___x_4380_ = lean_usize_add(v_i_4370_, v___x_4379_);
v_i_4370_ = v___x_4380_;
v_b_4371_ = v___x_4378_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4382_, lean_object* v_sz_4383_, lean_object* v_i_4384_, lean_object* v_b_4385_){
_start:
{
size_t v_sz_boxed_4386_; size_t v_i_boxed_4387_; lean_object* v_res_4388_; 
v_sz_boxed_4386_ = lean_unbox_usize(v_sz_4383_);
lean_dec(v_sz_4383_);
v_i_boxed_4387_ = lean_unbox_usize(v_i_4384_);
lean_dec(v_i_4384_);
v_res_4388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0_spec__2(v_as_4382_, v_sz_boxed_4386_, v_i_boxed_4387_, v_b_4385_);
lean_dec_ref(v_b_4385_);
lean_dec_ref(v_as_4382_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0___boxed(lean_object* v_x_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_x_4389_);
lean_dec_ref(v_x_4389_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(lean_object* v_t_4391_){
_start:
{
lean_object* v_root_4392_; lean_object* v_tail_4393_; lean_object* v___x_4394_; 
v_root_4392_ = lean_ctor_get(v_t_4391_, 0);
v_tail_4393_ = lean_ctor_get(v_t_4391_, 1);
v___x_4394_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__0(v_root_4392_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v___x_4395_; size_t v_sz_4396_; size_t v___x_4397_; lean_object* v___x_4398_; lean_object* v_fst_4399_; 
v___x_4395_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1_spec__4___closed__0));
v_sz_4396_ = lean_array_size(v_tail_4393_);
v___x_4397_ = ((size_t)0ULL);
v___x_4398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0_spec__1(v_tail_4393_, v_sz_4396_, v___x_4397_, v___x_4395_);
v_fst_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_fst_4399_);
lean_dec_ref(v___x_4398_);
if (lean_obj_tag(v_fst_4399_) == 0)
{
return v___x_4394_;
}
else
{
lean_object* v_val_4400_; 
v_val_4400_ = lean_ctor_get(v_fst_4399_, 0);
lean_inc(v_val_4400_);
lean_dec_ref_known(v_fst_4399_, 1);
return v_val_4400_;
}
}
else
{
return v___x_4394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0___boxed(lean_object* v_t_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_t_4401_);
lean_dec_ref(v_t_4401_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(lean_object* v_node_4417_, lean_object* v_a_4418_){
_start:
{
if (lean_obj_tag(v_node_4417_) == 1)
{
lean_object* v_children_4420_; lean_object* v_res_4421_; 
v_children_4420_ = lean_ctor_get(v_node_4417_, 1);
v_res_4421_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__0(v_children_4420_);
if (lean_obj_tag(v_res_4421_) == 1)
{
lean_object* v_val_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4459_; 
v_val_4422_ = lean_ctor_get(v_res_4421_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v_res_4421_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4424_ = v_res_4421_;
v_isShared_4425_ = v_isSharedCheck_4459_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_val_4422_);
lean_dec(v_res_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4459_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v_fst_4426_; lean_object* v_snd_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4458_; 
v_fst_4426_ = lean_ctor_get(v_val_4422_, 0);
v_snd_4427_ = lean_ctor_get(v_val_4422_, 1);
v_isSharedCheck_4458_ = !lean_is_exclusive(v_val_4422_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4429_ = v_val_4422_;
v_isShared_4430_ = v_isSharedCheck_4458_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_snd_4427_);
lean_inc(v_fst_4426_);
lean_dec(v_val_4422_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4458_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4431_; lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4457_; 
v___x_4431_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__1(v_a_4418_);
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4434_ = v___x_4431_;
v_isShared_4435_ = v_isSharedCheck_4457_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4431_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4457_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; uint8_t v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___y_4444_; lean_object* v___x_4446_; 
v___x_4436_ = lean_box(0);
v___x_4437_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__0));
v___x_4438_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__2));
v___x_4439_ = 1;
v___x_4440_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__3));
v___x_4441_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__4));
v___x_4442_ = l_Lean_Syntax_getPos_x3f(v_fst_4426_, v___x_4439_);
v___x_4443_ = lean_box(v___x_4439_);
v___y_4444_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___y_4444_, 0, v___x_4442_);
lean_closure_set(v___y_4444_, 1, v_fst_4426_);
lean_closure_set(v___y_4444_, 2, v___x_4443_);
lean_closure_set(v___y_4444_, 3, v_a_4432_);
lean_closure_set(v___y_4444_, 4, v___x_4436_);
lean_closure_set(v___y_4444_, 5, v___x_4437_);
lean_closure_set(v___y_4444_, 6, v___x_4438_);
lean_closure_set(v___y_4444_, 7, v___x_4436_);
lean_closure_set(v___y_4444_, 8, v___x_4440_);
lean_closure_set(v___y_4444_, 9, v___x_4436_);
lean_closure_set(v___y_4444_, 10, v___x_4436_);
lean_closure_set(v___y_4444_, 11, v___x_4436_);
lean_closure_set(v___y_4444_, 12, v_snd_4427_);
lean_closure_set(v___y_4444_, 13, v___x_4441_);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___y_4444_);
v___x_4446_ = v___x_4424_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___y_4444_);
v___x_4446_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
lean_object* v___x_4448_; 
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 1, v___x_4446_);
lean_ctor_set(v___x_4429_, 0, v___x_4441_);
v___x_4448_ = v___x_4429_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4441_);
lean_ctor_set(v_reuseFailAlloc_4455_, 1, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4453_; 
v___x_4449_ = lean_unsigned_to_nat(1u);
v___x_4450_ = lean_mk_empty_array_with_capacity(v___x_4449_);
v___x_4451_ = lean_array_push(v___x_4450_, v___x_4448_);
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 0, v___x_4451_);
v___x_4453_ = v___x_4434_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4451_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
return v___x_4453_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4460_; lean_object* v___x_4461_; 
lean_dec(v_res_4421_);
v___x_4460_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
return v___x_4461_;
}
}
else
{
lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4462_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___closed__5));
v___x_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4462_);
return v___x_4463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg___boxed(lean_object* v_node_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4464_, v_a_4465_);
lean_dec_ref(v_a_4465_);
lean_dec_ref(v_node_4464_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(lean_object* v_x_4468_, lean_object* v_x_4469_, lean_object* v_x_4470_, lean_object* v_node_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v___x_4474_; 
v___x_4474_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___redArg(v_node_4471_, v_a_4472_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed(lean_object* v_x_4475_, lean_object* v_x_4476_, lean_object* v_x_4477_, lean_object* v_node_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_){
_start:
{
lean_object* v_res_4481_; 
v_res_4481_ = l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction(v_x_4475_, v_x_4476_, v_x_4477_, v_node_4478_, v_a_4479_);
lean_dec_ref(v_a_4479_);
lean_dec_ref(v_node_4478_);
lean_dec_ref(v_x_4477_);
lean_dec_ref(v_x_4476_);
lean_dec_ref(v_x_4475_);
return v_res_4481_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(lean_object* v_s_4482_, lean_object* v_inst_4483_, lean_object* v_R_4484_, lean_object* v_a_4485_, uint8_t v_b_4486_, lean_object* v_c_4487_){
_start:
{
uint8_t v___x_4488_; 
v___x_4488_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___redArg(v_s_4482_, v_a_4485_, v_b_4486_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4___boxed(lean_object* v_s_4489_, lean_object* v_inst_4490_, lean_object* v_R_4491_, lean_object* v_a_4492_, lean_object* v_b_4493_, lean_object* v_c_4494_){
_start:
{
uint8_t v_b_boxed_4495_; uint8_t v_res_4496_; lean_object* v_r_4497_; 
v_b_boxed_4495_ = lean_unbox(v_b_4493_);
v_res_4496_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_spec__2_spec__4(v_s_4489_, v_inst_4490_, v_R_4491_, v_a_4492_, v_b_boxed_4495_, v_c_4494_);
lean_dec_ref(v_s_4489_);
v_r_4497_ = lean_box(v_res_4496_);
return v_r_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_(){
_start:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4503_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1___closed__0_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_));
v___x_4504_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___boxed), 6, 0);
v___x_4505_ = l_Lean_CodeAction_insertBuiltin(v___x_4503_, v___x_4504_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354____boxed(lean_object* v_a_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction___regBuiltin_Lean_Elab_Tactic_GuardMsgs_guardMsgsCodeAction_declare__1_00___x40_Lean_Elab_GuardMsgs_1904941021____hygCtx___hyg_354_();
return v_res_4507_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4513_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4514_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_4513_);
return v___x_4514_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4515_ = lean_unsigned_to_nat(0u);
v___x_4516_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__2);
v___x_4517_ = ((lean_object*)(l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__1));
v___x_4518_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
lean_ctor_set(v___x_4518_, 1, v___x_4516_);
lean_ctor_set(v___x_4518_, 2, v___x_4515_);
lean_ctor_set(v___x_4518_, 3, v___x_4515_);
return v___x_4518_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(lean_object* v_s_4519_){
_start:
{
lean_object* v___x_4520_; uint8_t v___x_4521_; uint8_t v___x_4522_; 
v___x_4520_ = lean_obj_once(&l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3, &l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___closed__3);
v___x_4521_ = 0;
v___x_4522_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__9_spec__21___redArg(v_s_4519_, v___x_4520_, v___x_4521_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0___boxed(lean_object* v_s_4523_){
_start:
{
uint8_t v_res_4524_; lean_object* v_r_4525_; 
v_res_4524_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v_s_4523_);
lean_dec_ref(v_s_4523_);
v_r_4525_ = lean_box(v_res_4524_);
return v_r_4525_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(uint8_t v_foundPanic_4526_, lean_object* v_as_x27_4527_, uint8_t v_b_4528_){
_start:
{
if (lean_obj_tag(v_as_x27_4527_) == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4530_ = lean_box(v_b_4528_);
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
return v___x_4531_;
}
else
{
lean_object* v_head_4532_; uint8_t v_isSilent_4533_; 
v_head_4532_ = lean_ctor_get(v_as_x27_4527_, 0);
v_isSilent_4533_ = lean_ctor_get_uint8(v_head_4532_, sizeof(void*)*5 + 2);
if (v_isSilent_4533_ == 0)
{
lean_object* v_tail_4534_; lean_object* v_data_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; uint8_t v___x_4540_; 
v_tail_4534_ = lean_ctor_get(v_as_x27_4527_, 1);
v_data_4535_ = lean_ctor_get(v_head_4532_, 4);
lean_inc(v_data_4535_);
v___x_4536_ = l_Lean_MessageData_toString(v_data_4535_);
v___x_4537_ = lean_unsigned_to_nat(0u);
v___x_4538_ = lean_string_utf8_byte_size(v___x_4536_);
v___x_4539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4536_);
lean_ctor_set(v___x_4539_, 1, v___x_4537_);
lean_ctor_set(v___x_4539_, 2, v___x_4538_);
v___x_4540_ = l_String_Slice_contains___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__0(v___x_4539_);
lean_dec_ref_known(v___x_4539_, 3);
if (v___x_4540_ == 0)
{
v_as_x27_4527_ = v_tail_4534_;
goto _start;
}
else
{
lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4542_ = lean_box(v_foundPanic_4526_);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
return v___x_4543_;
}
}
else
{
lean_object* v_tail_4544_; 
v_tail_4544_ = lean_ctor_get(v_as_x27_4527_, 1);
v_as_x27_4527_ = v_tail_4544_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg___boxed(lean_object* v_foundPanic_4546_, lean_object* v_as_x27_4547_, lean_object* v_b_4548_, lean_object* v___y_4549_){
_start:
{
uint8_t v_foundPanic_boxed_4550_; uint8_t v_b_boxed_4551_; lean_object* v_res_4552_; 
v_foundPanic_boxed_4550_ = lean_unbox(v_foundPanic_4546_);
v_b_boxed_4551_ = lean_unbox(v_b_4548_);
v_res_4552_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_boxed_4550_, v_as_x27_4547_, v_b_boxed_4551_);
lean_dec(v_as_x27_4547_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(lean_object* v_msgData_4553_, uint8_t v_severity_4554_, uint8_t v_isSilent_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l_Lean_Elab_Command_getRef___redArg(v___y_4556_);
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_object* v_a_4560_; lean_object* v___x_4561_; 
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
lean_inc(v_a_4560_);
lean_dec_ref_known(v___x_4559_, 1);
v___x_4561_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardMsgs_spec__2_spec__2(v_a_4560_, v_msgData_4553_, v_severity_4554_, v_isSilent_4555_, v___y_4556_, v___y_4557_);
lean_dec(v_a_4560_);
return v___x_4561_;
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec_ref(v_msgData_4553_);
v_a_4562_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4559_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4559_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2___boxed(lean_object* v_msgData_4570_, lean_object* v_severity_4571_, lean_object* v_isSilent_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
uint8_t v_severity_boxed_4576_; uint8_t v_isSilent_boxed_4577_; lean_object* v_res_4578_; 
v_severity_boxed_4576_ = lean_unbox(v_severity_4571_);
v_isSilent_boxed_4577_ = lean_unbox(v_isSilent_4572_);
v_res_4578_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4570_, v_severity_boxed_4576_, v_isSilent_boxed_4577_, v___y_4573_, v___y_4574_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(lean_object* v_msgData_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
uint8_t v___x_4583_; uint8_t v___x_4584_; lean_object* v___x_4585_; 
v___x_4583_ = 2;
v___x_4584_ = 0;
v___x_4585_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2_spec__2(v_msgData_4579_, v___x_4583_, v___x_4584_, v___y_4580_, v___y_4581_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2___boxed(lean_object* v_msgData_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v_msgData_4586_, v___y_4587_, v___y_4588_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
return v_res_4590_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4(void){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__3));
v___x_4599_ = l_Lean_MessageData_ofFormat(v___x_4598_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(lean_object* v_x_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_){
_start:
{
lean_object* v___x_4604_; uint8_t v_foundPanic_4605_; 
v___x_4604_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
lean_inc(v_x_4600_);
v_foundPanic_4605_ = l_Lean_Syntax_isOfKind(v_x_4600_, v___x_4604_);
if (v_foundPanic_4605_ == 0)
{
lean_object* v___x_4606_; 
lean_dec(v_x_4600_);
v___x_4606_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardMsgs_parseGuardMsgsFilterAction_spec__0___redArg();
return v___x_4606_;
}
else
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4607_ = lean_unsigned_to_nat(2u);
v___x_4608_ = l_Lean_Syntax_getArg(v_x_4600_, v___x_4607_);
lean_dec(v_x_4600_);
v___x_4609_ = l_Lean_Elab_Tactic_GuardMsgs_runAndCollectMessages(v___x_4608_, v_a_4601_, v_a_4602_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; uint8_t v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4670_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_a_4610_);
lean_dec_ref_known(v___x_4609_, 1);
v___x_4611_ = 0;
v___x_4612_ = l_Lean_MessageLog_toList(v_a_4610_);
v___x_4613_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4605_, v___x_4612_, v___x_4611_);
lean_dec(v___x_4612_);
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4670_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4670_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
uint8_t v___x_4618_; 
v___x_4618_ = lean_unbox(v_a_4614_);
lean_dec(v_a_4614_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; lean_object* v_env_4620_; lean_object* v_scopes_4621_; lean_object* v_usedQuotCtxts_4622_; lean_object* v_nextMacroScope_4623_; lean_object* v_maxRecDepth_4624_; lean_object* v_ngen_4625_; lean_object* v_auxDeclNGen_4626_; lean_object* v_infoState_4627_; lean_object* v_traceState_4628_; lean_object* v_snapshotTasks_4629_; lean_object* v_prevLinterStates_4630_; lean_object* v_codeQualityEntryTasks_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4641_; 
lean_del_object(v___x_4616_);
v___x_4619_ = lean_st_ref_take(v_a_4602_);
v_env_4620_ = lean_ctor_get(v___x_4619_, 0);
v_scopes_4621_ = lean_ctor_get(v___x_4619_, 2);
v_usedQuotCtxts_4622_ = lean_ctor_get(v___x_4619_, 3);
v_nextMacroScope_4623_ = lean_ctor_get(v___x_4619_, 4);
v_maxRecDepth_4624_ = lean_ctor_get(v___x_4619_, 5);
v_ngen_4625_ = lean_ctor_get(v___x_4619_, 6);
v_auxDeclNGen_4626_ = lean_ctor_get(v___x_4619_, 7);
v_infoState_4627_ = lean_ctor_get(v___x_4619_, 8);
v_traceState_4628_ = lean_ctor_get(v___x_4619_, 9);
v_snapshotTasks_4629_ = lean_ctor_get(v___x_4619_, 10);
v_prevLinterStates_4630_ = lean_ctor_get(v___x_4619_, 11);
v_codeQualityEntryTasks_4631_ = lean_ctor_get(v___x_4619_, 12);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4641_ == 0)
{
lean_object* v_unused_4642_; 
v_unused_4642_ = lean_ctor_get(v___x_4619_, 1);
lean_dec(v_unused_4642_);
v___x_4633_ = v___x_4619_;
v_isShared_4634_ = v_isSharedCheck_4641_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4631_);
lean_inc(v_prevLinterStates_4630_);
lean_inc(v_snapshotTasks_4629_);
lean_inc(v_traceState_4628_);
lean_inc(v_infoState_4627_);
lean_inc(v_auxDeclNGen_4626_);
lean_inc(v_ngen_4625_);
lean_inc(v_maxRecDepth_4624_);
lean_inc(v_nextMacroScope_4623_);
lean_inc(v_usedQuotCtxts_4622_);
lean_inc(v_scopes_4621_);
lean_inc(v_env_4620_);
lean_dec(v___x_4619_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4641_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
lean_ctor_set(v___x_4633_, 1, v_a_4610_);
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_env_4620_);
lean_ctor_set(v_reuseFailAlloc_4640_, 1, v_a_4610_);
lean_ctor_set(v_reuseFailAlloc_4640_, 2, v_scopes_4621_);
lean_ctor_set(v_reuseFailAlloc_4640_, 3, v_usedQuotCtxts_4622_);
lean_ctor_set(v_reuseFailAlloc_4640_, 4, v_nextMacroScope_4623_);
lean_ctor_set(v_reuseFailAlloc_4640_, 5, v_maxRecDepth_4624_);
lean_ctor_set(v_reuseFailAlloc_4640_, 6, v_ngen_4625_);
lean_ctor_set(v_reuseFailAlloc_4640_, 7, v_auxDeclNGen_4626_);
lean_ctor_set(v_reuseFailAlloc_4640_, 8, v_infoState_4627_);
lean_ctor_set(v_reuseFailAlloc_4640_, 9, v_traceState_4628_);
lean_ctor_set(v_reuseFailAlloc_4640_, 10, v_snapshotTasks_4629_);
lean_ctor_set(v_reuseFailAlloc_4640_, 11, v_prevLinterStates_4630_);
lean_ctor_set(v_reuseFailAlloc_4640_, 12, v_codeQualityEntryTasks_4631_);
v___x_4636_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4637_ = lean_st_ref_put(v_a_4602_, v___x_4636_);
v___x_4638_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4, &l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4_once, _init_l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__4);
v___x_4639_ = l_Lean_logError___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__2(v___x_4638_, v_a_4601_, v_a_4602_);
return v___x_4639_;
}
}
}
else
{
lean_object* v___x_4643_; lean_object* v_env_4644_; lean_object* v_scopes_4645_; lean_object* v_usedQuotCtxts_4646_; lean_object* v_nextMacroScope_4647_; lean_object* v_maxRecDepth_4648_; lean_object* v_ngen_4649_; lean_object* v_auxDeclNGen_4650_; lean_object* v_infoState_4651_; lean_object* v_traceState_4652_; lean_object* v_snapshotTasks_4653_; lean_object* v_prevLinterStates_4654_; lean_object* v_codeQualityEntryTasks_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4668_; 
lean_dec(v_a_4610_);
v___x_4643_ = lean_st_ref_take(v_a_4602_);
v_env_4644_ = lean_ctor_get(v___x_4643_, 0);
v_scopes_4645_ = lean_ctor_get(v___x_4643_, 2);
v_usedQuotCtxts_4646_ = lean_ctor_get(v___x_4643_, 3);
v_nextMacroScope_4647_ = lean_ctor_get(v___x_4643_, 4);
v_maxRecDepth_4648_ = lean_ctor_get(v___x_4643_, 5);
v_ngen_4649_ = lean_ctor_get(v___x_4643_, 6);
v_auxDeclNGen_4650_ = lean_ctor_get(v___x_4643_, 7);
v_infoState_4651_ = lean_ctor_get(v___x_4643_, 8);
v_traceState_4652_ = lean_ctor_get(v___x_4643_, 9);
v_snapshotTasks_4653_ = lean_ctor_get(v___x_4643_, 10);
v_prevLinterStates_4654_ = lean_ctor_get(v___x_4643_, 11);
v_codeQualityEntryTasks_4655_ = lean_ctor_get(v___x_4643_, 12);
v_isSharedCheck_4668_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4668_ == 0)
{
lean_object* v_unused_4669_; 
v_unused_4669_ = lean_ctor_get(v___x_4643_, 1);
lean_dec(v_unused_4669_);
v___x_4657_ = v___x_4643_;
v_isShared_4658_ = v_isSharedCheck_4668_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4655_);
lean_inc(v_prevLinterStates_4654_);
lean_inc(v_snapshotTasks_4653_);
lean_inc(v_traceState_4652_);
lean_inc(v_infoState_4651_);
lean_inc(v_auxDeclNGen_4650_);
lean_inc(v_ngen_4649_);
lean_inc(v_maxRecDepth_4648_);
lean_inc(v_nextMacroScope_4647_);
lean_inc(v_usedQuotCtxts_4646_);
lean_inc(v_scopes_4645_);
lean_inc(v_env_4644_);
lean_dec(v___x_4643_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4668_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4662_; 
v___x_4659_ = lean_box(0);
v___x_4660_ = l_Lean_MessageLog_empty;
if (v_isShared_4658_ == 0)
{
lean_ctor_set(v___x_4657_, 1, v___x_4660_);
v___x_4662_ = v___x_4657_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v_env_4644_);
lean_ctor_set(v_reuseFailAlloc_4667_, 1, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4667_, 2, v_scopes_4645_);
lean_ctor_set(v_reuseFailAlloc_4667_, 3, v_usedQuotCtxts_4646_);
lean_ctor_set(v_reuseFailAlloc_4667_, 4, v_nextMacroScope_4647_);
lean_ctor_set(v_reuseFailAlloc_4667_, 5, v_maxRecDepth_4648_);
lean_ctor_set(v_reuseFailAlloc_4667_, 6, v_ngen_4649_);
lean_ctor_set(v_reuseFailAlloc_4667_, 7, v_auxDeclNGen_4650_);
lean_ctor_set(v_reuseFailAlloc_4667_, 8, v_infoState_4651_);
lean_ctor_set(v_reuseFailAlloc_4667_, 9, v_traceState_4652_);
lean_ctor_set(v_reuseFailAlloc_4667_, 10, v_snapshotTasks_4653_);
lean_ctor_set(v_reuseFailAlloc_4667_, 11, v_prevLinterStates_4654_);
lean_ctor_set(v_reuseFailAlloc_4667_, 12, v_codeQualityEntryTasks_4655_);
v___x_4662_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
lean_object* v___x_4663_; lean_object* v___x_4665_; 
v___x_4663_ = lean_st_ref_put(v_a_4602_, v___x_4662_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4659_);
v___x_4665_ = v___x_4616_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4659_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
}
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
v_a_4671_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4609_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4609_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed(lean_object* v_x_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic(v_x_4679_, v_a_4680_, v_a_4681_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(uint8_t v_foundPanic_4684_, lean_object* v_as_4685_, lean_object* v_as_x27_4686_, uint8_t v_b_4687_, lean_object* v_a_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v___x_4692_; 
v___x_4692_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___redArg(v_foundPanic_4684_, v_as_x27_4686_, v_b_4687_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1___boxed(lean_object* v_foundPanic_4693_, lean_object* v_as_4694_, lean_object* v_as_x27_4695_, lean_object* v_b_4696_, lean_object* v_a_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
uint8_t v_foundPanic_boxed_4701_; uint8_t v_b_boxed_4702_; lean_object* v_res_4703_; 
v_foundPanic_boxed_4701_ = lean_unbox(v_foundPanic_4693_);
v_b_boxed_4702_ = lean_unbox(v_b_4696_);
v_res_4703_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_GuardMsgs_elabGuardPanic_spec__1(v_foundPanic_boxed_4701_, v_as_4694_, v_as_x27_4695_, v_b_boxed_4702_, v_a_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v_as_x27_4695_);
lean_dec(v_as_4694_);
return v_res_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1(){
_start:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4712_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4713_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___closed__1));
v___x_4714_ = ((lean_object*)(l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___closed__1));
v___x_4715_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___boxed), 4, 0);
v___x_4716_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4712_, v___x_4713_, v___x_4714_, v___x_4715_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1___boxed(lean_object* v_a_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l___private_Lean_Elab_GuardMsgs_0__Lean_Elab_Tactic_GuardMsgs_elabGuardPanic___regBuiltin_Lean_Elab_Tactic_GuardMsgs_elabGuardPanic__1();
return v_res_4718_;
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
