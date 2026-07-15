// Lean compiler output
// Module: Lean.PostprocessTraces.Basic
// Imports: public meta import Lean.Elab.Command public meta import Lean.Meta.Eval import Lean.CoreM
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
double lean_float_of_nat(lean_object*);
uint8_t lean_float_beq(double, double);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLe(double, double);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
double lean_float_add(double, double);
double lean_float_mul(double, double);
double round(double);
uint64_t lean_float_to_uint64(double);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
uint8_t l_Lean_instBEqTraceResult_beq(uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toArray(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "PostprocessTraces"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__1 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__1_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "postprocessTracesCmd"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__2 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__2_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value_aux_0),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value_aux_1),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 16, 235, 102, 51, 61, 86, 237)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__4 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__4_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "postprocess_traces "};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__6 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__6_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__6_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__7 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__7_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__8 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__8_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__9 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__9_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__10 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__10_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__7_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__10_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__11 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__11_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " in"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__12 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__12_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__12_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__13 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__13_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__11_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__13_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__14 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__14_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__15 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__15_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__15_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__16 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__16_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__16_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__17 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__17_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__14_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__17_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__18 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__18_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__19 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__19_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__19_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__20 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__20_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__21 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__21_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__18_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__21_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__22 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__22_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__22_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__23 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__23_value;
LEAN_EXPORT const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__23_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_node_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTraceTree;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor = (const lean_object*)&l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___closed__0_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___closed__1 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2;
static const lean_array_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__3 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "open"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__2 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__2_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3_value_aux_2),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 46, 79, 112, 232, 100, 17, 35)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openSimple"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__5 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__5_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6_value_aux_2),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__5_value),LEAN_SCALAR_PTR_LITERAL(171, 238, 134, 92, 162, 110, 43, 67)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__8 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__8_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.PostprocessTraces"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__9 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__9_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11_value_aux_0),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11_value)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__12 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__12_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__14 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__14_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16_value_aux_2),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__17 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__17_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_2),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__17_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__19 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__19_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__21 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__21_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__22 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__22_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_value_aux_1),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(131, 135, 26, 65, 16, 127, 78, 49)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_value)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__26 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__26_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__28 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__28_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__28_value),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13_value)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__26_value),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29_value)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__30 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__30_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__31 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__31_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "TracePostprocessor"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32_value),LEAN_SCALAR_PTR_LITERAL(251, 174, 159, 176, 196, 77, 180, 200)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_value_aux_0),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32_value),LEAN_SCALAR_PTR_LITERAL(33, 98, 63, 149, 37, 148, 219, 124)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__36 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__36_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__38 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__38_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception: "};
static const lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0 = (const lean_object*)&l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f___boxed(lean_object*);
static const lean_array_object l_Lean_PostprocessTraces_TraceTree_children___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PostprocessTraces_TraceTree_children___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_TraceTree_children___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_withChildren(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_modifyData(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0;
LEAN_EXPORT double l_Lean_PostprocessTraces_TraceTree_elapsed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_elapsed___boxed(lean_object*);
LEAN_EXPORT double l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(lean_object*, size_t, size_t, double);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT double l_Lean_PostprocessTraces_TraceTree_selfElapsed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_selfElapsed___boxed(lean_object*);
static const lean_string_object l_Lean_PostprocessTraces_TraceTree_headText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_PostprocessTraces_TraceTree_headText___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_TraceTree_headText___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr___closed__0 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_PostprocessTraces_succeeded___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_succeeded___redArg___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_succeeded___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_PostprocessTraces_failed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_failed___redArg___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_failed___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_PostprocessTraces_errored___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_errored___redArg___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_errored___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg(double, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs(double, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg(double, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs(double, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_filterSubtrees(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_filterSubtrees___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_hoist(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_hoist___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_exposeSubtrees(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_exposeSubtrees___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__0 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__0_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__1;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " node"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__2 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__2_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__3;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__4;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__5 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__0;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__1 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__1_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ms"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__2 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs(double);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___boxed(lean_object*);
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " (self: "};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go___closed__0 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go___closed__0_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx(lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v___x_56_; 
v___x_56_ = lean_unsigned_to_nat(0u);
return v___x_56_;
}
else
{
lean_object* v___x_57_; 
v___x_57_ = lean_unsigned_to_nat(1u);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx___boxed(lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_PostprocessTraces_TraceTree_ctorIdx(v_x_58_);
lean_dec_ref(v_x_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(lean_object* v_t_60_, lean_object* v_k_61_){
_start:
{
if (lean_obj_tag(v_t_60_) == 0)
{
lean_object* v_data_62_; lean_object* v_msg_63_; lean_object* v_children_64_; lean_object* v_wrap_65_; lean_object* v___x_66_; 
v_data_62_ = lean_ctor_get(v_t_60_, 0);
lean_inc_ref(v_data_62_);
v_msg_63_ = lean_ctor_get(v_t_60_, 1);
lean_inc_ref(v_msg_63_);
v_children_64_ = lean_ctor_get(v_t_60_, 2);
lean_inc_ref(v_children_64_);
v_wrap_65_ = lean_ctor_get(v_t_60_, 3);
lean_inc_ref(v_wrap_65_);
lean_dec_ref_known(v_t_60_, 4);
v___x_66_ = lean_apply_4(v_k_61_, v_data_62_, v_msg_63_, v_children_64_, v_wrap_65_);
return v___x_66_;
}
else
{
lean_object* v_msg_67_; lean_object* v___x_68_; 
v_msg_67_ = lean_ctor_get(v_t_60_, 0);
lean_inc_ref(v_msg_67_);
lean_dec_ref_known(v_t_60_, 1);
v___x_68_ = lean_apply_1(v_k_61_, v_msg_67_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim(lean_object* v_motive__1_69_, lean_object* v_ctorIdx_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_k_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_71_, v_k_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim___boxed(lean_object* v_motive__1_75_, lean_object* v_ctorIdx_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_k_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_PostprocessTraces_TraceTree_ctorElim(v_motive__1_75_, v_ctorIdx_76_, v_t_77_, v_h_78_, v_k_79_);
lean_dec(v_ctorIdx_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_node_elim___redArg(lean_object* v_t_81_, lean_object* v_node_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_81_, v_node_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_node_elim(lean_object* v_motive__1_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_node_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_85_, v_node_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_leaf_elim___redArg(lean_object* v_t_89_, lean_object* v_leaf_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_89_, v_leaf_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_leaf_elim(lean_object* v_motive__1_92_, lean_object* v_t_93_, lean_object* v_h_94_, lean_object* v_leaf_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_93_, v_leaf_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = l_Lean_MessageData_nil;
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_instInhabitedTraceTree(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0, &l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0_once, _init_l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0(lean_object* v_a_100_, lean_object* v_wrap_101_, lean_object* v_m_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_103_, 0, v_a_100_);
lean_ctor_set(v___x_103_, 1, v_m_102_);
v___x_104_ = lean_apply_1(v_wrap_101_, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1(lean_object* v_a_105_, lean_object* v_wrap_106_, lean_object* v_m_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_108_, 0, v_a_105_);
lean_ctor_set(v___x_108_, 1, v_m_107_);
v___x_109_ = lean_apply_1(v_wrap_106_, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0(lean_object* v___y_110_){
_start:
{
lean_inc_ref(v___y_110_);
return v___y_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0___boxed(lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0(v___y_111_);
lean_dec_ref(v___y_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go(lean_object* v_wrap_114_, lean_object* v_a_115_){
_start:
{
switch(lean_obj_tag(v_a_115_))
{
case 3:
{
lean_object* v_a_116_; lean_object* v_a_117_; lean_object* v___f_118_; 
v_a_116_ = lean_ctor_get(v_a_115_, 0);
lean_inc_ref(v_a_116_);
v_a_117_ = lean_ctor_get(v_a_115_, 1);
lean_inc_ref(v_a_117_);
lean_dec_ref_known(v_a_115_, 2);
v___f_118_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0), 3, 2);
lean_closure_set(v___f_118_, 0, v_a_116_);
lean_closure_set(v___f_118_, 1, v_wrap_114_);
v_wrap_114_ = v___f_118_;
v_a_115_ = v_a_117_;
goto _start;
}
case 4:
{
lean_object* v_a_120_; lean_object* v_a_121_; lean_object* v___f_122_; 
v_a_120_ = lean_ctor_get(v_a_115_, 0);
lean_inc_ref(v_a_120_);
v_a_121_ = lean_ctor_get(v_a_115_, 1);
lean_inc_ref(v_a_121_);
lean_dec_ref_known(v_a_115_, 2);
v___f_122_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1), 3, 2);
lean_closure_set(v___f_122_, 0, v_a_120_);
lean_closure_set(v___f_122_, 1, v_wrap_114_);
v_wrap_114_ = v___f_122_;
v_a_115_ = v_a_121_;
goto _start;
}
case 9:
{
lean_object* v_data_124_; lean_object* v_msg_125_; lean_object* v_children_126_; size_t v_sz_127_; size_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_data_124_ = lean_ctor_get(v_a_115_, 0);
lean_inc_ref(v_data_124_);
v_msg_125_ = lean_ctor_get(v_a_115_, 1);
lean_inc_ref(v_msg_125_);
v_children_126_ = lean_ctor_get(v_a_115_, 2);
lean_inc_ref(v_children_126_);
lean_dec_ref_known(v_a_115_, 3);
v_sz_127_ = lean_array_size(v_children_126_);
v___x_128_ = ((size_t)0ULL);
v___x_129_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(v_sz_127_, v___x_128_, v_children_126_);
v___x_130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_130_, 0, v_data_124_);
lean_ctor_set(v___x_130_, 1, v_msg_125_);
lean_ctor_set(v___x_130_, 2, v___x_129_);
lean_ctor_set(v___x_130_, 3, v_wrap_114_);
return v___x_130_;
}
default: 
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_apply_1(v_wrap_114_, v_a_115_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(size_t v_sz_133_, size_t v_i_134_, lean_object* v_bs_135_){
_start:
{
uint8_t v___x_136_; 
v___x_136_ = lean_usize_dec_lt(v_i_134_, v_sz_133_);
if (v___x_136_ == 0)
{
return v_bs_135_;
}
else
{
lean_object* v___f_137_; lean_object* v_v_138_; lean_object* v___x_139_; lean_object* v_bs_x27_140_; lean_object* v___x_141_; size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; 
v___f_137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___closed__0));
v_v_138_ = lean_array_uget(v_bs_135_, v_i_134_);
v___x_139_ = lean_unsigned_to_nat(0u);
v_bs_x27_140_ = lean_array_uset(v_bs_135_, v_i_134_, v___x_139_);
v___x_141_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go(v___f_137_, v_v_138_);
v___x_142_ = ((size_t)1ULL);
v___x_143_ = lean_usize_add(v_i_134_, v___x_142_);
v___x_144_ = lean_array_uset(v_bs_x27_140_, v_i_134_, v___x_141_);
v_i_134_ = v___x_143_;
v_bs_135_ = v___x_144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___boxed(lean_object* v_sz_146_, lean_object* v_i_147_, lean_object* v_bs_148_){
_start:
{
size_t v_sz_boxed_149_; size_t v_i_boxed_150_; lean_object* v_res_151_; 
v_sz_boxed_149_ = lean_unbox_usize(v_sz_146_);
lean_dec(v_sz_146_);
v_i_boxed_150_ = lean_unbox_usize(v_i_147_);
lean_dec(v_i_147_);
v_res_151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(v_sz_boxed_149_, v_i_boxed_150_, v_bs_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0(lean_object* v___y_152_){
_start:
{
lean_inc_ref(v___y_152_);
return v___y_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0___boxed(lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0(v___y_153_);
lean_dec_ref(v___y_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData(lean_object* v_msg_156_){
_start:
{
lean_object* v___f_157_; lean_object* v___x_158_; 
v___f_157_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0));
v___x_158_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go(v___f_157_, v_msg_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(size_t v_sz_159_, size_t v_i_160_, lean_object* v_bs_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = lean_usize_dec_lt(v_i_160_, v_sz_159_);
if (v___x_162_ == 0)
{
return v_bs_161_;
}
else
{
lean_object* v_v_163_; lean_object* v___x_164_; lean_object* v_bs_x27_165_; lean_object* v___x_166_; size_t v___x_167_; size_t v___x_168_; lean_object* v___x_169_; 
v_v_163_ = lean_array_uget(v_bs_161_, v_i_160_);
v___x_164_ = lean_unsigned_to_nat(0u);
v_bs_x27_165_ = lean_array_uset(v_bs_161_, v_i_160_, v___x_164_);
v___x_166_ = l_Lean_PostprocessTraces_TraceTree_toMessageData(v_v_163_);
v___x_167_ = ((size_t)1ULL);
v___x_168_ = lean_usize_add(v_i_160_, v___x_167_);
v___x_169_ = lean_array_uset(v_bs_x27_165_, v_i_160_, v___x_166_);
v_i_160_ = v___x_168_;
v_bs_161_ = v___x_169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_toMessageData(lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_171_) == 0)
{
lean_object* v_data_172_; lean_object* v_msg_173_; lean_object* v_children_174_; lean_object* v_wrap_175_; size_t v_sz_176_; size_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_data_172_ = lean_ctor_get(v_x_171_, 0);
lean_inc_ref(v_data_172_);
v_msg_173_ = lean_ctor_get(v_x_171_, 1);
lean_inc_ref(v_msg_173_);
v_children_174_ = lean_ctor_get(v_x_171_, 2);
lean_inc_ref(v_children_174_);
v_wrap_175_ = lean_ctor_get(v_x_171_, 3);
lean_inc_ref(v_wrap_175_);
lean_dec_ref_known(v_x_171_, 4);
v_sz_176_ = lean_array_size(v_children_174_);
v___x_177_ = ((size_t)0ULL);
v___x_178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_176_, v___x_177_, v_children_174_);
v___x_179_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_179_, 0, v_data_172_);
lean_ctor_set(v___x_179_, 1, v_msg_173_);
lean_ctor_set(v___x_179_, 2, v___x_178_);
v___x_180_ = lean_apply_1(v_wrap_175_, v___x_179_);
return v___x_180_;
}
else
{
lean_object* v_msg_181_; 
v_msg_181_ = lean_ctor_get(v_x_171_, 0);
lean_inc_ref(v_msg_181_);
lean_dec_ref_known(v_x_171_, 1);
return v_msg_181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0___boxed(lean_object* v_sz_182_, lean_object* v_i_183_, lean_object* v_bs_184_){
_start:
{
size_t v_sz_boxed_185_; size_t v_i_boxed_186_; lean_object* v_res_187_; 
v_sz_boxed_185_ = lean_unbox_usize(v_sz_182_);
lean_dec(v_sz_182_);
v_i_boxed_186_ = lean_unbox_usize(v_i_183_);
lean_dec(v_i_183_);
v_res_187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_boxed_185_, v_i_boxed_186_, v_bs_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0(lean_object* v_roots_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v_roots_188_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0___boxed(lean_object* v_roots_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0(v_roots_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___lam__2(lean_object* v_data_200_, lean_object* v_msg_201_, lean_object* v_a_202_, lean_object* v_wrap_203_, lean_object* v_children_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_205_, 0, v_data_200_);
lean_ctor_set(v___x_205_, 1, v_msg_201_);
lean_ctor_set(v___x_205_, 2, v_children_204_);
v___x_206_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_206_, 0, v_a_202_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_apply_1(v_wrap_203_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go(lean_object* v_wrap_211_, lean_object* v_a_212_){
_start:
{
switch(lean_obj_tag(v_a_212_))
{
case 3:
{
lean_object* v_a_213_; lean_object* v_a_214_; lean_object* v___f_215_; 
v_a_213_ = lean_ctor_get(v_a_212_, 0);
lean_inc_ref(v_a_213_);
v_a_214_ = lean_ctor_get(v_a_212_, 1);
lean_inc_ref(v_a_214_);
lean_dec_ref_known(v_a_212_, 2);
v___f_215_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0), 3, 2);
lean_closure_set(v___f_215_, 0, v_a_213_);
lean_closure_set(v___f_215_, 1, v_wrap_211_);
v_wrap_211_ = v___f_215_;
v_a_212_ = v_a_214_;
goto _start;
}
case 4:
{
lean_object* v_a_217_; lean_object* v_a_218_; lean_object* v___f_219_; 
v_a_217_ = lean_ctor_get(v_a_212_, 0);
lean_inc_ref(v_a_217_);
v_a_218_ = lean_ctor_get(v_a_212_, 1);
lean_inc_ref(v_a_218_);
lean_dec_ref_known(v_a_212_, 2);
v___f_219_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1), 3, 2);
lean_closure_set(v___f_219_, 0, v_a_217_);
lean_closure_set(v___f_219_, 1, v_wrap_211_);
v_wrap_211_ = v___f_219_;
v_a_212_ = v_a_218_;
goto _start;
}
case 8:
{
lean_object* v_a_221_; 
v_a_221_ = lean_ctor_get(v_a_212_, 1);
lean_inc_ref(v_a_221_);
if (lean_obj_tag(v_a_221_) == 9)
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_237_; 
v_a_222_ = lean_ctor_get(v_a_212_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_a_212_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v_a_212_, 1);
lean_dec(v_unused_238_);
v___x_224_ = v_a_212_;
v_isShared_225_ = v_isSharedCheck_237_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v_a_212_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_237_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v_data_226_; lean_object* v_msg_227_; lean_object* v_children_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v_data_226_ = lean_ctor_get(v_a_221_, 0);
lean_inc_ref(v_data_226_);
v_msg_227_ = lean_ctor_get(v_a_221_, 1);
lean_inc_ref(v_msg_227_);
v_children_228_ = lean_ctor_get(v_a_221_, 2);
lean_inc_ref(v_children_228_);
lean_dec_ref_known(v_a_221_, 3);
v___x_229_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___closed__1));
v___x_230_ = lean_name_eq(v_a_222_, v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; 
lean_dec_ref(v_children_228_);
lean_dec_ref(v_msg_227_);
lean_dec_ref(v_data_226_);
lean_del_object(v___x_224_);
lean_dec(v_a_222_);
lean_dec_ref(v_wrap_211_);
v___x_231_ = lean_box(0);
return v___x_231_;
}
else
{
lean_object* v___f_232_; lean_object* v___x_234_; 
v___f_232_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___lam__2), 5, 4);
lean_closure_set(v___f_232_, 0, v_data_226_);
lean_closure_set(v___f_232_, 1, v_msg_227_);
lean_closure_set(v___f_232_, 2, v_a_222_);
lean_closure_set(v___f_232_, 3, v_wrap_211_);
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 0);
lean_ctor_set(v___x_224_, 1, v_children_228_);
lean_ctor_set(v___x_224_, 0, v___f_232_);
v___x_234_ = v___x_224_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___f_232_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_children_228_);
v___x_234_ = v_reuseFailAlloc_236_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
}
}
else
{
lean_object* v___x_239_; 
lean_dec_ref(v_a_221_);
lean_dec_ref_known(v_a_212_, 2);
lean_dec_ref(v_wrap_211_);
v___x_239_ = lean_box(0);
return v___x_239_;
}
}
default: 
{
lean_object* v___x_240_; 
lean_dec_ref(v_a_212_);
lean_dec_ref(v_wrap_211_);
v___x_240_ = lean_box(0);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f(lean_object* v_data_241_){
_start:
{
lean_object* v___f_242_; lean_object* v___x_243_; 
v___f_242_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0));
v___x_243_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go(v___f_242_, v_data_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage_spec__0(size_t v_sz_244_, size_t v_i_245_, lean_object* v_bs_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = lean_usize_dec_lt(v_i_245_, v_sz_244_);
if (v___x_247_ == 0)
{
return v_bs_246_;
}
else
{
lean_object* v_v_248_; lean_object* v___x_249_; lean_object* v_bs_x27_250_; lean_object* v___x_251_; size_t v___x_252_; size_t v___x_253_; lean_object* v___x_254_; 
v_v_248_ = lean_array_uget(v_bs_246_, v_i_245_);
v___x_249_ = lean_unsigned_to_nat(0u);
v_bs_x27_250_ = lean_array_uset(v_bs_246_, v_i_245_, v___x_249_);
v___x_251_ = l_Lean_PostprocessTraces_TraceTree_ofMessageData(v_v_248_);
v___x_252_ = ((size_t)1ULL);
v___x_253_ = lean_usize_add(v_i_245_, v___x_252_);
v___x_254_ = lean_array_uset(v_bs_x27_250_, v_i_245_, v___x_251_);
v_i_245_ = v___x_253_;
v_bs_246_ = v___x_254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage_spec__0___boxed(lean_object* v_sz_256_, lean_object* v_i_257_, lean_object* v_bs_258_){
_start:
{
size_t v_sz_boxed_259_; size_t v_i_boxed_260_; lean_object* v_res_261_; 
v_sz_boxed_259_ = lean_unbox_usize(v_sz_256_);
lean_dec(v_sz_256_);
v_i_boxed_260_ = lean_unbox_usize(v_i_257_);
lean_dec(v_i_257_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage_spec__0(v_sz_boxed_259_, v_i_boxed_260_, v_bs_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage(lean_object* v_post_262_, lean_object* v_msg_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_fileName_267_; lean_object* v_pos_268_; lean_object* v_endPos_269_; uint8_t v_keepFullRange_270_; uint8_t v_severity_271_; uint8_t v_isSilent_272_; lean_object* v_caption_273_; lean_object* v_data_274_; lean_object* v___x_275_; 
v_fileName_267_ = lean_ctor_get(v_msg_263_, 0);
v_pos_268_ = lean_ctor_get(v_msg_263_, 1);
v_endPos_269_ = lean_ctor_get(v_msg_263_, 2);
v_keepFullRange_270_ = lean_ctor_get_uint8(v_msg_263_, sizeof(void*)*5);
v_severity_271_ = lean_ctor_get_uint8(v_msg_263_, sizeof(void*)*5 + 1);
v_isSilent_272_ = lean_ctor_get_uint8(v_msg_263_, sizeof(void*)*5 + 2);
v_caption_273_ = lean_ctor_get(v_msg_263_, 3);
v_data_274_ = lean_ctor_get(v_msg_263_, 4);
lean_inc(v_data_274_);
v___x_275_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f(v_data_274_);
if (lean_obj_tag(v___x_275_) == 1)
{
lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_322_; 
lean_inc_ref(v_caption_273_);
lean_inc(v_endPos_269_);
lean_inc_ref(v_pos_268_);
lean_inc_ref(v_fileName_267_);
v_isSharedCheck_322_ = !lean_is_exclusive(v_msg_263_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; lean_object* v_unused_324_; lean_object* v_unused_325_; lean_object* v_unused_326_; lean_object* v_unused_327_; 
v_unused_323_ = lean_ctor_get(v_msg_263_, 4);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_msg_263_, 3);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_msg_263_, 2);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_msg_263_, 1);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v_msg_263_, 0);
lean_dec(v_unused_327_);
v___x_277_ = v_msg_263_;
v_isShared_278_ = v_isSharedCheck_322_;
goto v_resetjp_276_;
}
else
{
lean_dec(v_msg_263_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_322_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v_val_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_321_; 
v_val_279_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_321_ == 0)
{
v___x_281_ = v___x_275_;
v_isShared_282_ = v_isSharedCheck_321_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_val_279_);
lean_dec(v___x_275_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_321_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_fst_283_; lean_object* v_snd_284_; size_t v_sz_285_; size_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_fst_283_ = lean_ctor_get(v_val_279_, 0);
lean_inc(v_fst_283_);
v_snd_284_ = lean_ctor_get(v_val_279_, 1);
lean_inc(v_snd_284_);
lean_dec(v_val_279_);
v_sz_285_ = lean_array_size(v_snd_284_);
v___x_286_ = ((size_t)0ULL);
v___x_287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage_spec__0(v_sz_285_, v___x_286_, v_snd_284_);
lean_inc(v_a_265_);
lean_inc_ref(v_a_264_);
v___x_288_ = lean_apply_4(v_post_262_, v___x_287_, v_a_264_, v_a_265_, lean_box(0));
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_312_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_312_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_312_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_312_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_293_ = lean_array_get_size(v_a_289_);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_nat_dec_eq(v___x_293_, v___x_294_);
if (v___x_295_ == 0)
{
size_t v_sz_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v_sz_296_ = lean_array_size(v_a_289_);
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_296_, v___x_286_, v_a_289_);
v___x_298_ = lean_apply_1(v_fst_283_, v___x_297_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 4, v___x_298_);
v___x_300_ = v___x_277_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_fileName_267_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_pos_268_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_endPos_269_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_caption_273_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v___x_298_);
lean_ctor_set_uint8(v_reuseFailAlloc_307_, sizeof(void*)*5, v_keepFullRange_270_);
lean_ctor_set_uint8(v_reuseFailAlloc_307_, sizeof(void*)*5 + 1, v_severity_271_);
lean_ctor_set_uint8(v_reuseFailAlloc_307_, sizeof(void*)*5 + 2, v_isSilent_272_);
v___x_300_ = v_reuseFailAlloc_307_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_300_);
v___x_302_ = v___x_281_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_306_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_304_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_302_);
v___x_304_ = v___x_291_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_310_; 
lean_dec(v_a_289_);
lean_dec(v_fst_283_);
lean_del_object(v___x_281_);
lean_del_object(v___x_277_);
lean_dec_ref(v_caption_273_);
lean_dec(v_endPos_269_);
lean_dec_ref(v_pos_268_);
lean_dec_ref(v_fileName_267_);
v___x_308_ = lean_box(0);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_308_);
v___x_310_ = v___x_291_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec(v_fst_283_);
lean_del_object(v___x_281_);
lean_del_object(v___x_277_);
lean_dec_ref(v_caption_273_);
lean_dec(v_endPos_269_);
lean_dec_ref(v_pos_268_);
lean_dec_ref(v_fileName_267_);
v_a_313_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_288_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_288_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v___x_275_);
lean_dec_ref(v_post_262_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v_msg_263_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage___boxed(lean_object* v_post_330_, lean_object* v_msg_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage(v_post_330_, v_msg_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(lean_object* v_a_336_, lean_object* v_messages_337_, lean_object* v_trees_338_, lean_object* v_a_x3f_339_){
_start:
{
lean_object* v___x_341_; lean_object* v_infoState_342_; lean_object* v_env_343_; lean_object* v_messages_344_; lean_object* v_scopes_345_; lean_object* v_usedQuotCtxts_346_; lean_object* v_nextMacroScope_347_; lean_object* v_maxRecDepth_348_; lean_object* v_ngen_349_; lean_object* v_auxDeclNGen_350_; lean_object* v_traceState_351_; lean_object* v_snapshotTasks_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_375_; 
v___x_341_ = lean_st_ref_take(v_a_336_);
v_infoState_342_ = lean_ctor_get(v___x_341_, 8);
v_env_343_ = lean_ctor_get(v___x_341_, 0);
v_messages_344_ = lean_ctor_get(v___x_341_, 1);
v_scopes_345_ = lean_ctor_get(v___x_341_, 2);
v_usedQuotCtxts_346_ = lean_ctor_get(v___x_341_, 3);
v_nextMacroScope_347_ = lean_ctor_get(v___x_341_, 4);
v_maxRecDepth_348_ = lean_ctor_get(v___x_341_, 5);
v_ngen_349_ = lean_ctor_get(v___x_341_, 6);
v_auxDeclNGen_350_ = lean_ctor_get(v___x_341_, 7);
v_traceState_351_ = lean_ctor_get(v___x_341_, 9);
v_snapshotTasks_352_ = lean_ctor_get(v___x_341_, 10);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_375_ == 0)
{
v___x_354_ = v___x_341_;
v_isShared_355_ = v_isSharedCheck_375_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_snapshotTasks_352_);
lean_inc(v_traceState_351_);
lean_inc(v_infoState_342_);
lean_inc(v_auxDeclNGen_350_);
lean_inc(v_ngen_349_);
lean_inc(v_maxRecDepth_348_);
lean_inc(v_nextMacroScope_347_);
lean_inc(v_usedQuotCtxts_346_);
lean_inc(v_scopes_345_);
lean_inc(v_messages_344_);
lean_inc(v_env_343_);
lean_dec(v___x_341_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_375_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
uint8_t v_enabled_356_; lean_object* v_assignment_357_; lean_object* v_lazyAssignment_358_; lean_object* v_trees_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_374_; 
v_enabled_356_ = lean_ctor_get_uint8(v_infoState_342_, sizeof(void*)*3);
v_assignment_357_ = lean_ctor_get(v_infoState_342_, 0);
v_lazyAssignment_358_ = lean_ctor_get(v_infoState_342_, 1);
v_trees_359_ = lean_ctor_get(v_infoState_342_, 2);
v_isSharedCheck_374_ = !lean_is_exclusive(v_infoState_342_);
if (v_isSharedCheck_374_ == 0)
{
v___x_361_ = v_infoState_342_;
v_isShared_362_ = v_isSharedCheck_374_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_trees_359_);
lean_inc(v_lazyAssignment_358_);
lean_inc(v_assignment_357_);
lean_dec(v_infoState_342_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_374_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = l_Lean_MessageLog_append(v_messages_337_, v_messages_344_);
v___x_364_ = l_Lean_PersistentArray_append___redArg(v_trees_338_, v_trees_359_);
lean_dec_ref(v_trees_359_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 2, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_assignment_357_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_lazyAssignment_358_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v___x_364_);
lean_ctor_set_uint8(v_reuseFailAlloc_373_, sizeof(void*)*3, v_enabled_356_);
v___x_366_ = v_reuseFailAlloc_373_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 8, v___x_366_);
lean_ctor_set(v___x_354_, 1, v___x_363_);
v___x_368_ = v___x_354_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_env_343_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_scopes_345_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_usedQuotCtxts_346_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v_nextMacroScope_347_);
lean_ctor_set(v_reuseFailAlloc_372_, 5, v_maxRecDepth_348_);
lean_ctor_set(v_reuseFailAlloc_372_, 6, v_ngen_349_);
lean_ctor_set(v_reuseFailAlloc_372_, 7, v_auxDeclNGen_350_);
lean_ctor_set(v_reuseFailAlloc_372_, 8, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_372_, 9, v_traceState_351_);
lean_ctor_set(v_reuseFailAlloc_372_, 10, v_snapshotTasks_352_);
v___x_368_ = v_reuseFailAlloc_372_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_st_ref_set(v_a_336_, v___x_368_);
v___x_370_ = lean_box(0);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0___boxed(lean_object* v_a_376_, lean_object* v_messages_377_, lean_object* v_trees_378_, lean_object* v_a_x3f_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_376_, v_messages_377_, v_trees_378_, v_a_x3f_379_);
lean_dec(v_a_x3f_379_);
lean_dec(v_a_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(lean_object* v_as_382_, size_t v_i_383_, size_t v_stop_384_, lean_object* v_b_385_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = lean_usize_dec_eq(v_i_383_, v_stop_384_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v_diagnostics_388_; lean_object* v_msgLog_389_; lean_object* v___x_390_; size_t v___x_391_; size_t v___x_392_; 
v___x_387_ = lean_array_uget_borrowed(v_as_382_, v_i_383_);
v_diagnostics_388_ = lean_ctor_get(v___x_387_, 1);
v_msgLog_389_ = lean_ctor_get(v_diagnostics_388_, 0);
lean_inc_ref(v_msgLog_389_);
v___x_390_ = l_Lean_MessageLog_append(v_b_385_, v_msgLog_389_);
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_383_, v___x_391_);
v_i_383_ = v___x_392_;
v_b_385_ = v___x_390_;
goto _start;
}
else
{
return v_b_385_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0___boxed(lean_object* v_as_394_, lean_object* v_i_395_, lean_object* v_stop_396_, lean_object* v_b_397_){
_start:
{
size_t v_i_boxed_398_; size_t v_stop_boxed_399_; lean_object* v_res_400_; 
v_i_boxed_398_ = lean_unbox_usize(v_i_395_);
lean_dec(v_i_395_);
v_stop_boxed_399_ = lean_unbox_usize(v_stop_396_);
lean_dec(v_stop_396_);
v_res_400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v_as_394_, v_i_boxed_398_, v_stop_boxed_399_, v_b_397_);
lean_dec_ref(v_as_394_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(lean_object* v_as_401_, size_t v_i_402_, size_t v_stop_403_, lean_object* v_b_404_){
_start:
{
lean_object* v___y_406_; uint8_t v___x_410_; 
v___x_410_ = lean_usize_dec_eq(v_i_402_, v_stop_403_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_411_ = lean_array_uget_borrowed(v_as_401_, v_i_402_);
v___x_412_ = l_Lean_MessageLog_empty;
lean_inc(v___x_411_);
v___x_413_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_411_);
v___x_414_ = l_Lean_Language_SnapshotTree_getAll(v___x_413_);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_array_get_size(v___x_414_);
v___x_417_ = lean_nat_dec_lt(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
lean_dec_ref(v___x_414_);
v___x_418_ = l_Lean_MessageLog_append(v_b_404_, v___x_412_);
v___y_406_ = v___x_418_;
goto v___jp_405_;
}
else
{
uint8_t v___x_419_; 
v___x_419_ = lean_nat_dec_le(v___x_416_, v___x_416_);
if (v___x_419_ == 0)
{
if (v___x_417_ == 0)
{
lean_object* v___x_420_; 
lean_dec_ref(v___x_414_);
v___x_420_ = l_Lean_MessageLog_append(v_b_404_, v___x_412_);
v___y_406_ = v___x_420_;
goto v___jp_405_;
}
else
{
size_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_421_ = ((size_t)0ULL);
v___x_422_ = lean_usize_of_nat(v___x_416_);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v___x_414_, v___x_421_, v___x_422_, v___x_412_);
lean_dec_ref(v___x_414_);
v___x_424_ = l_Lean_MessageLog_append(v_b_404_, v___x_423_);
v___y_406_ = v___x_424_;
goto v___jp_405_;
}
}
else
{
size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_425_ = ((size_t)0ULL);
v___x_426_ = lean_usize_of_nat(v___x_416_);
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v___x_414_, v___x_425_, v___x_426_, v___x_412_);
lean_dec_ref(v___x_414_);
v___x_428_ = l_Lean_MessageLog_append(v_b_404_, v___x_427_);
v___y_406_ = v___x_428_;
goto v___jp_405_;
}
}
}
else
{
return v_b_404_;
}
v___jp_405_:
{
size_t v___x_407_; size_t v___x_408_; 
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_add(v_i_402_, v___x_407_);
v_i_402_ = v___x_408_;
v_b_404_ = v___y_406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1___boxed(lean_object* v_as_429_, lean_object* v_i_430_, lean_object* v_stop_431_, lean_object* v_b_432_){
_start:
{
size_t v_i_boxed_433_; size_t v_stop_boxed_434_; lean_object* v_res_435_; 
v_i_boxed_433_ = lean_unbox_usize(v_i_430_);
lean_dec(v_i_430_);
v_stop_boxed_434_ = lean_unbox_usize(v_stop_431_);
lean_dec(v_stop_431_);
v_res_435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_as_429_, v_i_boxed_433_, v_stop_boxed_434_, v_b_432_);
lean_dec_ref(v_as_429_);
return v_res_435_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_unsigned_to_nat(32u);
v___x_437_ = lean_mk_empty_array_with_capacity(v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1(void){
_start:
{
size_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_439_ = ((size_t)5ULL);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_unsigned_to_nat(32u);
v___x_442_ = lean_mk_empty_array_with_capacity(v___x_441_);
v___x_443_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0);
v___x_444_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_440_);
lean_ctor_set(v___x_444_, 3, v___x_440_);
lean_ctor_set_usize(v___x_444_, 4, v___x_439_);
return v___x_444_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = l_Lean_NameSet_empty;
v___x_446_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1);
v___x_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
lean_ctor_set(v___x_447_, 2, v___x_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages(lean_object* v_cmd_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_env_457_; lean_object* v_scopes_458_; lean_object* v_usedQuotCtxts_459_; lean_object* v_nextMacroScope_460_; lean_object* v_maxRecDepth_461_; lean_object* v_ngen_462_; lean_object* v_auxDeclNGen_463_; lean_object* v_infoState_464_; lean_object* v_traceState_465_; lean_object* v_snapshotTasks_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_559_; 
v___x_454_ = lean_st_ref_get(v_a_452_);
v___x_455_ = lean_st_ref_get(v_a_452_);
v___x_456_ = lean_st_ref_take(v_a_452_);
v_env_457_ = lean_ctor_get(v___x_456_, 0);
v_scopes_458_ = lean_ctor_get(v___x_456_, 2);
v_usedQuotCtxts_459_ = lean_ctor_get(v___x_456_, 3);
v_nextMacroScope_460_ = lean_ctor_get(v___x_456_, 4);
v_maxRecDepth_461_ = lean_ctor_get(v___x_456_, 5);
v_ngen_462_ = lean_ctor_get(v___x_456_, 6);
v_auxDeclNGen_463_ = lean_ctor_get(v___x_456_, 7);
v_infoState_464_ = lean_ctor_get(v___x_456_, 8);
v_traceState_465_ = lean_ctor_get(v___x_456_, 9);
v_snapshotTasks_466_ = lean_ctor_get(v___x_456_, 10);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v___x_456_, 1);
lean_dec(v_unused_560_);
v___x_468_ = v___x_456_;
v_isShared_469_ = v_isSharedCheck_559_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snapshotTasks_466_);
lean_inc(v_traceState_465_);
lean_inc(v_infoState_464_);
lean_inc(v_auxDeclNGen_463_);
lean_inc(v_ngen_462_);
lean_inc(v_maxRecDepth_461_);
lean_inc(v_nextMacroScope_460_);
lean_inc(v_usedQuotCtxts_459_);
lean_inc(v_scopes_458_);
lean_inc(v_env_457_);
lean_dec(v___x_456_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_559_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_env_457_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_scopes_458_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_usedQuotCtxts_459_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_nextMacroScope_460_);
lean_ctor_set(v_reuseFailAlloc_558_, 5, v_maxRecDepth_461_);
lean_ctor_set(v_reuseFailAlloc_558_, 6, v_ngen_462_);
lean_ctor_set(v_reuseFailAlloc_558_, 7, v_auxDeclNGen_463_);
lean_ctor_set(v_reuseFailAlloc_558_, 8, v_infoState_464_);
lean_ctor_set(v_reuseFailAlloc_558_, 9, v_traceState_465_);
lean_ctor_set(v_reuseFailAlloc_558_, 10, v_snapshotTasks_466_);
v___x_473_ = v_reuseFailAlloc_558_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_474_; lean_object* v_infoState_475_; lean_object* v_messages_476_; lean_object* v_trees_477_; lean_object* v_fileName_478_; lean_object* v_fileMap_479_; lean_object* v_currRecDepth_480_; lean_object* v_cmdPos_481_; lean_object* v_macroStack_482_; lean_object* v_quotContext_x3f_483_; lean_object* v_currMacroScope_484_; lean_object* v_ref_485_; lean_object* v_cancelTk_x3f_486_; uint8_t v_suppressElabErrors_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_474_ = lean_st_ref_set(v_a_452_, v___x_473_);
v_infoState_475_ = lean_ctor_get(v___x_455_, 8);
lean_inc_ref(v_infoState_475_);
lean_dec(v___x_455_);
v_messages_476_ = lean_ctor_get(v___x_454_, 1);
lean_inc_ref(v_messages_476_);
lean_dec(v___x_454_);
v_trees_477_ = lean_ctor_get(v_infoState_475_, 2);
lean_inc_ref(v_trees_477_);
lean_dec_ref(v_infoState_475_);
v_fileName_478_ = lean_ctor_get(v_a_451_, 0);
v_fileMap_479_ = lean_ctor_get(v_a_451_, 1);
v_currRecDepth_480_ = lean_ctor_get(v_a_451_, 2);
v_cmdPos_481_ = lean_ctor_get(v_a_451_, 3);
v_macroStack_482_ = lean_ctor_get(v_a_451_, 4);
v_quotContext_x3f_483_ = lean_ctor_get(v_a_451_, 5);
v_currMacroScope_484_ = lean_ctor_get(v_a_451_, 6);
v_ref_485_ = lean_ctor_get(v_a_451_, 7);
v_cancelTk_x3f_486_ = lean_ctor_get(v_a_451_, 9);
v_suppressElabErrors_487_ = lean_ctor_get_uint8(v_a_451_, sizeof(void*)*10);
v___x_488_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__3));
v___x_489_ = lean_box(0);
lean_inc(v_cancelTk_x3f_486_);
lean_inc(v_ref_485_);
lean_inc(v_currMacroScope_484_);
lean_inc(v_quotContext_x3f_483_);
lean_inc(v_macroStack_482_);
lean_inc(v_cmdPos_481_);
lean_inc(v_currRecDepth_480_);
lean_inc_ref(v_fileMap_479_);
lean_inc_ref(v_fileName_478_);
v___x_490_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_490_, 0, v_fileName_478_);
lean_ctor_set(v___x_490_, 1, v_fileMap_479_);
lean_ctor_set(v___x_490_, 2, v_currRecDepth_480_);
lean_ctor_set(v___x_490_, 3, v_cmdPos_481_);
lean_ctor_set(v___x_490_, 4, v_macroStack_482_);
lean_ctor_set(v___x_490_, 5, v_quotContext_x3f_483_);
lean_ctor_set(v___x_490_, 6, v_currMacroScope_484_);
lean_ctor_set(v___x_490_, 7, v_ref_485_);
lean_ctor_set(v___x_490_, 8, v___x_489_);
lean_ctor_set(v___x_490_, 9, v_cancelTk_x3f_486_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*10, v_suppressElabErrors_487_);
v___x_491_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_450_, v___x_488_, v___x_490_, v_a_452_);
lean_dec_ref_known(v___x_490_, 10);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_546_; 
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; 
v_unused_547_ = lean_ctor_get(v___x_491_, 0);
lean_dec(v_unused_547_);
v___x_493_ = v___x_491_;
v_isShared_494_ = v_isSharedCheck_546_;
goto v_resetjp_492_;
}
else
{
lean_dec(v___x_491_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_546_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_messages_497_; lean_object* v___y_499_; lean_object* v_snapshotTasks_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_495_ = lean_st_ref_get(v_a_452_);
v___x_496_ = lean_st_ref_get(v_a_452_);
v_messages_497_ = lean_ctor_get(v___x_495_, 1);
lean_inc_ref(v_messages_497_);
lean_dec(v___x_495_);
v_snapshotTasks_535_ = lean_ctor_get(v___x_496_, 10);
lean_inc_ref(v_snapshotTasks_535_);
lean_dec(v___x_496_);
v___x_536_ = l_Lean_MessageLog_empty;
v___x_537_ = lean_array_get_size(v_snapshotTasks_535_);
v___x_538_ = lean_nat_dec_lt(v___x_470_, v___x_537_);
if (v___x_538_ == 0)
{
lean_dec_ref(v_snapshotTasks_535_);
v___y_499_ = v___x_536_;
goto v___jp_498_;
}
else
{
uint8_t v___x_539_; 
v___x_539_ = lean_nat_dec_le(v___x_537_, v___x_537_);
if (v___x_539_ == 0)
{
if (v___x_538_ == 0)
{
lean_dec_ref(v_snapshotTasks_535_);
v___y_499_ = v___x_536_;
goto v___jp_498_;
}
else
{
size_t v___x_540_; size_t v___x_541_; lean_object* v___x_542_; 
v___x_540_ = ((size_t)0ULL);
v___x_541_ = lean_usize_of_nat(v___x_537_);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_snapshotTasks_535_, v___x_540_, v___x_541_, v___x_536_);
lean_dec_ref(v_snapshotTasks_535_);
v___y_499_ = v___x_542_;
goto v___jp_498_;
}
}
else
{
size_t v___x_543_; size_t v___x_544_; lean_object* v___x_545_; 
v___x_543_ = ((size_t)0ULL);
v___x_544_ = lean_usize_of_nat(v___x_537_);
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_snapshotTasks_535_, v___x_543_, v___x_544_, v___x_536_);
lean_dec_ref(v_snapshotTasks_535_);
v___y_499_ = v___x_545_;
goto v___jp_498_;
}
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v_env_501_; lean_object* v_scopes_502_; lean_object* v_usedQuotCtxts_503_; lean_object* v_nextMacroScope_504_; lean_object* v_maxRecDepth_505_; lean_object* v_ngen_506_; lean_object* v_auxDeclNGen_507_; lean_object* v_infoState_508_; lean_object* v_traceState_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_532_; 
v___x_500_ = lean_st_ref_take(v_a_452_);
v_env_501_ = lean_ctor_get(v___x_500_, 0);
v_scopes_502_ = lean_ctor_get(v___x_500_, 2);
v_usedQuotCtxts_503_ = lean_ctor_get(v___x_500_, 3);
v_nextMacroScope_504_ = lean_ctor_get(v___x_500_, 4);
v_maxRecDepth_505_ = lean_ctor_get(v___x_500_, 5);
v_ngen_506_ = lean_ctor_get(v___x_500_, 6);
v_auxDeclNGen_507_ = lean_ctor_get(v___x_500_, 7);
v_infoState_508_ = lean_ctor_get(v___x_500_, 8);
v_traceState_509_ = lean_ctor_get(v___x_500_, 9);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; lean_object* v_unused_534_; 
v_unused_533_ = lean_ctor_get(v___x_500_, 10);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v___x_500_, 1);
lean_dec(v_unused_534_);
v___x_511_ = v___x_500_;
v_isShared_512_ = v_isSharedCheck_532_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_traceState_509_);
lean_inc(v_infoState_508_);
lean_inc(v_auxDeclNGen_507_);
lean_inc(v_ngen_506_);
lean_inc(v_maxRecDepth_505_);
lean_inc(v_nextMacroScope_504_);
lean_inc(v_usedQuotCtxts_503_);
lean_inc(v_scopes_502_);
lean_inc(v_env_501_);
lean_dec(v___x_500_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_532_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 10, v___x_488_);
lean_ctor_set(v___x_511_, 1, v___x_471_);
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_env_501_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_scopes_502_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v_usedQuotCtxts_503_);
lean_ctor_set(v_reuseFailAlloc_531_, 4, v_nextMacroScope_504_);
lean_ctor_set(v_reuseFailAlloc_531_, 5, v_maxRecDepth_505_);
lean_ctor_set(v_reuseFailAlloc_531_, 6, v_ngen_506_);
lean_ctor_set(v_reuseFailAlloc_531_, 7, v_auxDeclNGen_507_);
lean_ctor_set(v_reuseFailAlloc_531_, 8, v_infoState_508_);
lean_ctor_set(v_reuseFailAlloc_531_, 9, v_traceState_509_);
lean_ctor_set(v_reuseFailAlloc_531_, 10, v___x_488_);
v___x_514_ = v_reuseFailAlloc_531_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_515_ = lean_st_ref_set(v_a_452_, v___x_514_);
v___x_516_ = l_Lean_MessageLog_append(v_messages_497_, v___y_499_);
v___x_517_ = l_Lean_MessageLog_toArray(v___x_516_);
lean_dec_ref(v___x_516_);
lean_inc_ref(v___x_517_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_517_);
v___x_519_ = v___x_493_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_530_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
v___x_521_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_452_, v_messages_476_, v_trees_477_, v___x_520_);
lean_dec_ref_known(v___x_520_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v___x_521_, 0);
lean_dec(v_unused_529_);
v___x_523_ = v___x_521_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_dec(v___x_521_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_517_);
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_517_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
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
lean_object* v_a_548_; lean_object* v___x_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_a_548_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_491_, 1);
v___x_549_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_452_, v_messages_476_, v_trees_477_, v___x_489_);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v___x_549_, 0);
lean_dec(v_unused_557_);
v___x_551_ = v___x_549_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_dec(v___x_549_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 1);
lean_ctor_set(v___x_551_, 0, v_a_548_);
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_548_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages___boxed(lean_object* v_cmd_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages(v_cmd_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(lean_object* v_type_566_, lean_object* v_e_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
uint8_t v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; 
v___x_573_ = 1;
v___x_574_ = 1;
v___x_575_ = l_Lean_Meta_evalExpr___redArg(v_type_566_, v_e_567_, v___x_573_, v___x_574_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1___boxed(lean_object* v_type_576_, lean_object* v_e_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(v_type_576_, v_e_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(lean_object* v_e_584_, lean_object* v___y_585_){
_start:
{
uint8_t v___x_587_; 
v___x_587_ = l_Lean_Expr_hasMVar(v_e_584_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v_e_584_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v_mctx_590_; lean_object* v___x_591_; lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___x_594_; lean_object* v_cache_595_; lean_object* v_zetaDeltaFVarIds_596_; lean_object* v_postponed_597_; lean_object* v_diag_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_607_; 
v___x_589_ = lean_st_ref_get(v___y_585_);
v_mctx_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc_ref(v_mctx_590_);
lean_dec(v___x_589_);
v___x_591_ = l_Lean_instantiateMVarsCore(v_mctx_590_, v_e_584_);
v_fst_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_fst_592_);
v_snd_593_ = lean_ctor_get(v___x_591_, 1);
lean_inc(v_snd_593_);
lean_dec_ref(v___x_591_);
v___x_594_ = lean_st_ref_take(v___y_585_);
v_cache_595_ = lean_ctor_get(v___x_594_, 1);
v_zetaDeltaFVarIds_596_ = lean_ctor_get(v___x_594_, 2);
v_postponed_597_ = lean_ctor_get(v___x_594_, 3);
v_diag_598_ = lean_ctor_get(v___x_594_, 4);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v___x_594_, 0);
lean_dec(v_unused_608_);
v___x_600_ = v___x_594_;
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_diag_598_);
lean_inc(v_postponed_597_);
lean_inc(v_zetaDeltaFVarIds_596_);
lean_inc(v_cache_595_);
lean_dec(v___x_594_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v_snd_593_);
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_snd_593_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_cache_595_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_zetaDeltaFVarIds_596_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v_postponed_597_);
lean_ctor_set(v_reuseFailAlloc_606_, 4, v_diag_598_);
v___x_603_ = v_reuseFailAlloc_606_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_st_ref_set(v___y_585_, v___x_603_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v_fst_592_);
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg___boxed(lean_object* v_e_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_e_609_, v___y_610_);
lean_dec(v___y_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(lean_object* v_e_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_e_613_, v___y_617_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___boxed(lean_object* v_e_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(v_e_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
return v_res_630_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_box(0);
v___x_632_ = l_Lean_Elab_abortTermExceptionId;
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg(){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0);
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___boxed(lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(lean_object* v_00_u03b1_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___boxed(lean_object* v_00_u03b1_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(v_00_u03b1_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(lean_object* v___x_657_, lean_object* v___x_658_, uint8_t v___x_659_, lean_object* v___x_660_, uint8_t v___x_661_, lean_object* v___x_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_657_, v___x_658_, v___x_659_, v___x_659_, v___x_660_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_661_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_673_; lean_object* v_a_674_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; uint8_t v___x_715_; 
lean_dec_ref_known(v___x_672_, 1);
v___x_673_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_a_671_, v___y_666_);
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref(v___x_673_);
v___x_715_ = l_Lean_Expr_hasSyntheticSorry(v_a_674_);
if (v___x_715_ == 0)
{
v___y_676_ = v___y_663_;
v___y_677_ = v___y_664_;
v___y_678_ = v___y_665_;
v___y_679_ = v___y_666_;
v___y_680_ = v___y_667_;
v___y_681_ = v___y_668_;
goto v___jp_675_;
}
else
{
lean_object* v___x_716_; lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_a_674_);
lean_dec_ref(v___x_662_);
v___x_716_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
v___jp_675_:
{
lean_object* v___x_682_; 
lean_inc(v_a_674_);
v___x_682_ = l_Lean_Meta_getMVars(v_a_674_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
v___x_684_ = lean_box(0);
v___x_685_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_683_, v___x_684_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v_a_683_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; uint8_t v___x_687_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 1);
v___x_687_ = lean_unbox(v_a_686_);
lean_dec(v_a_686_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; lean_object* v___x_689_; 
v___x_688_ = 1;
v___x_689_ = l_Lean_Meta_evalExpr___redArg(v___x_662_, v_a_674_, v___x_688_, v___x_659_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_a_674_);
lean_dec_ref(v___x_662_);
v___x_690_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_a_674_);
lean_dec_ref(v___x_662_);
v_a_699_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_685_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_685_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_a_674_);
lean_dec_ref(v___x_662_);
v_a_707_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_682_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_682_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_a_671_);
lean_dec_ref(v___x_662_);
v_a_725_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_672_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_672_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec_ref(v___x_662_);
v_a_733_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_670_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_670_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed(lean_object* v___x_741_, lean_object* v___x_742_, lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v___x_745_, lean_object* v___x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
uint8_t v___x_6069__boxed_754_; uint8_t v___x_6071__boxed_755_; lean_object* v_res_756_; 
v___x_6069__boxed_754_ = lean_unbox(v___x_743_);
v___x_6071__boxed_755_ = lean_unbox(v___x_745_);
v_res_756_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(v___x_741_, v___x_742_, v___x_6069__boxed_754_, v___x_744_, v___x_6071__boxed_755_, v___x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_756_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_757_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1);
v___x_763_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
lean_ctor_set(v___x_763_, 2, v___x_762_);
lean_ctor_set(v___x_763_, 3, v___x_762_);
lean_ctor_set(v___x_763_, 4, v___x_762_);
lean_ctor_set(v___x_763_, 5, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(lean_object* v_env_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; lean_object* v_nextMacroScope_769_; lean_object* v_ngen_770_; lean_object* v_auxDeclNGen_771_; lean_object* v_traceState_772_; lean_object* v_messages_773_; lean_object* v_infoState_774_; lean_object* v_snapshotTasks_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_801_; 
v___x_768_ = lean_st_ref_take(v___y_766_);
v_nextMacroScope_769_ = lean_ctor_get(v___x_768_, 1);
v_ngen_770_ = lean_ctor_get(v___x_768_, 2);
v_auxDeclNGen_771_ = lean_ctor_get(v___x_768_, 3);
v_traceState_772_ = lean_ctor_get(v___x_768_, 4);
v_messages_773_ = lean_ctor_get(v___x_768_, 6);
v_infoState_774_ = lean_ctor_get(v___x_768_, 7);
v_snapshotTasks_775_ = lean_ctor_get(v___x_768_, 8);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; lean_object* v_unused_803_; 
v_unused_802_ = lean_ctor_get(v___x_768_, 5);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v___x_768_, 0);
lean_dec(v_unused_803_);
v___x_777_ = v___x_768_;
v_isShared_778_ = v_isSharedCheck_801_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_snapshotTasks_775_);
lean_inc(v_infoState_774_);
lean_inc(v_messages_773_);
lean_inc(v_traceState_772_);
lean_inc(v_auxDeclNGen_771_);
lean_inc(v_ngen_770_);
lean_inc(v_nextMacroScope_769_);
lean_dec(v___x_768_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_801_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 5, v___x_779_);
lean_ctor_set(v___x_777_, 0, v_env_764_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_env_764_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_nextMacroScope_769_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v_ngen_770_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v_auxDeclNGen_771_);
lean_ctor_set(v_reuseFailAlloc_800_, 4, v_traceState_772_);
lean_ctor_set(v_reuseFailAlloc_800_, 5, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_800_, 6, v_messages_773_);
lean_ctor_set(v_reuseFailAlloc_800_, 7, v_infoState_774_);
lean_ctor_set(v_reuseFailAlloc_800_, 8, v_snapshotTasks_775_);
v___x_781_ = v_reuseFailAlloc_800_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_mctx_784_; lean_object* v_zetaDeltaFVarIds_785_; lean_object* v_postponed_786_; lean_object* v_diag_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_798_; 
v___x_782_ = lean_st_ref_set(v___y_766_, v___x_781_);
v___x_783_ = lean_st_ref_take(v___y_765_);
v_mctx_784_ = lean_ctor_get(v___x_783_, 0);
v_zetaDeltaFVarIds_785_ = lean_ctor_get(v___x_783_, 2);
v_postponed_786_ = lean_ctor_get(v___x_783_, 3);
v_diag_787_ = lean_ctor_get(v___x_783_, 4);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v___x_783_, 1);
lean_dec(v_unused_799_);
v___x_789_ = v___x_783_;
v_isShared_790_ = v_isSharedCheck_798_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_diag_787_);
lean_inc(v_postponed_786_);
lean_inc(v_zetaDeltaFVarIds_785_);
lean_inc(v_mctx_784_);
lean_dec(v___x_783_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_798_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_mctx_784_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_zetaDeltaFVarIds_785_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v_postponed_786_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v_diag_787_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = lean_st_ref_set(v___y_765_, v___x_793_);
v___x_795_ = lean_box(0);
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
return v___x_796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___boxed(lean_object* v_env_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec(v___y_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(lean_object* v_env_809_, lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; lean_object* v_env_819_; lean_object* v_a_821_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_818_ = lean_st_ref_get(v___y_816_);
v_env_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc_ref(v_env_819_);
lean_dec(v___x_818_);
v___x_831_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_809_, v___y_814_, v___y_816_);
lean_dec_ref(v___x_831_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
v___x_832_ = lean_apply_7(v_x_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, lean_box(0));
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_819_, v___y_814_, v___y_816_);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v___x_834_, 0);
lean_dec(v_unused_842_);
v___x_836_ = v___x_834_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_dec(v___x_834_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v_a_833_);
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_833_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v_a_843_; 
v_a_843_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_832_, 1);
v_a_821_ = v_a_843_;
goto v___jp_820_;
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v___x_822_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_819_, v___y_814_, v___y_816_);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_822_, 0);
lean_dec(v_unused_830_);
v___x_824_ = v___x_822_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_dec(v___x_822_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 1);
lean_ctor_set(v___x_824_, 0, v_a_821_);
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_821_);
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
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg___boxed(lean_object* v_env_844_, lean_object* v_x_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v_env_844_, v_x_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_853_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__9));
v___x_874_ = l_String_toRawSubstring_x27(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__22));
v___x_902_ = l_String_toRawSubstring_x27(v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32));
v___x_925_ = l_String_toRawSubstring_x27(v___x_924_);
return v___x_925_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_box(0);
v___x_940_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35));
v___x_941_ = l_Lean_mkConst(v___x_940_, v___x_939_);
return v___x_941_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(lean_object* v_post_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_ref_952_; lean_object* v_quotContext_953_; lean_object* v_currMacroScope_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_env_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_ref_952_ = lean_ctor_get(v_a_949_, 5);
v_quotContext_953_ = lean_ctor_get(v_a_949_, 10);
v_currMacroScope_954_ = lean_ctor_get(v_a_949_, 11);
v___x_955_ = 0;
v___x_956_ = l_Lean_SourceInfo_fromRef(v_ref_952_, v___x_955_);
v___x_957_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__2));
v___x_958_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3));
lean_inc_n(v___x_956_, 14);
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_956_);
lean_ctor_set(v___x_959_, 1, v___x_957_);
v___x_960_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6));
v___x_961_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__8));
v___x_962_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10);
v___x_963_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11));
lean_inc_n(v_currMacroScope_954_, 3);
lean_inc_n(v_quotContext_953_, 3);
v___x_964_ = l_Lean_addMacroScope(v_quotContext_953_, v___x_963_, v_currMacroScope_954_);
v___x_965_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13));
v___x_966_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_966_, 0, v___x_956_);
lean_ctor_set(v___x_966_, 1, v___x_962_);
lean_ctor_set(v___x_966_, 2, v___x_964_);
lean_ctor_set(v___x_966_, 3, v___x_965_);
v___x_967_ = l_Lean_Syntax_node1(v___x_956_, v___x_961_, v___x_966_);
v___x_968_ = l_Lean_Syntax_node1(v___x_956_, v___x_960_, v___x_967_);
v___x_969_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__14));
v___x_970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_956_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16));
v___x_972_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18));
v___x_973_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__19));
v___x_974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_956_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__21));
v___x_976_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23);
v___x_977_ = lean_box(0);
v___x_978_ = l_Lean_addMacroScope(v_quotContext_953_, v___x_977_, v_currMacroScope_954_);
v___x_979_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__30));
v___x_980_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_980_, 0, v___x_956_);
lean_ctor_set(v___x_980_, 1, v___x_976_);
lean_ctor_set(v___x_980_, 2, v___x_978_);
lean_ctor_set(v___x_980_, 3, v___x_979_);
v___x_981_ = l_Lean_Syntax_node1(v___x_956_, v___x_975_, v___x_980_);
v___x_982_ = l_Lean_Syntax_node2(v___x_956_, v___x_972_, v___x_974_, v___x_981_);
v___x_983_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__31));
v___x_984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_956_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33);
v___x_986_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34));
v___x_987_ = l_Lean_addMacroScope(v_quotContext_953_, v___x_986_, v_currMacroScope_954_);
v___x_988_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37));
v___x_989_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_989_, 0, v___x_956_);
lean_ctor_set(v___x_989_, 1, v___x_985_);
lean_ctor_set(v___x_989_, 2, v___x_987_);
lean_ctor_set(v___x_989_, 3, v___x_988_);
v___x_990_ = l_Lean_Syntax_node1(v___x_956_, v___x_961_, v___x_989_);
v___x_991_ = lean_st_ref_get(v_a_950_);
v___x_992_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__38));
v___x_993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_956_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v_env_994_ = lean_ctor_get(v___x_991_, 0);
lean_inc_ref(v_env_994_);
lean_dec(v___x_991_);
v___x_995_ = l_Lean_Syntax_node5(v___x_956_, v___x_971_, v___x_982_, v_post_944_, v___x_984_, v___x_990_, v___x_993_);
v___x_996_ = l_Lean_Syntax_node4(v___x_956_, v___x_958_, v___x_959_, v___x_968_, v___x_970_, v___x_995_);
v___x_997_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39);
v___x_998_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40);
v___x_999_ = 1;
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_box(v___x_999_);
v___x_1002_ = lean_box(v___x_955_);
v___f_1003_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1003_, 0, v___x_996_);
lean_closure_set(v___f_1003_, 1, v___x_998_);
lean_closure_set(v___f_1003_, 2, v___x_1001_);
lean_closure_set(v___f_1003_, 3, v___x_1000_);
lean_closure_set(v___f_1003_, 4, v___x_1002_);
lean_closure_set(v___f_1003_, 5, v___x_997_);
v___x_1004_ = l_Lean_Environment_unlockAsync(v_env_994_);
v___x_1005_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v___x_1004_, v___f_1003_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___boxed(lean_object* v_post_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(v_post_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(lean_object* v_env_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1015_, v___y_1019_, v___y_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___boxed(lean_object* v_env_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(v_env_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(lean_object* v_00_u03b1_1033_, lean_object* v_env_1034_, lean_object* v_x_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v_env_1034_, v_x_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___boxed(lean_object* v_00_u03b1_1044_, lean_object* v_env_1045_, lean_object* v_x_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(v_00_u03b1_1044_, v_env_1045_, v_x_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(lean_object* v_post_1055_, lean_object* v_x_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(v_post_1055_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed(lean_object* v_post_1065_, lean_object* v_x_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(v_post_1065_, v_x_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec_ref(v_x_1066_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(lean_object* v_a_1075_, lean_object* v_traceState_1076_, lean_object* v_a_x3f_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v_env_1080_; lean_object* v_messages_1081_; lean_object* v_scopes_1082_; lean_object* v_usedQuotCtxts_1083_; lean_object* v_nextMacroScope_1084_; lean_object* v_maxRecDepth_1085_; lean_object* v_ngen_1086_; lean_object* v_auxDeclNGen_1087_; lean_object* v_infoState_1088_; lean_object* v_snapshotTasks_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1099_; 
v___x_1079_ = lean_st_ref_take(v_a_1075_);
v_env_1080_ = lean_ctor_get(v___x_1079_, 0);
v_messages_1081_ = lean_ctor_get(v___x_1079_, 1);
v_scopes_1082_ = lean_ctor_get(v___x_1079_, 2);
v_usedQuotCtxts_1083_ = lean_ctor_get(v___x_1079_, 3);
v_nextMacroScope_1084_ = lean_ctor_get(v___x_1079_, 4);
v_maxRecDepth_1085_ = lean_ctor_get(v___x_1079_, 5);
v_ngen_1086_ = lean_ctor_get(v___x_1079_, 6);
v_auxDeclNGen_1087_ = lean_ctor_get(v___x_1079_, 7);
v_infoState_1088_ = lean_ctor_get(v___x_1079_, 8);
v_snapshotTasks_1089_ = lean_ctor_get(v___x_1079_, 10);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v___x_1079_, 9);
lean_dec(v_unused_1100_);
v___x_1091_ = v___x_1079_;
v_isShared_1092_ = v_isSharedCheck_1099_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_snapshotTasks_1089_);
lean_inc(v_infoState_1088_);
lean_inc(v_auxDeclNGen_1087_);
lean_inc(v_ngen_1086_);
lean_inc(v_maxRecDepth_1085_);
lean_inc(v_nextMacroScope_1084_);
lean_inc(v_usedQuotCtxts_1083_);
lean_inc(v_scopes_1082_);
lean_inc(v_messages_1081_);
lean_inc(v_env_1080_);
lean_dec(v___x_1079_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1099_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 9, v_traceState_1076_);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_env_1080_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_messages_1081_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_scopes_1082_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_usedQuotCtxts_1083_);
lean_ctor_set(v_reuseFailAlloc_1098_, 4, v_nextMacroScope_1084_);
lean_ctor_set(v_reuseFailAlloc_1098_, 5, v_maxRecDepth_1085_);
lean_ctor_set(v_reuseFailAlloc_1098_, 6, v_ngen_1086_);
lean_ctor_set(v_reuseFailAlloc_1098_, 7, v_auxDeclNGen_1087_);
lean_ctor_set(v_reuseFailAlloc_1098_, 8, v_infoState_1088_);
lean_ctor_set(v_reuseFailAlloc_1098_, 9, v_traceState_1076_);
lean_ctor_set(v_reuseFailAlloc_1098_, 10, v_snapshotTasks_1089_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = lean_st_ref_set(v_a_1075_, v___x_1094_);
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1___boxed(lean_object* v_a_1101_, lean_object* v_traceState_1102_, lean_object* v_a_x3f_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1101_, v_traceState_1102_, v_a_x3f_1103_);
lean_dec(v_a_x3f_1103_);
lean_dec(v_a_1101_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(lean_object* v_a_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_apply_4(v_a_1106_, v___y_1107_, v___y_1108_, v___y_1109_, lean_box(0));
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed(lean_object* v_a_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(v_a_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(lean_object* v_post_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; lean_object* v_traceState_1123_; lean_object* v___f_1124_; lean_object* v_r_1125_; 
v___x_1122_ = lean_st_ref_get(v_a_1120_);
v_traceState_1123_ = lean_ctor_get(v___x_1122_, 9);
lean_inc_ref(v_traceState_1123_);
lean_dec(v___x_1122_);
v___f_1124_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1124_, 0, v_post_1118_);
v_r_1125_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_1124_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v_r_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1143_; 
v_a_1126_ = lean_ctor_get(v_r_1125_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_r_1125_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1128_ = v_r_1125_;
v_isShared_1129_ = v_isSharedCheck_1143_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v_r_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1143_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
lean_inc(v_a_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 1);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1140_; 
v___x_1132_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1120_, v_traceState_1123_, v___x_1131_);
lean_dec_ref(v___x_1131_);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; 
v_unused_1141_ = lean_ctor_get(v___x_1132_, 0);
lean_dec(v_unused_1141_);
v___x_1134_ = v___x_1132_;
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
else
{
lean_dec(v___x_1132_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___f_1136_; lean_object* v___x_1138_; 
v___f_1136_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed), 5, 1);
lean_closure_set(v___f_1136_, 0, v_a_1126_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___f_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___f_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_a_1144_ = lean_ctor_get(v_r_1125_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v_r_1125_, 1);
v___x_1145_ = lean_box(0);
v___x_1146_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1120_, v_traceState_1123_, v___x_1145_);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1146_, 0);
lean_dec(v_unused_1154_);
v___x_1148_ = v___x_1146_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v___x_1146_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 1);
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1144_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___boxed(lean_object* v_post_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
return v_res_1159_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = lean_box(0);
v___x_1161_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v___x_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg(){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___boxed(lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0(lean_object* v_00_u03b1_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___boxed(lean_object* v_00_u03b1_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0(v_00_u03b1_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1177_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
lean_ctor_set(v___x_1183_, 2, v___x_1182_);
lean_ctor_set(v___x_1183_, 3, v___x_1182_);
lean_ctor_set(v___x_1183_, 4, v___x_1181_);
lean_ctor_set(v___x_1183_, 5, v___x_1181_);
lean_ctor_set(v___x_1183_, 6, v___x_1181_);
lean_ctor_set(v___x_1183_, 7, v___x_1181_);
lean_ctor_set(v___x_1183_, 8, v___x_1181_);
lean_ctor_set(v___x_1183_, 9, v___x_1181_);
return v___x_1183_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_unsigned_to_nat(32u);
v___x_1185_ = lean_mk_empty_array_with_capacity(v___x_1184_);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1187_ = ((size_t)5ULL);
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = lean_unsigned_to_nat(32u);
v___x_1190_ = lean_mk_empty_array_with_capacity(v___x_1189_);
v___x_1191_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3);
v___x_1192_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1190_);
lean_ctor_set(v___x_1192_, 2, v___x_1188_);
lean_ctor_set(v___x_1192_, 3, v___x_1188_);
lean_ctor_set_usize(v___x_1192_, 4, v___x_1187_);
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1193_ = lean_box(1);
v___x_1194_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4);
v___x_1195_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_1196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1194_);
lean_ctor_set(v___x_1196_, 2, v___x_1193_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; lean_object* v_env_1201_; lean_object* v___x_1202_; lean_object* v_scopes_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_opts_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1200_ = lean_st_ref_get(v___y_1198_);
v_env_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc_ref(v_env_1201_);
lean_dec(v___x_1200_);
v___x_1202_ = lean_st_ref_get(v___y_1198_);
v_scopes_1203_ = lean_ctor_get(v___x_1202_, 2);
lean_inc(v_scopes_1203_);
lean_dec(v___x_1202_);
v___x_1204_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1205_ = l_List_head_x21___redArg(v___x_1204_, v_scopes_1203_);
lean_dec(v_scopes_1203_);
v_opts_1206_ = lean_ctor_get(v___x_1205_, 1);
lean_inc_ref(v_opts_1206_);
lean_dec(v___x_1205_);
v___x_1207_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_1208_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5);
v___x_1209_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1209_, 0, v_env_1201_);
lean_ctor_set(v___x_1209_, 1, v___x_1207_);
lean_ctor_set(v___x_1209_, 2, v___x_1208_);
lean_ctor_set(v___x_1209_, 3, v_opts_1206_);
v___x_1210_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v_msgData_1197_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v_msgData_1212_, v___y_1213_);
lean_dec(v___y_1213_);
return v_res_1215_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(uint8_t v___y_1216_, uint8_t v_suppressElabErrors_1217_, lean_object* v_x_1218_){
_start:
{
if (lean_obj_tag(v_x_1218_) == 1)
{
lean_object* v_pre_1219_; 
v_pre_1219_ = lean_ctor_get(v_x_1218_, 0);
if (lean_obj_tag(v_pre_1219_) == 0)
{
lean_object* v_str_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v_str_1220_ = lean_ctor_get(v_x_1218_, 1);
v___x_1221_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_traceContainer_x3f_go___closed__0));
v___x_1222_ = lean_string_dec_eq(v_str_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
return v___y_1216_;
}
else
{
return v_suppressElabErrors_1217_;
}
}
else
{
return v___y_1216_;
}
}
else
{
return v___y_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v___y_1223_, lean_object* v_suppressElabErrors_1224_, lean_object* v_x_1225_){
_start:
{
uint8_t v___y_6276__boxed_1226_; uint8_t v_suppressElabErrors_boxed_1227_; uint8_t v_res_1228_; lean_object* v_r_1229_; 
v___y_6276__boxed_1226_ = lean_unbox(v___y_1223_);
v_suppressElabErrors_boxed_1227_ = lean_unbox(v_suppressElabErrors_1224_);
v_res_1228_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(v___y_6276__boxed_1226_, v_suppressElabErrors_boxed_1227_, v_x_1225_);
lean_dec(v_x_1225_);
v_r_1229_ = lean_box(v_res_1228_);
return v_r_1229_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(lean_object* v_opts_1230_, lean_object* v_opt_1231_){
_start:
{
lean_object* v_name_1232_; lean_object* v_defValue_1233_; lean_object* v_map_1234_; lean_object* v___x_1235_; 
v_name_1232_ = lean_ctor_get(v_opt_1231_, 0);
v_defValue_1233_ = lean_ctor_get(v_opt_1231_, 1);
v_map_1234_ = lean_ctor_get(v_opts_1230_, 0);
v___x_1235_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1234_, v_name_1232_);
if (lean_obj_tag(v___x_1235_) == 0)
{
uint8_t v___x_1236_; 
v___x_1236_ = lean_unbox(v_defValue_1233_);
return v___x_1236_;
}
else
{
lean_object* v_val_1237_; 
v_val_1237_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v___x_1235_, 1);
if (lean_obj_tag(v_val_1237_) == 1)
{
uint8_t v_v_1238_; 
v_v_1238_ = lean_ctor_get_uint8(v_val_1237_, 0);
lean_dec_ref_known(v_val_1237_, 0);
return v_v_1238_;
}
else
{
uint8_t v___x_1239_; 
lean_dec(v_val_1237_);
v___x_1239_ = lean_unbox(v_defValue_1233_);
return v___x_1239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_opts_1240_, lean_object* v_opt_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(v_opts_1240_, v_opt_1241_);
lean_dec_ref(v_opt_1241_);
lean_dec_ref(v_opts_1240_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(lean_object* v_ref_1244_, lean_object* v_msgData_1245_, uint8_t v_severity_1246_, uint8_t v_isSilent_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
uint8_t v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; uint8_t v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; uint8_t v___y_1315_; uint8_t v___y_1316_; lean_object* v___y_1317_; uint8_t v___y_1318_; lean_object* v___y_1319_; uint8_t v___y_1343_; uint8_t v___y_1344_; uint8_t v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; uint8_t v___y_1351_; uint8_t v___y_1352_; uint8_t v___y_1353_; uint8_t v___x_1368_; uint8_t v___y_1370_; uint8_t v___y_1371_; uint8_t v___y_1372_; uint8_t v___y_1374_; uint8_t v___x_1386_; 
v___x_1368_ = 2;
v___x_1386_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1246_, v___x_1368_);
if (v___x_1386_ == 0)
{
v___y_1374_ = v___x_1386_;
goto v___jp_1373_;
}
else
{
uint8_t v___x_1387_; 
lean_inc_ref(v_msgData_1245_);
v___x_1387_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1245_);
v___y_1374_ = v___x_1387_;
goto v___jp_1373_;
}
v___jp_1251_:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Elab_Command_getScope___redArg(v___y_1259_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1262_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = l_Lean_Elab_Command_getScope___redArg(v___y_1259_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1297_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1297_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1297_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v_currNamespace_1268_; lean_object* v_openDecls_1269_; lean_object* v_env_1270_; lean_object* v_messages_1271_; lean_object* v_scopes_1272_; lean_object* v_usedQuotCtxts_1273_; lean_object* v_nextMacroScope_1274_; lean_object* v_maxRecDepth_1275_; lean_object* v_ngen_1276_; lean_object* v_auxDeclNGen_1277_; lean_object* v_infoState_1278_; lean_object* v_traceState_1279_; lean_object* v_snapshotTasks_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1296_; 
v___x_1267_ = lean_st_ref_take(v___y_1259_);
v_currNamespace_1268_ = lean_ctor_get(v_a_1261_, 2);
lean_inc(v_currNamespace_1268_);
lean_dec(v_a_1261_);
v_openDecls_1269_ = lean_ctor_get(v_a_1263_, 3);
lean_inc(v_openDecls_1269_);
lean_dec(v_a_1263_);
v_env_1270_ = lean_ctor_get(v___x_1267_, 0);
v_messages_1271_ = lean_ctor_get(v___x_1267_, 1);
v_scopes_1272_ = lean_ctor_get(v___x_1267_, 2);
v_usedQuotCtxts_1273_ = lean_ctor_get(v___x_1267_, 3);
v_nextMacroScope_1274_ = lean_ctor_get(v___x_1267_, 4);
v_maxRecDepth_1275_ = lean_ctor_get(v___x_1267_, 5);
v_ngen_1276_ = lean_ctor_get(v___x_1267_, 6);
v_auxDeclNGen_1277_ = lean_ctor_get(v___x_1267_, 7);
v_infoState_1278_ = lean_ctor_get(v___x_1267_, 8);
v_traceState_1279_ = lean_ctor_get(v___x_1267_, 9);
v_snapshotTasks_1280_ = lean_ctor_get(v___x_1267_, 10);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1282_ = v___x_1267_;
v_isShared_1283_ = v_isSharedCheck_1296_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_snapshotTasks_1280_);
lean_inc(v_traceState_1279_);
lean_inc(v_infoState_1278_);
lean_inc(v_auxDeclNGen_1277_);
lean_inc(v_ngen_1276_);
lean_inc(v_maxRecDepth_1275_);
lean_inc(v_nextMacroScope_1274_);
lean_inc(v_usedQuotCtxts_1273_);
lean_inc(v_scopes_1272_);
lean_inc(v_messages_1271_);
lean_inc(v_env_1270_);
lean_dec(v___x_1267_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1296_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_currNamespace_1268_);
lean_ctor_set(v___x_1284_, 1, v_openDecls_1269_);
v___x_1285_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v___y_1253_);
lean_inc_ref(v___y_1257_);
lean_inc_ref(v___y_1256_);
v___x_1286_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1286_, 0, v___y_1256_);
lean_ctor_set(v___x_1286_, 1, v___y_1254_);
lean_ctor_set(v___x_1286_, 2, v___y_1258_);
lean_ctor_set(v___x_1286_, 3, v___y_1257_);
lean_ctor_set(v___x_1286_, 4, v___x_1285_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*5, v___y_1252_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*5 + 1, v___y_1255_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*5 + 2, v_isSilent_1247_);
v___x_1287_ = l_Lean_MessageLog_add(v___x_1286_, v_messages_1271_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___x_1287_);
v___x_1289_ = v___x_1282_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_env_1270_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_scopes_1272_);
lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_usedQuotCtxts_1273_);
lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_nextMacroScope_1274_);
lean_ctor_set(v_reuseFailAlloc_1295_, 5, v_maxRecDepth_1275_);
lean_ctor_set(v_reuseFailAlloc_1295_, 6, v_ngen_1276_);
lean_ctor_set(v_reuseFailAlloc_1295_, 7, v_auxDeclNGen_1277_);
lean_ctor_set(v_reuseFailAlloc_1295_, 8, v_infoState_1278_);
lean_ctor_set(v_reuseFailAlloc_1295_, 9, v_traceState_1279_);
lean_ctor_set(v_reuseFailAlloc_1295_, 10, v_snapshotTasks_1280_);
v___x_1289_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_st_ref_set(v___y_1259_, v___x_1289_);
v___x_1291_ = lean_box(0);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1291_);
v___x_1293_ = v___x_1265_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_a_1261_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v___y_1253_);
v_a_1298_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1262_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1262_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v___y_1253_);
v_a_1306_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1260_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1260_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
v___jp_1314_:
{
lean_object* v_fileName_1320_; lean_object* v_fileMap_1321_; uint8_t v_suppressElabErrors_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1341_; 
v_fileName_1320_ = lean_ctor_get(v___y_1248_, 0);
v_fileMap_1321_ = lean_ctor_get(v___y_1248_, 1);
v_suppressElabErrors_1322_ = lean_ctor_get_uint8(v___y_1248_, sizeof(void*)*10);
v___x_1323_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1245_);
v___x_1324_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v___x_1323_, v___y_1249_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1341_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1341_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_inc_ref_n(v_fileMap_1321_, 2);
v___x_1329_ = l_Lean_FileMap_toPosition(v_fileMap_1321_, v___y_1317_);
lean_dec(v___y_1317_);
v___x_1330_ = l_Lean_FileMap_toPosition(v_fileMap_1321_, v___y_1319_);
lean_dec(v___y_1319_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
v___x_1332_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__22));
if (v_suppressElabErrors_1322_ == 0)
{
lean_del_object(v___x_1327_);
v___y_1252_ = v___y_1316_;
v___y_1253_ = v_a_1325_;
v___y_1254_ = v___x_1329_;
v___y_1255_ = v___y_1318_;
v___y_1256_ = v_fileName_1320_;
v___y_1257_ = v___x_1332_;
v___y_1258_ = v___x_1331_;
v___y_1259_ = v___y_1249_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___f_1335_; uint8_t v___x_1336_; 
v___x_1333_ = lean_box(v___y_1315_);
v___x_1334_ = lean_box(v_suppressElabErrors_1322_);
v___f_1335_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1335_, 0, v___x_1333_);
lean_closure_set(v___f_1335_, 1, v___x_1334_);
lean_inc(v_a_1325_);
v___x_1336_ = l_Lean_MessageData_hasTag(v___f_1335_, v_a_1325_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
lean_dec_ref_known(v___x_1331_, 1);
lean_dec_ref(v___x_1329_);
lean_dec(v_a_1325_);
v___x_1337_ = lean_box(0);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1337_);
v___x_1339_ = v___x_1327_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
else
{
lean_del_object(v___x_1327_);
v___y_1252_ = v___y_1316_;
v___y_1253_ = v_a_1325_;
v___y_1254_ = v___x_1329_;
v___y_1255_ = v___y_1318_;
v___y_1256_ = v_fileName_1320_;
v___y_1257_ = v___x_1332_;
v___y_1258_ = v___x_1331_;
v___y_1259_ = v___y_1249_;
goto v___jp_1251_;
}
}
}
}
v___jp_1342_:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_Syntax_getTailPos_x3f(v___y_1346_, v___y_1344_);
lean_dec(v___y_1346_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_inc(v___y_1347_);
v___y_1315_ = v___y_1343_;
v___y_1316_ = v___y_1344_;
v___y_1317_ = v___y_1347_;
v___y_1318_ = v___y_1345_;
v___y_1319_ = v___y_1347_;
goto v___jp_1314_;
}
else
{
lean_object* v_val_1349_; 
v_val_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_val_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___y_1315_ = v___y_1343_;
v___y_1316_ = v___y_1344_;
v___y_1317_ = v___y_1347_;
v___y_1318_ = v___y_1345_;
v___y_1319_ = v_val_1349_;
goto v___jp_1314_;
}
}
v___jp_1350_:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Elab_Command_getRef___redArg(v___y_1248_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v_ref_1356_; lean_object* v___x_1357_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v_ref_1356_ = l_Lean_replaceRef(v_ref_1244_, v_a_1355_);
lean_dec(v_a_1355_);
v___x_1357_ = l_Lean_Syntax_getPos_x3f(v_ref_1356_, v___y_1352_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_unsigned_to_nat(0u);
v___y_1343_ = v___y_1351_;
v___y_1344_ = v___y_1352_;
v___y_1345_ = v___y_1353_;
v___y_1346_ = v_ref_1356_;
v___y_1347_ = v___x_1358_;
goto v___jp_1342_;
}
else
{
lean_object* v_val_1359_; 
v_val_1359_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_val_1359_);
lean_dec_ref_known(v___x_1357_, 1);
v___y_1343_ = v___y_1351_;
v___y_1344_ = v___y_1352_;
v___y_1345_ = v___y_1353_;
v___y_1346_ = v_ref_1356_;
v___y_1347_ = v_val_1359_;
goto v___jp_1342_;
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec_ref(v_msgData_1245_);
v_a_1360_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1354_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1354_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
v___jp_1369_:
{
if (v___y_1372_ == 0)
{
v___y_1351_ = v___y_1370_;
v___y_1352_ = v___y_1371_;
v___y_1353_ = v_severity_1246_;
goto v___jp_1350_;
}
else
{
v___y_1351_ = v___y_1370_;
v___y_1352_ = v___y_1371_;
v___y_1353_ = v___x_1368_;
goto v___jp_1350_;
}
}
v___jp_1373_:
{
if (v___y_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v_scopes_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v_opts_1379_; uint8_t v___x_1380_; uint8_t v___x_1381_; 
v___x_1375_ = lean_st_ref_get(v___y_1249_);
v_scopes_1376_ = lean_ctor_get(v___x_1375_, 2);
lean_inc(v_scopes_1376_);
lean_dec(v___x_1375_);
v___x_1377_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1378_ = l_List_head_x21___redArg(v___x_1377_, v_scopes_1376_);
lean_dec(v_scopes_1376_);
v_opts_1379_ = lean_ctor_get(v___x_1378_, 1);
lean_inc_ref(v_opts_1379_);
lean_dec(v___x_1378_);
v___x_1380_ = 1;
v___x_1381_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1246_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_dec_ref(v_opts_1379_);
v___y_1370_ = v___y_1374_;
v___y_1371_ = v___y_1374_;
v___y_1372_ = v___x_1381_;
goto v___jp_1369_;
}
else
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = l_Lean_warningAsError;
v___x_1383_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(v_opts_1379_, v___x_1382_);
lean_dec_ref(v_opts_1379_);
v___y_1370_ = v___y_1374_;
v___y_1371_ = v___y_1374_;
v___y_1372_ = v___x_1383_;
goto v___jp_1369_;
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec_ref(v_msgData_1245_);
v___x_1384_ = lean_box(0);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_1388_, lean_object* v_msgData_1389_, lean_object* v_severity_1390_, lean_object* v_isSilent_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v_severity_boxed_1395_; uint8_t v_isSilent_boxed_1396_; lean_object* v_res_1397_; 
v_severity_boxed_1395_ = lean_unbox(v_severity_1390_);
v_isSilent_boxed_1396_ = lean_unbox(v_isSilent_1391_);
v_res_1397_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_1388_, v_msgData_1389_, v_severity_boxed_1395_, v_isSilent_boxed_1396_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v_ref_1388_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(lean_object* v_msgData_1398_, uint8_t v_severity_1399_, uint8_t v_isSilent_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_Elab_Command_getRef___redArg(v___y_1401_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_a_1405_, v_msgData_1398_, v_severity_1399_, v_isSilent_1400_, v___y_1401_, v___y_1402_);
lean_dec(v_a_1405_);
return v___x_1406_;
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v_msgData_1398_);
v_a_1407_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1404_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1404_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_1415_, lean_object* v_severity_1416_, lean_object* v_isSilent_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
uint8_t v_severity_boxed_1421_; uint8_t v_isSilent_boxed_1422_; lean_object* v_res_1423_; 
v_severity_boxed_1421_ = lean_unbox(v_severity_1416_);
v_isSilent_boxed_1422_ = lean_unbox(v_isSilent_1417_);
v_res_1423_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_1415_, v_severity_boxed_1421_, v_isSilent_boxed_1422_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(lean_object* v_msgData_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v___x_1428_; uint8_t v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = 2;
v___x_1429_ = 0;
v___x_1430_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_1424_, v___x_1428_, v___x_1429_, v___y_1425_, v___y_1426_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2___boxed(lean_object* v_msgData_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v_msgData_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(lean_object* v_ref_1436_, lean_object* v_msgData_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
uint8_t v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = 2;
v___x_1442_ = 0;
v___x_1443_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_1436_, v_msgData_1437_, v___x_1441_, v___x_1442_, v___y_1438_, v___y_1439_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1___boxed(lean_object* v_ref_1444_, lean_object* v_msgData_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_1444_, v_msgData_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v_ref_1444_);
return v_res_1449_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0));
v___x_1452_ = l_Lean_stringToMessageData(v___x_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(lean_object* v_ex_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
if (lean_obj_tag(v_ex_1453_) == 0)
{
lean_object* v_ref_1457_; lean_object* v_msg_1458_; lean_object* v___x_1459_; 
v_ref_1457_ = lean_ctor_get(v_ex_1453_, 0);
lean_inc(v_ref_1457_);
v_msg_1458_ = lean_ctor_get(v_ex_1453_, 1);
lean_inc_ref(v_msg_1458_);
lean_dec_ref_known(v_ex_1453_, 2);
v___x_1459_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_1457_, v_msg_1458_, v___y_1454_, v___y_1455_);
lean_dec(v_ref_1457_);
return v___x_1459_;
}
else
{
lean_object* v_id_1460_; uint8_t v___y_1462_; uint8_t v___x_1484_; 
v_id_1460_ = lean_ctor_get(v_ex_1453_, 0);
lean_inc(v_id_1460_);
v___x_1484_ = l_Lean_Elab_isAbortExceptionId(v_id_1460_);
if (v___x_1484_ == 0)
{
uint8_t v___x_1485_; 
v___x_1485_ = l_Lean_Exception_isInterrupt(v_ex_1453_);
lean_dec_ref_known(v_ex_1453_, 2);
v___y_1462_ = v___x_1485_;
goto v___jp_1461_;
}
else
{
lean_dec_ref_known(v_ex_1453_, 2);
v___y_1462_ = v___x_1484_;
goto v___jp_1461_;
}
v___jp_1461_:
{
if (v___y_1462_ == 0)
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_InternalExceptionId_getName(v_id_1460_);
lean_dec(v_id_1460_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1);
v___x_1466_ = l_Lean_MessageData_ofName(v_a_1464_);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1465_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v___x_1467_, v___y_1454_, v___y_1455_);
return v___x_1468_;
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1481_; 
v_a_1469_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1471_ = v___x_1463_;
v_isShared_1472_ = v_isSharedCheck_1481_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1463_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1481_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v_ref_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v_ref_1473_ = lean_ctor_get(v___y_1454_, 7);
v___x_1474_ = lean_io_error_to_string(v_a_1469_);
v___x_1475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
v___x_1476_ = l_Lean_MessageData_ofFormat(v___x_1475_);
lean_inc(v_ref_1473_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_ref_1473_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1477_);
v___x_1479_ = v___x_1471_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec(v_id_1460_);
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___boxed(lean_object* v_ex_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_ex_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(lean_object* v_a_1491_, lean_object* v_as_1492_, size_t v_sz_1493_, size_t v_i_1494_, lean_object* v_b_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_a_1500_; uint8_t v___x_1504_; 
v___x_1504_ = lean_usize_dec_lt(v_i_1494_, v_sz_1493_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
lean_dec_ref(v_a_1491_);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_b_1495_);
return v___x_1505_;
}
else
{
lean_object* v___x_1506_; lean_object* v_a_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1506_ = lean_box(0);
v_a_1507_ = lean_array_uget_borrowed(v_as_1492_, v_i_1494_);
lean_inc(v_a_1507_);
lean_inc_ref(v_a_1491_);
v___x_1508_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_postprocessMessage___boxed), 5, 2);
lean_closure_set(v___x_1508_, 0, v_a_1491_);
lean_closure_set(v___x_1508_, 1, v_a_1507_);
v___x_1509_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1508_, v___y_1496_, v___y_1497_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
if (lean_obj_tag(v_a_1510_) == 1)
{
lean_object* v_val_1511_; lean_object* v___x_1512_; lean_object* v_env_1513_; lean_object* v_messages_1514_; lean_object* v_scopes_1515_; lean_object* v_usedQuotCtxts_1516_; lean_object* v_nextMacroScope_1517_; lean_object* v_maxRecDepth_1518_; lean_object* v_ngen_1519_; lean_object* v_auxDeclNGen_1520_; lean_object* v_infoState_1521_; lean_object* v_traceState_1522_; lean_object* v_snapshotTasks_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1532_; 
v_val_1511_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_val_1511_);
lean_dec_ref_known(v_a_1510_, 1);
v___x_1512_ = lean_st_ref_take(v___y_1497_);
v_env_1513_ = lean_ctor_get(v___x_1512_, 0);
v_messages_1514_ = lean_ctor_get(v___x_1512_, 1);
v_scopes_1515_ = lean_ctor_get(v___x_1512_, 2);
v_usedQuotCtxts_1516_ = lean_ctor_get(v___x_1512_, 3);
v_nextMacroScope_1517_ = lean_ctor_get(v___x_1512_, 4);
v_maxRecDepth_1518_ = lean_ctor_get(v___x_1512_, 5);
v_ngen_1519_ = lean_ctor_get(v___x_1512_, 6);
v_auxDeclNGen_1520_ = lean_ctor_get(v___x_1512_, 7);
v_infoState_1521_ = lean_ctor_get(v___x_1512_, 8);
v_traceState_1522_ = lean_ctor_get(v___x_1512_, 9);
v_snapshotTasks_1523_ = lean_ctor_get(v___x_1512_, 10);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1525_ = v___x_1512_;
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_snapshotTasks_1523_);
lean_inc(v_traceState_1522_);
lean_inc(v_infoState_1521_);
lean_inc(v_auxDeclNGen_1520_);
lean_inc(v_ngen_1519_);
lean_inc(v_maxRecDepth_1518_);
lean_inc(v_nextMacroScope_1517_);
lean_inc(v_usedQuotCtxts_1516_);
lean_inc(v_scopes_1515_);
lean_inc(v_messages_1514_);
lean_inc(v_env_1513_);
lean_dec(v___x_1512_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1527_ = l_Lean_MessageLog_add(v_val_1511_, v_messages_1514_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 1, v___x_1527_);
v___x_1529_ = v___x_1525_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_env_1513_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_scopes_1515_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_usedQuotCtxts_1516_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_nextMacroScope_1517_);
lean_ctor_set(v_reuseFailAlloc_1531_, 5, v_maxRecDepth_1518_);
lean_ctor_set(v_reuseFailAlloc_1531_, 6, v_ngen_1519_);
lean_ctor_set(v_reuseFailAlloc_1531_, 7, v_auxDeclNGen_1520_);
lean_ctor_set(v_reuseFailAlloc_1531_, 8, v_infoState_1521_);
lean_ctor_set(v_reuseFailAlloc_1531_, 9, v_traceState_1522_);
lean_ctor_set(v_reuseFailAlloc_1531_, 10, v_snapshotTasks_1523_);
v___x_1529_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_st_ref_set(v___y_1497_, v___x_1529_);
v_a_1500_ = v___x_1506_;
goto v___jp_1499_;
}
}
}
else
{
lean_dec(v_a_1510_);
v_a_1500_ = v___x_1506_;
goto v___jp_1499_;
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1563_; 
v_a_1533_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1535_ = v___x_1509_;
v_isShared_1536_ = v_isSharedCheck_1563_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1509_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1563_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
uint8_t v___x_1537_; 
v___x_1537_ = l_Lean_Exception_isInterrupt(v_a_1533_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_del_object(v___x_1535_);
v___x_1538_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_a_1533_, v___y_1496_, v___y_1497_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1539_; lean_object* v_env_1540_; lean_object* v_messages_1541_; lean_object* v_scopes_1542_; lean_object* v_usedQuotCtxts_1543_; lean_object* v_nextMacroScope_1544_; lean_object* v_maxRecDepth_1545_; lean_object* v_ngen_1546_; lean_object* v_auxDeclNGen_1547_; lean_object* v_infoState_1548_; lean_object* v_traceState_1549_; lean_object* v_snapshotTasks_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref_known(v___x_1538_, 1);
v___x_1539_ = lean_st_ref_take(v___y_1497_);
v_env_1540_ = lean_ctor_get(v___x_1539_, 0);
v_messages_1541_ = lean_ctor_get(v___x_1539_, 1);
v_scopes_1542_ = lean_ctor_get(v___x_1539_, 2);
v_usedQuotCtxts_1543_ = lean_ctor_get(v___x_1539_, 3);
v_nextMacroScope_1544_ = lean_ctor_get(v___x_1539_, 4);
v_maxRecDepth_1545_ = lean_ctor_get(v___x_1539_, 5);
v_ngen_1546_ = lean_ctor_get(v___x_1539_, 6);
v_auxDeclNGen_1547_ = lean_ctor_get(v___x_1539_, 7);
v_infoState_1548_ = lean_ctor_get(v___x_1539_, 8);
v_traceState_1549_ = lean_ctor_get(v___x_1539_, 9);
v_snapshotTasks_1550_ = lean_ctor_get(v___x_1539_, 10);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1552_ = v___x_1539_;
v_isShared_1553_ = v_isSharedCheck_1559_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_snapshotTasks_1550_);
lean_inc(v_traceState_1549_);
lean_inc(v_infoState_1548_);
lean_inc(v_auxDeclNGen_1547_);
lean_inc(v_ngen_1546_);
lean_inc(v_maxRecDepth_1545_);
lean_inc(v_nextMacroScope_1544_);
lean_inc(v_usedQuotCtxts_1543_);
lean_inc(v_scopes_1542_);
lean_inc(v_messages_1541_);
lean_inc(v_env_1540_);
lean_dec(v___x_1539_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1559_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1556_; 
lean_inc(v_a_1507_);
v___x_1554_ = l_Lean_MessageLog_add(v_a_1507_, v_messages_1541_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 1, v___x_1554_);
v___x_1556_ = v___x_1552_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_env_1540_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_scopes_1542_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_usedQuotCtxts_1543_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_nextMacroScope_1544_);
lean_ctor_set(v_reuseFailAlloc_1558_, 5, v_maxRecDepth_1545_);
lean_ctor_set(v_reuseFailAlloc_1558_, 6, v_ngen_1546_);
lean_ctor_set(v_reuseFailAlloc_1558_, 7, v_auxDeclNGen_1547_);
lean_ctor_set(v_reuseFailAlloc_1558_, 8, v_infoState_1548_);
lean_ctor_set(v_reuseFailAlloc_1558_, 9, v_traceState_1549_);
lean_ctor_set(v_reuseFailAlloc_1558_, 10, v_snapshotTasks_1550_);
v___x_1556_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_st_ref_set(v___y_1497_, v___x_1556_);
v_a_1500_ = v___x_1506_;
goto v___jp_1499_;
}
}
}
else
{
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_dec_ref_known(v___x_1538_, 1);
v_a_1500_ = v___x_1506_;
goto v___jp_1499_;
}
else
{
lean_dec_ref(v_a_1491_);
return v___x_1538_;
}
}
}
else
{
lean_object* v___x_1561_; 
lean_dec_ref(v_a_1491_);
if (v_isShared_1536_ == 0)
{
v___x_1561_ = v___x_1535_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1533_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
v___jp_1499_:
{
size_t v___x_1501_; size_t v___x_1502_; 
v___x_1501_ = ((size_t)1ULL);
v___x_1502_ = lean_usize_add(v_i_1494_, v___x_1501_);
v_i_1494_ = v___x_1502_;
v_b_1495_ = v_a_1500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2___boxed(lean_object* v_a_1564_, lean_object* v_as_1565_, lean_object* v_sz_1566_, lean_object* v_i_1567_, lean_object* v_b_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
size_t v_sz_boxed_1572_; size_t v_i_boxed_1573_; lean_object* v_res_1574_; 
v_sz_boxed_1572_ = lean_unbox_usize(v_sz_1566_);
lean_dec(v_sz_1566_);
v_i_boxed_1573_ = lean_unbox_usize(v_i_1567_);
lean_dec(v_i_1567_);
v_res_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_1564_, v_as_1565_, v_sz_boxed_1572_, v_i_boxed_1573_, v_b_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec_ref(v_as_1565_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(lean_object* v_x_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = ((lean_object*)(l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3));
lean_inc(v_x_1575_);
v___x_1580_ = l_Lean_Syntax_isOfKind(v_x_1575_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec(v_x_1575_);
v___x_1581_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; lean_object* v_post_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v_a_1587_; lean_object* v___y_1611_; lean_object* v___x_1621_; 
v___x_1582_ = lean_unsigned_to_nat(1u);
v_post_1583_ = l_Lean_Syntax_getArg(v_x_1575_, v___x_1582_);
v___x_1584_ = lean_unsigned_to_nat(3u);
v___x_1585_ = l_Lean_Syntax_getArg(v_x_1575_, v___x_1584_);
lean_dec(v_x_1575_);
v___x_1621_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_1583_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1621_) == 0)
{
v___y_1611_ = v___x_1621_;
goto v___jp_1610_;
}
else
{
lean_object* v_a_1622_; uint8_t v___x_1623_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
v___x_1623_ = l_Lean_Exception_isInterrupt(v_a_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; 
lean_dec_ref_known(v___x_1621_, 1);
v___x_1624_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_a_1622_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v___f_1625_; 
lean_dec_ref_known(v___x_1624_, 1);
v___f_1625_ = ((lean_object*)(l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___closed__0));
v_a_1587_ = v___f_1625_;
goto v___jp_1586_;
}
else
{
lean_dec(v___x_1585_);
return v___x_1624_;
}
}
else
{
lean_dec(v_a_1622_);
v___y_1611_ = v___x_1621_;
goto v___jp_1610_;
}
}
v___jp_1586_:
{
lean_object* v___x_1588_; 
v___x_1588_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_runAndCollectMessages(v___x_1585_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1590_; size_t v_sz_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1588_, 1);
v___x_1590_ = lean_box(0);
v_sz_1591_ = lean_array_size(v_a_1589_);
v___x_1592_ = ((size_t)0ULL);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_1587_, v_a_1589_, v_sz_1591_, v___x_1592_, v___x_1590_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1589_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; 
v_unused_1601_ = lean_ctor_get(v___x_1593_, 0);
lean_dec(v_unused_1601_);
v___x_1595_ = v___x_1593_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v___x_1593_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1590_);
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1590_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
else
{
return v___x_1593_;
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec_ref(v_a_1587_);
v_a_1602_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1588_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1588_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
v___jp_1610_:
{
if (lean_obj_tag(v___y_1611_) == 0)
{
lean_object* v_a_1612_; 
v_a_1612_ = lean_ctor_get(v___y_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___y_1611_, 1);
v_a_1587_ = v_a_1612_;
goto v___jp_1586_;
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v___x_1585_);
v_a_1613_ = lean_ctor_get(v___y_1611_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___y_1611_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___y_1611_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___y_1611_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___boxed(lean_object* v_x_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(v_x_1626_, v_a_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(lean_object* v_msgData_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v_msgData_1631_, v___y_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(v_msgData_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f(lean_object* v_x_1641_){
_start:
{
if (lean_obj_tag(v_x_1641_) == 0)
{
lean_object* v_data_1642_; lean_object* v___x_1643_; 
v_data_1642_ = lean_ctor_get(v_x_1641_, 0);
lean_inc_ref(v_data_1642_);
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v_data_1642_);
return v___x_1643_;
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_box(0);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f___boxed(lean_object* v_x_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_x_1645_);
lean_dec_ref(v_x_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f(lean_object* v_t_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_1647_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_box(0);
return v___x_1649_;
}
else
{
lean_object* v_val_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
v_val_1650_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1652_ = v___x_1648_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_val_1650_);
lean_dec(v___x_1648_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v_cls_1654_; lean_object* v___x_1656_; 
v_cls_1654_ = lean_ctor_get(v_val_1650_, 0);
lean_inc(v_cls_1654_);
lean_dec(v_val_1650_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v_cls_1654_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_cls_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f___boxed(lean_object* v_t_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_1659_);
lean_dec_ref(v_t_1659_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children(lean_object* v_x_1663_){
_start:
{
if (lean_obj_tag(v_x_1663_) == 0)
{
lean_object* v_children_1664_; 
v_children_1664_ = lean_ctor_get(v_x_1663_, 2);
lean_inc_ref(v_children_1664_);
return v_children_1664_;
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_children___closed__0));
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children___boxed(lean_object* v_x_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_PostprocessTraces_TraceTree_children(v_x_1666_);
lean_dec_ref(v_x_1666_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_withChildren(lean_object* v_t_1668_, lean_object* v_children_1669_){
_start:
{
if (lean_obj_tag(v_t_1668_) == 0)
{
lean_object* v_data_1670_; lean_object* v_msg_1671_; lean_object* v_wrap_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
v_data_1670_ = lean_ctor_get(v_t_1668_, 0);
v_msg_1671_ = lean_ctor_get(v_t_1668_, 1);
v_wrap_1672_ = lean_ctor_get(v_t_1668_, 3);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_t_1668_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; 
v_unused_1680_ = lean_ctor_get(v_t_1668_, 2);
lean_dec(v_unused_1680_);
v___x_1674_ = v_t_1668_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_wrap_1672_);
lean_inc(v_msg_1671_);
lean_inc(v_data_1670_);
lean_dec(v_t_1668_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 2, v_children_1669_);
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_data_1670_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_msg_1671_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v_children_1669_);
lean_ctor_set(v_reuseFailAlloc_1678_, 3, v_wrap_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_dec_ref(v_children_1669_);
return v_t_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_modifyData(lean_object* v_t_1681_, lean_object* v_f_1682_){
_start:
{
if (lean_obj_tag(v_t_1681_) == 0)
{
lean_object* v_data_1683_; lean_object* v_msg_1684_; lean_object* v_children_1685_; lean_object* v_wrap_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1694_; 
v_data_1683_ = lean_ctor_get(v_t_1681_, 0);
v_msg_1684_ = lean_ctor_get(v_t_1681_, 1);
v_children_1685_ = lean_ctor_get(v_t_1681_, 2);
v_wrap_1686_ = lean_ctor_get(v_t_1681_, 3);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_t_1681_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1688_ = v_t_1681_;
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_wrap_1686_);
lean_inc(v_children_1685_);
lean_inc(v_msg_1684_);
lean_inc(v_data_1683_);
lean_dec(v_t_1681_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_apply_1(v_f_1682_, v_data_1683_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_msg_1684_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_children_1685_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_wrap_1686_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
else
{
lean_dec_ref(v_f_1682_);
return v_t_1681_;
}
}
}
static double _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0(void){
_start:
{
lean_object* v___x_1695_; double v___x_1696_; 
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = lean_float_of_nat(v___x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT double l_Lean_PostprocessTraces_TraceTree_elapsed(lean_object* v_t_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_1697_);
if (lean_obj_tag(v___x_1698_) == 0)
{
double v___x_1699_; 
v___x_1699_ = lean_float_once(&l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0, &l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0_once, _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0);
return v___x_1699_;
}
else
{
lean_object* v_val_1700_; double v_startTime_1701_; double v_stopTime_1702_; double v___x_1703_; 
v_val_1700_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v___x_1698_, 1);
v_startTime_1701_ = lean_ctor_get_float(v_val_1700_, sizeof(void*)*3);
v_stopTime_1702_ = lean_ctor_get_float(v_val_1700_, sizeof(void*)*3 + 8);
lean_dec(v_val_1700_);
v___x_1703_ = lean_float_sub(v_stopTime_1702_, v_startTime_1701_);
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_elapsed___boxed(lean_object* v_t_1704_){
_start:
{
double v_res_1705_; lean_object* v_r_1706_; 
v_res_1705_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_1704_);
lean_dec_ref(v_t_1704_);
v_r_1706_ = lean_box_float(v_res_1705_);
return v_r_1706_;
}
}
LEAN_EXPORT double l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(lean_object* v_as_1707_, size_t v_i_1708_, size_t v_stop_1709_, double v_b_1710_){
_start:
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_usize_dec_eq(v_i_1708_, v_stop_1709_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; double v___x_1713_; double v___x_1714_; size_t v___x_1715_; size_t v___x_1716_; 
v___x_1712_ = lean_array_uget_borrowed(v_as_1707_, v_i_1708_);
v___x_1713_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v___x_1712_);
v___x_1714_ = lean_float_add(v_b_1710_, v___x_1713_);
v___x_1715_ = ((size_t)1ULL);
v___x_1716_ = lean_usize_add(v_i_1708_, v___x_1715_);
v_i_1708_ = v___x_1716_;
v_b_1710_ = v___x_1714_;
goto _start;
}
else
{
return v_b_1710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0___boxed(lean_object* v_as_1718_, lean_object* v_i_1719_, lean_object* v_stop_1720_, lean_object* v_b_1721_){
_start:
{
size_t v_i_boxed_1722_; size_t v_stop_boxed_1723_; double v_b_boxed_1724_; double v_res_1725_; lean_object* v_r_1726_; 
v_i_boxed_1722_ = lean_unbox_usize(v_i_1719_);
lean_dec(v_i_1719_);
v_stop_boxed_1723_ = lean_unbox_usize(v_stop_1720_);
lean_dec(v_stop_1720_);
v_b_boxed_1724_ = lean_unbox_float(v_b_1721_);
lean_dec_ref(v_b_1721_);
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v_as_1718_, v_i_boxed_1722_, v_stop_boxed_1723_, v_b_boxed_1724_);
lean_dec_ref(v_as_1718_);
v_r_1726_ = lean_box_float(v_res_1725_);
return v_r_1726_;
}
}
LEAN_EXPORT double l_Lean_PostprocessTraces_TraceTree_selfElapsed(lean_object* v_t_1727_){
_start:
{
lean_object* v___x_1728_; double v___x_1729_; double v___x_1730_; double v___y_1732_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1728_ = lean_unsigned_to_nat(0u);
v___x_1729_ = lean_float_once(&l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0, &l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0_once, _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0);
v___x_1730_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_1727_);
v___x_1735_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_1727_);
v___x_1736_ = lean_array_get_size(v___x_1735_);
v___x_1737_ = lean_nat_dec_lt(v___x_1728_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_dec_ref(v___x_1735_);
v___y_1732_ = v___x_1729_;
goto v___jp_1731_;
}
else
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_nat_dec_le(v___x_1736_, v___x_1736_);
if (v___x_1738_ == 0)
{
if (v___x_1737_ == 0)
{
lean_dec_ref(v___x_1735_);
v___y_1732_ = v___x_1729_;
goto v___jp_1731_;
}
else
{
size_t v___x_1739_; size_t v___x_1740_; double v___x_1741_; 
v___x_1739_ = ((size_t)0ULL);
v___x_1740_ = lean_usize_of_nat(v___x_1736_);
v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v___x_1735_, v___x_1739_, v___x_1740_, v___x_1729_);
lean_dec_ref(v___x_1735_);
v___y_1732_ = v___x_1741_;
goto v___jp_1731_;
}
}
else
{
size_t v___x_1742_; size_t v___x_1743_; double v___x_1744_; 
v___x_1742_ = ((size_t)0ULL);
v___x_1743_ = lean_usize_of_nat(v___x_1736_);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v___x_1735_, v___x_1742_, v___x_1743_, v___x_1729_);
lean_dec_ref(v___x_1735_);
v___y_1732_ = v___x_1744_;
goto v___jp_1731_;
}
}
v___jp_1731_:
{
double v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = lean_float_sub(v___x_1730_, v___y_1732_);
v___x_1734_ = lean_float_decLe(v___x_1729_, v___x_1733_);
if (v___x_1734_ == 0)
{
return v___x_1729_;
}
else
{
return v___x_1733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_selfElapsed___boxed(lean_object* v_t_1745_){
_start:
{
double v_res_1746_; lean_object* v_r_1747_; 
v_res_1746_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_t_1745_);
lean_dec_ref(v_t_1745_);
v_r_1747_ = lean_box_float(v_res_1746_);
return v_r_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText(lean_object* v_x_1749_){
_start:
{
if (lean_obj_tag(v_x_1749_) == 0)
{
lean_object* v_data_1751_; lean_object* v_msg_1752_; lean_object* v_wrap_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v_result_x3f_1756_; 
v_data_1751_ = lean_ctor_get(v_x_1749_, 0);
lean_inc_ref(v_data_1751_);
v_msg_1752_ = lean_ctor_get(v_x_1749_, 1);
lean_inc_ref(v_msg_1752_);
v_wrap_1753_ = lean_ctor_get(v_x_1749_, 3);
lean_inc_ref(v_wrap_1753_);
lean_dec_ref_known(v_x_1749_, 4);
v___x_1754_ = lean_apply_1(v_wrap_1753_, v_msg_1752_);
v___x_1755_ = l_Lean_MessageData_toString(v___x_1754_);
v_result_x3f_1756_ = lean_ctor_get(v_data_1751_, 1);
lean_inc(v_result_x3f_1756_);
lean_dec_ref(v_data_1751_);
if (lean_obj_tag(v_result_x3f_1756_) == 0)
{
return v___x_1755_;
}
else
{
lean_object* v_val_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_val_1757_ = lean_ctor_get(v_result_x3f_1756_, 0);
lean_inc(v_val_1757_);
lean_dec_ref_known(v_result_x3f_1756_, 1);
v___x_1758_ = lean_unbox(v_val_1757_);
lean_dec(v_val_1757_);
v___x_1759_ = l_Lean_TraceResult_toEmoji(v___x_1758_);
v___x_1760_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_headText___closed__0));
v___x_1761_ = lean_string_append(v___x_1759_, v___x_1760_);
v___x_1762_ = lean_string_append(v___x_1761_, v___x_1755_);
lean_dec_ref(v___x_1755_);
return v___x_1762_;
}
}
else
{
lean_object* v_msg_1763_; lean_object* v___x_1764_; 
v_msg_1763_ = lean_ctor_get(v_x_1749_, 0);
lean_inc_ref(v_msg_1763_);
lean_dec_ref_known(v_x_1749_, 1);
v___x_1764_ = l_Lean_MessageData_toString(v_msg_1763_);
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText___boxed(lean_object* v_x_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_PostprocessTraces_TraceTree_headText(v_x_1765_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f(lean_object* v_t_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_1768_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_box(0);
return v___x_1770_;
}
else
{
lean_object* v_val_1771_; lean_object* v_result_x3f_1772_; 
v_val_1771_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_val_1771_);
lean_dec_ref_known(v___x_1769_, 1);
v_result_x3f_1772_ = lean_ctor_get(v_val_1771_, 1);
lean_inc(v_result_x3f_1772_);
lean_dec(v_val_1771_);
return v_result_x3f_1772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f___boxed(lean_object* v_t_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_1773_);
lean_dec_ref(v_t_1773_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees(lean_object* v_p_1775_, lean_object* v_t_1776_, lean_object* v_acc_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v___x_1781_; 
lean_inc_ref(v_p_1775_);
lean_inc(v_a_1779_);
lean_inc_ref(v_a_1778_);
lean_inc_ref(v_t_1776_);
v___x_1781_ = lean_apply_4(v_p_1775_, v_t_1776_, v_a_1778_, v_a_1779_, lean_box(0));
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1808_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1808_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1808_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
uint8_t v___x_1786_; 
v___x_1786_ = lean_unbox(v_a_1782_);
lean_dec(v_a_1782_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1787_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_1776_);
lean_dec_ref(v_t_1776_);
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_array_get_size(v___x_1787_);
v___x_1790_ = lean_nat_dec_lt(v___x_1788_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1792_; 
lean_dec_ref(v___x_1787_);
lean_dec_ref(v_p_1775_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v_acc_1777_);
v___x_1792_ = v___x_1784_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_acc_1777_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
else
{
uint8_t v___x_1794_; 
v___x_1794_ = lean_nat_dec_le(v___x_1789_, v___x_1789_);
if (v___x_1794_ == 0)
{
if (v___x_1790_ == 0)
{
lean_object* v___x_1796_; 
lean_dec_ref(v___x_1787_);
lean_dec_ref(v_p_1775_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v_acc_1777_);
v___x_1796_ = v___x_1784_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_acc_1777_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
else
{
size_t v___x_1798_; size_t v___x_1799_; lean_object* v___x_1800_; 
lean_del_object(v___x_1784_);
v___x_1798_ = ((size_t)0ULL);
v___x_1799_ = lean_usize_of_nat(v___x_1789_);
v___x_1800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_1775_, v___x_1787_, v___x_1798_, v___x_1799_, v_acc_1777_, v_a_1778_, v_a_1779_);
lean_dec_ref(v___x_1787_);
return v___x_1800_;
}
}
else
{
size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
lean_del_object(v___x_1784_);
v___x_1801_ = ((size_t)0ULL);
v___x_1802_ = lean_usize_of_nat(v___x_1789_);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_1775_, v___x_1787_, v___x_1801_, v___x_1802_, v_acc_1777_, v_a_1778_, v_a_1779_);
lean_dec_ref(v___x_1787_);
return v___x_1803_;
}
}
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
lean_dec_ref(v_p_1775_);
v___x_1804_ = lean_array_push(v_acc_1777_, v_t_1776_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1804_);
v___x_1806_ = v___x_1784_;
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
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec_ref(v_acc_1777_);
lean_dec_ref(v_t_1776_);
lean_dec_ref(v_p_1775_);
v_a_1809_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1781_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1781_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(lean_object* v_p_1817_, lean_object* v_as_1818_, size_t v_i_1819_, size_t v_stop_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
uint8_t v___x_1825_; 
v___x_1825_ = lean_usize_dec_eq(v_i_1819_, v_stop_1820_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_array_uget_borrowed(v_as_1818_, v_i_1819_);
lean_inc(v___x_1826_);
lean_inc_ref(v_p_1817_);
v___x_1827_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_1817_, v___x_1826_, v_b_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; size_t v___x_1829_; size_t v___x_1830_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1829_ = ((size_t)1ULL);
v___x_1830_ = lean_usize_add(v_i_1819_, v___x_1829_);
v_i_1819_ = v___x_1830_;
v_b_1821_ = v_a_1828_;
goto _start;
}
else
{
lean_dec_ref(v_p_1817_);
return v___x_1827_;
}
}
else
{
lean_object* v___x_1832_; 
lean_dec_ref(v_p_1817_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_b_1821_);
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0___boxed(lean_object* v_p_1833_, lean_object* v_as_1834_, lean_object* v_i_1835_, lean_object* v_stop_1836_, lean_object* v_b_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
size_t v_i_boxed_1841_; size_t v_stop_boxed_1842_; lean_object* v_res_1843_; 
v_i_boxed_1841_ = lean_unbox_usize(v_i_1835_);
lean_dec(v_i_1835_);
v_stop_boxed_1842_ = lean_unbox_usize(v_stop_1836_);
lean_dec(v_stop_1836_);
v_res_1843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_1833_, v_as_1834_, v_i_boxed_1841_, v_stop_boxed_1842_, v_b_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec_ref(v_as_1834_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees___boxed(lean_object* v_p_1844_, lean_object* v_t_1845_, lean_object* v_acc_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_1844_, v_t_1845_, v_acc_1846_, v_a_1847_, v_a_1848_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(lean_object* v_p_1851_, lean_object* v_as_1852_, lean_object* v_start_1853_, lean_object* v_stop_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1858_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_children___closed__0));
v___x_1859_ = lean_nat_dec_lt(v_start_1853_, v_stop_1854_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref(v_p_1851_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = lean_array_get_size(v_as_1852_);
v___x_1862_ = lean_nat_dec_le(v_stop_1854_, v___x_1861_);
if (v___x_1862_ == 0)
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_nat_dec_lt(v_start_1853_, v___x_1861_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; 
lean_dec_ref(v_p_1851_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1858_);
return v___x_1864_;
}
else
{
size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = lean_usize_of_nat(v_start_1853_);
v___x_1866_ = lean_usize_of_nat(v___x_1861_);
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_1851_, v_as_1852_, v___x_1865_, v___x_1866_, v___x_1858_, v___y_1855_, v___y_1856_);
return v___x_1867_;
}
}
else
{
size_t v___x_1868_; size_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_usize_of_nat(v_start_1853_);
v___x_1869_ = lean_usize_of_nat(v_stop_1854_);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_1851_, v_as_1852_, v___x_1868_, v___x_1869_, v___x_1858_, v___y_1855_, v___y_1856_);
return v___x_1870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees(lean_object* v_p_1871_, lean_object* v_t_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1876_; 
lean_inc_ref(v_p_1871_);
lean_inc(v_a_1874_);
lean_inc_ref(v_a_1873_);
lean_inc_ref(v_t_1872_);
v___x_1876_ = lean_apply_4(v_p_1871_, v_t_1872_, v_a_1873_, v_a_1874_, lean_box(0));
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1914_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1914_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1914_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
uint8_t v___x_1881_; 
v___x_1881_ = lean_unbox(v_a_1877_);
lean_dec(v_a_1877_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_del_object(v___x_1879_);
v___x_1882_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_1872_);
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = lean_array_get_size(v___x_1882_);
v___x_1885_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(v_p_1871_, v___x_1882_, v___x_1883_, v___x_1884_, v_a_1873_, v_a_1874_);
lean_dec_ref(v___x_1882_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1901_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1901_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1901_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = lean_array_get_size(v_a_1886_);
v___x_1891_ = lean_nat_dec_eq(v___x_1890_, v___x_1883_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1892_ = l_Lean_PostprocessTraces_TraceTree_withChildren(v_t_1872_, v_a_1886_);
v___x_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1893_);
v___x_1895_ = v___x_1888_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
lean_dec(v_a_1886_);
lean_dec_ref(v_t_1872_);
v___x_1897_ = lean_box(0);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1897_);
v___x_1899_ = v___x_1888_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v_t_1872_);
v_a_1902_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1885_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1885_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_dec_ref(v_p_1871_);
v___x_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1910_, 0, v_t_1872_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1910_);
v___x_1912_ = v___x_1879_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v_t_1872_);
lean_dec_ref(v_p_1871_);
v_a_1915_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1876_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1876_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(lean_object* v_p_1923_, lean_object* v_as_1924_, size_t v_i_1925_, size_t v_stop_1926_, lean_object* v_b_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
uint8_t v___x_1931_; 
v___x_1931_ = lean_usize_dec_eq(v_i_1925_, v_stop_1926_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_array_uget_borrowed(v_as_1924_, v_i_1925_);
lean_inc(v___x_1932_);
lean_inc_ref(v_p_1923_);
v___x_1933_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_1923_, v___x_1932_, v___y_1928_, v___y_1929_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v_a_1936_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
if (lean_obj_tag(v_a_1934_) == 0)
{
v_a_1936_ = v_b_1927_;
goto v___jp_1935_;
}
else
{
lean_object* v_val_1940_; lean_object* v___x_1941_; 
v_val_1940_ = lean_ctor_get(v_a_1934_, 0);
lean_inc(v_val_1940_);
lean_dec_ref_known(v_a_1934_, 1);
v___x_1941_ = lean_array_push(v_b_1927_, v_val_1940_);
v_a_1936_ = v___x_1941_;
goto v___jp_1935_;
}
v___jp_1935_:
{
size_t v___x_1937_; size_t v___x_1938_; 
v___x_1937_ = ((size_t)1ULL);
v___x_1938_ = lean_usize_add(v_i_1925_, v___x_1937_);
v_i_1925_ = v___x_1938_;
v_b_1927_ = v_a_1936_;
goto _start;
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v_b_1927_);
lean_dec_ref(v_p_1923_);
v_a_1942_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1933_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1933_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v___x_1950_; 
lean_dec_ref(v_p_1923_);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v_b_1927_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0___boxed(lean_object* v_p_1951_, lean_object* v_as_1952_, lean_object* v_i_1953_, lean_object* v_stop_1954_, lean_object* v_b_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
size_t v_i_boxed_1959_; size_t v_stop_boxed_1960_; lean_object* v_res_1961_; 
v_i_boxed_1959_ = lean_unbox_usize(v_i_1953_);
lean_dec(v_i_1953_);
v_stop_boxed_1960_ = lean_unbox_usize(v_stop_1954_);
lean_dec(v_stop_1954_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_1951_, v_as_1952_, v_i_boxed_1959_, v_stop_boxed_1960_, v_b_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec_ref(v_as_1952_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0___boxed(lean_object* v_p_1962_, lean_object* v_as_1963_, lean_object* v_start_1964_, lean_object* v_stop_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(v_p_1962_, v_as_1963_, v_start_1964_, v_stop_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v_stop_1965_);
lean_dec(v_start_1964_);
lean_dec_ref(v_as_1963_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees___boxed(lean_object* v_p_1970_, lean_object* v_t_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_1970_, v_t_1971_, v_a_1972_, v_a_1973_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(lean_object* v_s_1976_, lean_object* v___x_1977_, lean_object* v___x_1978_, lean_object* v_a_1979_, lean_object* v_b_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_box(0);
switch(lean_obj_tag(v_a_1979_))
{
case 0:
{
lean_object* v_pos_1982_; lean_object* v___x_1983_; 
v_pos_1982_ = lean_ctor_get(v_a_1979_, 0);
lean_inc(v_pos_1982_);
lean_dec_ref_known(v_a_1979_, 1);
v___x_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_pos_1982_);
return v___x_1983_;
}
case 1:
{
lean_object* v_pos_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1993_; 
v_pos_1984_ = lean_ctor_get(v_a_1979_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1986_ = v_a_1979_;
v_isShared_1987_ = v_isSharedCheck_1993_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_pos_1984_);
lean_dec(v_a_1979_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1993_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1988_ = lean_string_utf8_next_fast(v_s_1976_, v_pos_1984_);
lean_dec(v_pos_1984_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set_tag(v___x_1986_, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1988_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
v_a_1979_ = v___x_1990_;
v_b_1980_ = v___x_1981_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1994_; lean_object* v_table_1995_; lean_object* v_stackPos_1996_; lean_object* v_needlePos_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2048_; 
v_needle_1994_ = lean_ctor_get(v_a_1979_, 0);
v_table_1995_ = lean_ctor_get(v_a_1979_, 1);
v_stackPos_1996_ = lean_ctor_get(v_a_1979_, 2);
v_needlePos_1997_ = lean_ctor_get(v_a_1979_, 3);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_1999_ = v_a_1979_;
v_isShared_2000_ = v_isSharedCheck_2048_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_needlePos_1997_);
lean_inc(v_stackPos_1996_);
lean_inc(v_table_1995_);
lean_inc(v_needle_1994_);
lean_dec(v_a_1979_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2048_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v_str_2001_; lean_object* v_startInclusive_2002_; lean_object* v_endExclusive_2003_; lean_object* v_basePos_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v_str_2001_ = lean_ctor_get(v_needle_1994_, 0);
v_startInclusive_2002_ = lean_ctor_get(v_needle_1994_, 1);
v_endExclusive_2003_ = lean_ctor_get(v_needle_1994_, 2);
v_basePos_2004_ = lean_nat_sub(v_stackPos_1996_, v_needlePos_1997_);
v___x_2005_ = lean_nat_sub(v_endExclusive_2003_, v_startInclusive_2002_);
v___x_2006_ = lean_nat_add(v_basePos_2004_, v___x_2005_);
v___x_2007_ = lean_nat_dec_le(v___x_2006_, v___x_1978_);
lean_dec(v___x_2006_);
if (v___x_2007_ == 0)
{
uint8_t v___x_2008_; 
lean_dec(v___x_2005_);
lean_del_object(v___x_1999_);
lean_dec(v_needlePos_1997_);
lean_dec(v_stackPos_1996_);
lean_dec_ref(v_table_1995_);
lean_dec_ref(v_needle_1994_);
v___x_2008_ = lean_nat_dec_lt(v_basePos_2004_, v___x_1978_);
lean_dec(v_basePos_2004_);
if (v___x_2008_ == 0)
{
lean_inc(v_b_1980_);
return v_b_1980_;
}
else
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_box(3);
v_a_1979_ = v___x_2009_;
v_b_1980_ = v___x_1981_;
goto _start;
}
}
else
{
uint8_t v_stackByte_2011_; lean_object* v___x_2012_; uint8_t v_patByte_2013_; uint8_t v___x_2014_; 
lean_dec(v_basePos_2004_);
lean_inc(v_stackPos_1996_);
v_stackByte_2011_ = lean_string_get_byte_fast(v_s_1976_, v_stackPos_1996_);
v___x_2012_ = lean_nat_add(v_startInclusive_2002_, v_needlePos_1997_);
v_patByte_2013_ = lean_string_get_byte_fast(v_str_2001_, v___x_2012_);
v___x_2014_ = lean_uint8_dec_eq(v_stackByte_2011_, v_patByte_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
lean_dec(v___x_2005_);
v___x_2015_ = lean_unsigned_to_nat(0u);
v___x_2016_ = lean_nat_dec_eq(v_needlePos_1997_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v_newNeedlePos_2019_; uint8_t v___x_2020_; 
v___x_2017_ = lean_unsigned_to_nat(1u);
v___x_2018_ = lean_nat_sub(v_needlePos_1997_, v___x_2017_);
lean_dec(v_needlePos_1997_);
v_newNeedlePos_2019_ = lean_array_fget_borrowed(v_table_1995_, v___x_2018_);
lean_dec(v___x_2018_);
v___x_2020_ = lean_nat_dec_eq(v_newNeedlePos_2019_, v___x_2015_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2022_; 
lean_inc(v_newNeedlePos_2019_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 3, v_newNeedlePos_2019_);
v___x_2022_ = v___x_1999_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_needle_1994_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_table_1995_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_stackPos_1996_);
lean_ctor_set(v_reuseFailAlloc_2024_, 3, v_newNeedlePos_2019_);
v___x_2022_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
v_a_1979_ = v___x_2022_;
v_b_1980_ = v___x_1981_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2025_; lean_object* v___x_2027_; 
v_nextStackPos_2025_ = l_String_Slice_posGE___redArg(v___x_1977_, v_stackPos_1996_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 3, v___x_2015_);
lean_ctor_set(v___x_1999_, 2, v_nextStackPos_2025_);
v___x_2027_ = v___x_1999_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_needle_1994_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_table_1995_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_nextStackPos_2025_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v___x_2015_);
v___x_2027_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
v_a_1979_ = v___x_2027_;
v_b_1980_ = v___x_1981_;
goto _start;
}
}
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v_nextStackPos_2032_; lean_object* v___x_2034_; 
lean_dec(v_needlePos_1997_);
v___x_2030_ = lean_unsigned_to_nat(1u);
v___x_2031_ = lean_nat_add(v_stackPos_1996_, v___x_2030_);
lean_dec(v_stackPos_1996_);
v_nextStackPos_2032_ = l_String_Slice_posGE___redArg(v___x_1977_, v___x_2031_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 3, v___x_2015_);
lean_ctor_set(v___x_1999_, 2, v_nextStackPos_2032_);
v___x_2034_ = v___x_1999_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_needle_1994_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_table_1995_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_nextStackPos_2032_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v___x_2015_);
v___x_2034_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
v_a_1979_ = v___x_2034_;
v_b_1980_ = v___x_1981_;
goto _start;
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v_nextStackPos_2038_; lean_object* v_nextNeedlePos_2039_; uint8_t v___x_2040_; 
v___x_2037_ = lean_unsigned_to_nat(1u);
v_nextStackPos_2038_ = lean_nat_add(v_stackPos_1996_, v___x_2037_);
lean_dec(v_stackPos_1996_);
v_nextNeedlePos_2039_ = lean_nat_add(v_needlePos_1997_, v___x_2037_);
lean_dec(v_needlePos_1997_);
v___x_2040_ = lean_nat_dec_eq(v_nextNeedlePos_2039_, v___x_2005_);
lean_dec(v___x_2005_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2042_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 3, v_nextNeedlePos_2039_);
lean_ctor_set(v___x_1999_, 2, v_nextStackPos_2038_);
v___x_2042_ = v___x_1999_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_needle_1994_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_table_1995_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_nextStackPos_2038_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_nextNeedlePos_2039_);
v___x_2042_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
v_a_1979_ = v___x_2042_;
goto _start;
}
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_del_object(v___x_1999_);
lean_dec_ref(v_table_1995_);
lean_dec_ref(v_needle_1994_);
v___x_2045_ = lean_nat_sub(v_nextStackPos_2038_, v_nextNeedlePos_2039_);
lean_dec(v_nextNeedlePos_2039_);
lean_dec(v_nextStackPos_2038_);
v___x_2046_ = l_String_Slice_pos_x21(v___x_1977_, v___x_2045_);
lean_dec(v___x_2045_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
return v___x_2047_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1980_);
return v_b_1980_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg___boxed(lean_object* v_s_2049_, lean_object* v___x_2050_, lean_object* v___x_2051_, lean_object* v_a_2052_, lean_object* v_b_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(v_s_2049_, v___x_2050_, v___x_2051_, v_a_2052_, v_b_2053_);
lean_dec(v_b_2053_);
lean_dec(v___x_2051_);
lean_dec_ref(v___x_2050_);
lean_dec_ref(v_s_2049_);
return v_res_2054_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr(lean_object* v_s_2057_, lean_object* v_pat_2058_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___y_2063_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2059_ = lean_unsigned_to_nat(0u);
v___x_2060_ = lean_string_utf8_byte_size(v_s_2057_);
lean_inc_ref(v_s_2057_);
v___x_2061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2061_, 0, v_s_2057_);
lean_ctor_set(v___x_2061_, 1, v___x_2059_);
lean_ctor_set(v___x_2061_, 2, v___x_2060_);
v___x_2068_ = lean_string_utf8_byte_size(v_pat_2058_);
v___x_2069_ = lean_nat_dec_eq(v___x_2068_, v___x_2059_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2070_, 0, v_pat_2058_);
lean_ctor_set(v___x_2070_, 1, v___x_2059_);
lean_ctor_set(v___x_2070_, 2, v___x_2068_);
v___x_2071_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2070_);
v___x_2072_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
lean_ctor_set(v___x_2072_, 2, v___x_2059_);
lean_ctor_set(v___x_2072_, 3, v___x_2059_);
v___y_2063_ = v___x_2072_;
goto v___jp_2062_;
}
else
{
lean_object* v___x_2073_; 
lean_dec_ref(v_pat_2058_);
v___x_2073_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr___closed__0));
v___y_2063_ = v___x_2073_;
goto v___jp_2062_;
}
v___jp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_box(0);
v___x_2065_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(v_s_2057_, v___x_2061_, v___x_2060_, v___y_2063_, v___x_2064_);
lean_dec_ref_known(v___x_2061_, 3);
lean_dec_ref(v_s_2057_);
if (lean_obj_tag(v___x_2065_) == 0)
{
uint8_t v___x_2066_; 
v___x_2066_ = 0;
return v___x_2066_;
}
else
{
uint8_t v___x_2067_; 
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = 1;
return v___x_2067_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr___boxed(lean_object* v_s_2074_, lean_object* v_pat_2075_){
_start:
{
uint8_t v_res_2076_; lean_object* v_r_2077_; 
v_res_2076_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr(v_s_2074_, v_pat_2075_);
v_r_2077_ = lean_box(v_res_2076_);
return v_r_2077_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0(lean_object* v_s_2078_, lean_object* v___x_2079_, lean_object* v___x_2080_, lean_object* v_inst_2081_, lean_object* v_R_2082_, lean_object* v_a_2083_, lean_object* v_b_2084_, lean_object* v_c_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(v_s_2078_, v___x_2079_, v___x_2080_, v_a_2083_, v_b_2084_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0___boxed(lean_object* v_s_2087_, lean_object* v___x_2088_, lean_object* v___x_2089_, lean_object* v_inst_2090_, lean_object* v_R_2091_, lean_object* v_a_2092_, lean_object* v_b_2093_, lean_object* v_c_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr_spec__0(v_s_2087_, v___x_2088_, v___x_2089_, v_inst_2090_, v_R_2091_, v_a_2092_, v_b_2093_, v_c_2094_);
lean_dec(v_b_2093_);
lean_dec(v___x_2089_);
lean_dec_ref(v___x_2088_);
lean_dec_ref(v_s_2087_);
return v_res_2095_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(lean_object* v_x_2096_, lean_object* v_x_2097_){
_start:
{
if (lean_obj_tag(v_x_2096_) == 0)
{
if (lean_obj_tag(v_x_2097_) == 0)
{
uint8_t v___x_2098_; 
v___x_2098_ = 1;
return v___x_2098_;
}
else
{
uint8_t v___x_2099_; 
v___x_2099_ = 0;
return v___x_2099_;
}
}
else
{
if (lean_obj_tag(v_x_2097_) == 0)
{
uint8_t v___x_2100_; 
v___x_2100_ = 0;
return v___x_2100_;
}
else
{
lean_object* v_val_2101_; lean_object* v_val_2102_; uint8_t v___x_2103_; 
v_val_2101_ = lean_ctor_get(v_x_2096_, 0);
v_val_2102_ = lean_ctor_get(v_x_2097_, 0);
v___x_2103_ = lean_name_eq(v_val_2101_, v_val_2102_);
return v___x_2103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0___boxed(lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
uint8_t v_res_2106_; lean_object* v_r_2107_; 
v_res_2106_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(v_x_2104_, v_x_2105_);
lean_dec(v_x_2105_);
lean_dec(v_x_2104_);
v_r_2107_ = lean_box(v_res_2106_);
return v_r_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg(lean_object* v_cls_2108_, lean_object* v_t_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2111_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_2109_);
v___x_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_cls_2108_);
v___x_2113_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(v___x_2111_, v___x_2112_);
lean_dec_ref_known(v___x_2112_, 1);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg___boxed(lean_object* v_cls_2116_, lean_object* v_t_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_PostprocessTraces_ofClass___redArg(v_cls_2116_, v_t_2117_);
lean_dec_ref(v_t_2117_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass(lean_object* v_cls_2120_, lean_object* v_t_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_PostprocessTraces_ofClass___redArg(v_cls_2120_, v_t_2121_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___boxed(lean_object* v_cls_2126_, lean_object* v_t_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_PostprocessTraces_ofClass(v_cls_2126_, v_t_2127_, v_a_2128_, v_a_2129_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
lean_dec_ref(v_t_2127_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg(lean_object* v_pat_2132_, lean_object* v_t_2133_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_2133_);
if (lean_obj_tag(v___x_2140_) == 0)
{
goto v___jp_2135_;
}
else
{
lean_object* v_val_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2152_; 
v_val_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2152_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_val_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2152_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
uint8_t v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2145_ = 1;
v___x_2146_ = l_Lean_Name_toString(v_val_2141_, v___x_2145_);
lean_inc_ref(v_pat_2132_);
v___x_2147_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr(v___x_2146_, v_pat_2132_);
if (v___x_2147_ == 0)
{
lean_del_object(v___x_2143_);
goto v___jp_2135_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec_ref(v_t_2133_);
lean_dec_ref(v_pat_2132_);
v___x_2148_ = lean_box(v___x_2147_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set_tag(v___x_2143_, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2148_);
v___x_2150_ = v___x_2143_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
v___jp_2135_:
{
lean_object* v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2136_ = l_Lean_PostprocessTraces_TraceTree_headText(v_t_2133_);
v___x_2137_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_containsSubstr(v___x_2136_, v_pat_2132_);
v___x_2138_ = lean_box(v___x_2137_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg___boxed(lean_object* v_pat_2153_, lean_object* v_t_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_PostprocessTraces_containsString___redArg(v_pat_2153_, v_t_2154_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString(lean_object* v_pat_2157_, lean_object* v_t_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_PostprocessTraces_containsString___redArg(v_pat_2157_, v_t_2158_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___boxed(lean_object* v_pat_2163_, lean_object* v_t_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_PostprocessTraces_containsString(v_pat_2163_, v_t_2164_, v_a_2165_, v_a_2166_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
return v_res_2168_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 0)
{
if (lean_obj_tag(v_x_2170_) == 0)
{
uint8_t v___x_2171_; 
v___x_2171_ = 1;
return v___x_2171_;
}
else
{
uint8_t v___x_2172_; 
v___x_2172_ = 0;
return v___x_2172_;
}
}
else
{
if (lean_obj_tag(v_x_2170_) == 0)
{
uint8_t v___x_2173_; 
v___x_2173_ = 0;
return v___x_2173_;
}
else
{
lean_object* v_val_2174_; lean_object* v_val_2175_; uint8_t v___x_2176_; uint8_t v___x_2177_; uint8_t v___x_2178_; 
v_val_2174_ = lean_ctor_get(v_x_2169_, 0);
v_val_2175_ = lean_ctor_get(v_x_2170_, 0);
v___x_2176_ = lean_unbox(v_val_2174_);
v___x_2177_ = lean_unbox(v_val_2175_);
v___x_2178_ = l_Lean_instBEqTraceResult_beq(v___x_2176_, v___x_2177_);
return v___x_2178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0___boxed(lean_object* v_x_2179_, lean_object* v_x_2180_){
_start:
{
uint8_t v_res_2181_; lean_object* v_r_2182_; 
v_res_2181_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v_x_2179_, v_x_2180_);
lean_dec(v_x_2180_);
lean_dec(v_x_2179_);
v_r_2182_ = lean_box(v_res_2181_);
return v_r_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___redArg(lean_object* v_t_2186_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2188_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_2186_);
v___x_2189_ = ((lean_object*)(l_Lean_PostprocessTraces_succeeded___redArg___closed__0));
v___x_2190_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_2188_, v___x_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = lean_box(v___x_2190_);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___redArg___boxed(lean_object* v_t_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_PostprocessTraces_succeeded___redArg(v_t_2193_);
lean_dec_ref(v_t_2193_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded(lean_object* v_t_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_PostprocessTraces_succeeded___redArg(v_t_2196_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___boxed(lean_object* v_t_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_PostprocessTraces_succeeded(v_t_2201_, v_a_2202_, v_a_2203_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec_ref(v_t_2201_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___redArg(lean_object* v_t_2209_){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2211_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_2209_);
v___x_2212_ = ((lean_object*)(l_Lean_PostprocessTraces_failed___redArg___closed__0));
v___x_2213_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_2211_, v___x_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(v___x_2213_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___redArg___boxed(lean_object* v_t_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_PostprocessTraces_failed___redArg(v_t_2216_);
lean_dec_ref(v_t_2216_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed(lean_object* v_t_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_PostprocessTraces_failed___redArg(v_t_2219_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___boxed(lean_object* v_t_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_PostprocessTraces_failed(v_t_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec_ref(v_t_2224_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___redArg(lean_object* v_t_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2234_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_2232_);
v___x_2235_ = ((lean_object*)(l_Lean_PostprocessTraces_errored___redArg___closed__0));
v___x_2236_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_2234_, v___x_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___redArg___boxed(lean_object* v_t_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_PostprocessTraces_errored___redArg(v_t_2239_);
lean_dec_ref(v_t_2239_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored(lean_object* v_t_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_PostprocessTraces_errored___redArg(v_t_2242_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___boxed(lean_object* v_t_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_PostprocessTraces_errored(v_t_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec_ref(v_t_2247_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg(lean_object* v_t_2252_){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2254_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_2252_);
v___x_2255_ = ((lean_object*)(l_Lean_PostprocessTraces_failed___redArg___closed__0));
v___x_2256_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_2254_, v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2257_ = ((lean_object*)(l_Lean_PostprocessTraces_errored___redArg___closed__0));
v___x_2258_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_2254_, v___x_2257_);
lean_dec(v___x_2254_);
v___x_2259_ = lean_box(v___x_2258_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec(v___x_2254_);
v___x_2261_ = lean_box(v___x_2256_);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg___boxed(lean_object* v_t_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_PostprocessTraces_unsuccessful___redArg(v_t_2263_);
lean_dec_ref(v_t_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful(lean_object* v_t_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_PostprocessTraces_unsuccessful___redArg(v_t_2266_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___boxed(lean_object* v_t_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_PostprocessTraces_unsuccessful(v_t_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec_ref(v_t_2271_);
return v_res_2275_;
}
}
static double _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0(void){
_start:
{
lean_object* v___x_2276_; double v___x_2277_; 
v___x_2276_ = lean_unsigned_to_nat(1000u);
v___x_2277_ = lean_float_of_nat(v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg(double v_ms_2278_, lean_object* v_t_2279_){
_start:
{
double v___x_2281_; double v___x_2282_; double v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2281_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_2279_);
v___x_2282_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_2283_ = lean_float_mul(v___x_2281_, v___x_2282_);
v___x_2284_ = lean_float_decLe(v_ms_2278_, v___x_2283_);
v___x_2285_ = lean_box(v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg___boxed(lean_object* v_ms_2287_, lean_object* v_t_2288_, lean_object* v_a_2289_){
_start:
{
double v_ms_boxed_2290_; lean_object* v_res_2291_; 
v_ms_boxed_2290_ = lean_unbox_float(v_ms_2287_);
lean_dec_ref(v_ms_2287_);
v_res_2291_ = l_Lean_PostprocessTraces_minTimeMs___redArg(v_ms_boxed_2290_, v_t_2288_);
lean_dec_ref(v_t_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs(double v_ms_2292_, lean_object* v_t_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_PostprocessTraces_minTimeMs___redArg(v_ms_2292_, v_t_2293_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___boxed(lean_object* v_ms_2298_, lean_object* v_t_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
double v_ms_boxed_2303_; lean_object* v_res_2304_; 
v_ms_boxed_2303_ = lean_unbox_float(v_ms_2298_);
lean_dec_ref(v_ms_2298_);
v_res_2304_ = l_Lean_PostprocessTraces_minTimeMs(v_ms_boxed_2303_, v_t_2299_, v_a_2300_, v_a_2301_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec_ref(v_t_2299_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg(double v_ms_2305_, lean_object* v_t_2306_){
_start:
{
double v___x_2308_; double v___x_2309_; double v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2308_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_t_2306_);
v___x_2309_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_2310_ = lean_float_mul(v___x_2308_, v___x_2309_);
v___x_2311_ = lean_float_decLe(v_ms_2305_, v___x_2310_);
v___x_2312_ = lean_box(v___x_2311_);
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg___boxed(lean_object* v_ms_2314_, lean_object* v_t_2315_, lean_object* v_a_2316_){
_start:
{
double v_ms_boxed_2317_; lean_object* v_res_2318_; 
v_ms_boxed_2317_ = lean_unbox_float(v_ms_2314_);
lean_dec_ref(v_ms_2314_);
v_res_2318_ = l_Lean_PostprocessTraces_minSelfTimeMs___redArg(v_ms_boxed_2317_, v_t_2315_);
lean_dec_ref(v_t_2315_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs(double v_ms_2319_, lean_object* v_t_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_PostprocessTraces_minSelfTimeMs___redArg(v_ms_2319_, v_t_2320_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___boxed(lean_object* v_ms_2325_, lean_object* v_t_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
double v_ms_boxed_2330_; lean_object* v_res_2331_; 
v_ms_boxed_2330_ = lean_unbox_float(v_ms_2325_);
lean_dec_ref(v_ms_2325_);
v_res_2331_ = l_Lean_PostprocessTraces_minSelfTimeMs(v_ms_boxed_2330_, v_t_2326_, v_a_2327_, v_a_2328_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v_t_2326_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(lean_object* v_p_2332_, lean_object* v_as_2333_, lean_object* v_start_2334_, lean_object* v_stop_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2339_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_children___closed__0));
v___x_2340_ = lean_nat_dec_lt(v_start_2334_, v_stop_2335_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; 
lean_dec_ref(v_p_2332_);
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
return v___x_2341_;
}
else
{
lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = lean_array_get_size(v_as_2333_);
v___x_2343_ = lean_nat_dec_le(v_stop_2335_, v___x_2342_);
if (v___x_2343_ == 0)
{
uint8_t v___x_2344_; 
v___x_2344_ = lean_nat_dec_lt(v_start_2334_, v___x_2342_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_dec_ref(v_p_2332_);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2339_);
return v___x_2345_;
}
else
{
size_t v___x_2346_; size_t v___x_2347_; lean_object* v___x_2348_; 
v___x_2346_ = lean_usize_of_nat(v_start_2334_);
v___x_2347_ = lean_usize_of_nat(v___x_2342_);
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_2332_, v_as_2333_, v___x_2346_, v___x_2347_, v___x_2339_, v___y_2336_, v___y_2337_);
return v___x_2348_;
}
}
else
{
size_t v___x_2349_; size_t v___x_2350_; lean_object* v___x_2351_; 
v___x_2349_ = lean_usize_of_nat(v_start_2334_);
v___x_2350_ = lean_usize_of_nat(v_stop_2335_);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_2332_, v_as_2333_, v___x_2349_, v___x_2350_, v___x_2339_, v___y_2336_, v___y_2337_);
return v___x_2351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___boxed(lean_object* v_p_2352_, lean_object* v_as_2353_, lean_object* v_start_2354_, lean_object* v_stop_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(v_p_2352_, v_as_2353_, v_start_2354_, v_stop_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v_stop_2355_);
lean_dec(v_start_2354_);
lean_dec_ref(v_as_2353_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_filterSubtrees(lean_object* v_p_2360_, lean_object* v_roots_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = lean_unsigned_to_nat(0u);
v___x_2366_ = lean_array_get_size(v_roots_2361_);
v___x_2367_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(v_p_2360_, v_roots_2361_, v___x_2365_, v___x_2366_, v_a_2362_, v_a_2363_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_filterSubtrees___boxed(lean_object* v_p_2368_, lean_object* v_roots_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_PostprocessTraces_filterSubtrees(v_p_2368_, v_roots_2369_, v_a_2370_, v_a_2371_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec_ref(v_roots_2369_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_hoist(lean_object* v_p_2374_, lean_object* v_roots_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_children___closed__0));
v___x_2381_ = lean_array_get_size(v_roots_2375_);
v___x_2382_ = lean_nat_dec_lt(v___x_2379_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; 
lean_dec_ref(v_p_2374_);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2380_);
return v___x_2383_;
}
else
{
uint8_t v___x_2384_; 
v___x_2384_ = lean_nat_dec_le(v___x_2381_, v___x_2381_);
if (v___x_2384_ == 0)
{
if (v___x_2382_ == 0)
{
lean_object* v___x_2385_; 
lean_dec_ref(v_p_2374_);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2380_);
return v___x_2385_;
}
else
{
size_t v___x_2386_; size_t v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = ((size_t)0ULL);
v___x_2387_ = lean_usize_of_nat(v___x_2381_);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_2374_, v_roots_2375_, v___x_2386_, v___x_2387_, v___x_2380_, v_a_2376_, v_a_2377_);
return v___x_2388_;
}
}
else
{
size_t v___x_2389_; size_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = ((size_t)0ULL);
v___x_2390_ = lean_usize_of_nat(v___x_2381_);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_2374_, v_roots_2375_, v___x_2389_, v___x_2390_, v___x_2380_, v_a_2376_, v_a_2377_);
return v___x_2391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_hoist___boxed(lean_object* v_p_2392_, lean_object* v_roots_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_PostprocessTraces_hoist(v_p_2392_, v_roots_2393_, v_a_2394_, v_a_2395_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
lean_dec_ref(v_roots_2393_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0(uint8_t v_a_2398_, lean_object* v_x_2399_){
_start:
{
lean_object* v_cls_2400_; lean_object* v_result_x3f_2401_; double v_startTime_2402_; double v_stopTime_2403_; lean_object* v_tag_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
v_cls_2400_ = lean_ctor_get(v_x_2399_, 0);
v_result_x3f_2401_ = lean_ctor_get(v_x_2399_, 1);
v_startTime_2402_ = lean_ctor_get_float(v_x_2399_, sizeof(void*)*3);
v_stopTime_2403_ = lean_ctor_get_float(v_x_2399_, sizeof(void*)*3 + 8);
v_tag_2404_ = lean_ctor_get(v_x_2399_, 2);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_x_2399_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v_x_2399_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_tag_2404_);
lean_inc(v_result_x3f_2401_);
lean_inc(v_cls_2400_);
lean_dec(v_x_2399_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_cls_2400_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v_result_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2410_, 2, v_tag_2404_);
lean_ctor_set_float(v_reuseFailAlloc_2410_, sizeof(void*)*3, v_startTime_2402_);
lean_ctor_set_float(v_reuseFailAlloc_2410_, sizeof(void*)*3 + 8, v_stopTime_2403_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_ctor_set_uint8(v___x_2409_, sizeof(void*)*3 + 16, v_a_2398_);
return v___x_2409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0___boxed(lean_object* v_a_2412_, lean_object* v_x_2413_){
_start:
{
uint8_t v_a_1094__boxed_2414_; lean_object* v_res_2415_; 
v_a_1094__boxed_2414_ = lean_unbox(v_a_2412_);
v_res_2415_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0(v_a_1094__boxed_2414_, v_x_2413_);
return v_res_2415_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(lean_object* v_as_2416_, size_t v_i_2417_, size_t v_stop_2418_){
_start:
{
uint8_t v___x_2419_; 
v___x_2419_ = lean_usize_dec_eq(v_i_2417_, v_stop_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v_snd_2421_; uint8_t v___x_2422_; 
v___x_2420_ = lean_array_uget_borrowed(v_as_2416_, v_i_2417_);
v_snd_2421_ = lean_ctor_get(v___x_2420_, 1);
v___x_2422_ = lean_unbox(v_snd_2421_);
if (v___x_2422_ == 0)
{
size_t v___x_2423_; size_t v___x_2424_; 
v___x_2423_ = ((size_t)1ULL);
v___x_2424_ = lean_usize_add(v_i_2417_, v___x_2423_);
v_i_2417_ = v___x_2424_;
goto _start;
}
else
{
uint8_t v___x_2426_; 
v___x_2426_ = 1;
return v___x_2426_;
}
}
else
{
uint8_t v___x_2427_; 
v___x_2427_ = 0;
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2___boxed(lean_object* v_as_2428_, lean_object* v_i_2429_, lean_object* v_stop_2430_){
_start:
{
size_t v_i_boxed_2431_; size_t v_stop_boxed_2432_; uint8_t v_res_2433_; lean_object* v_r_2434_; 
v_i_boxed_2431_ = lean_unbox_usize(v_i_2429_);
lean_dec(v_i_2429_);
v_stop_boxed_2432_ = lean_unbox_usize(v_stop_2430_);
lean_dec(v_stop_2430_);
v_res_2433_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(v_as_2428_, v_i_boxed_2431_, v_stop_boxed_2432_);
lean_dec_ref(v_as_2428_);
v_r_2434_ = lean_box(v_res_2433_);
return v_r_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(size_t v_sz_2435_, size_t v_i_2436_, lean_object* v_bs_2437_){
_start:
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_usize_dec_lt(v_i_2436_, v_sz_2435_);
if (v___x_2438_ == 0)
{
return v_bs_2437_;
}
else
{
lean_object* v_v_2439_; lean_object* v_fst_2440_; lean_object* v___x_2441_; lean_object* v_bs_x27_2442_; size_t v___x_2443_; size_t v___x_2444_; lean_object* v___x_2445_; 
v_v_2439_ = lean_array_uget_borrowed(v_bs_2437_, v_i_2436_);
v_fst_2440_ = lean_ctor_get(v_v_2439_, 0);
lean_inc(v_fst_2440_);
v___x_2441_ = lean_unsigned_to_nat(0u);
v_bs_x27_2442_ = lean_array_uset(v_bs_2437_, v_i_2436_, v___x_2441_);
v___x_2443_ = ((size_t)1ULL);
v___x_2444_ = lean_usize_add(v_i_2436_, v___x_2443_);
v___x_2445_ = lean_array_uset(v_bs_x27_2442_, v_i_2436_, v_fst_2440_);
v_i_2436_ = v___x_2444_;
v_bs_2437_ = v___x_2445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1___boxed(lean_object* v_sz_2447_, lean_object* v_i_2448_, lean_object* v_bs_2449_){
_start:
{
size_t v_sz_boxed_2450_; size_t v_i_boxed_2451_; lean_object* v_res_2452_; 
v_sz_boxed_2450_ = lean_unbox_usize(v_sz_2447_);
lean_dec(v_sz_2447_);
v_i_boxed_2451_ = lean_unbox_usize(v_i_2448_);
lean_dec(v_i_2448_);
v_res_2452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(v_sz_boxed_2450_, v_i_boxed_2451_, v_bs_2449_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go(lean_object* v_p_2453_, lean_object* v_t_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2458_; 
lean_inc_ref(v_p_2453_);
lean_inc(v_a_2456_);
lean_inc_ref(v_a_2455_);
lean_inc_ref(v_t_2454_);
v___x_2458_ = lean_apply_4(v_p_2453_, v_t_2454_, v_a_2455_, v_a_2456_, lean_box(0));
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2507_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2507_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2507_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
uint8_t v___x_2463_; 
v___x_2463_ = lean_unbox(v_a_2459_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; size_t v_sz_2465_; size_t v___x_2466_; lean_object* v___x_2467_; 
lean_del_object(v___x_2461_);
v___x_2464_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_2454_);
v_sz_2465_ = lean_array_size(v___x_2464_);
v___x_2466_ = ((size_t)0ULL);
v___x_2467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(v_p_2453_, v_sz_2465_, v___x_2466_, v___x_2464_, v_a_2455_, v_a_2456_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2494_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2494_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2494_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
uint8_t v___y_2473_; lean_object* v___y_2474_; lean_object* v___f_2480_; uint8_t v___y_2482_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
lean_inc(v_a_2459_);
v___f_2480_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2480_, 0, v_a_2459_);
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2488_ = lean_array_get_size(v_a_2468_);
v___x_2489_ = lean_nat_dec_lt(v___x_2487_, v___x_2488_);
if (v___x_2489_ == 0)
{
uint8_t v___x_2490_; 
v___x_2490_ = lean_unbox(v_a_2459_);
lean_dec(v_a_2459_);
v___y_2482_ = v___x_2490_;
goto v___jp_2481_;
}
else
{
if (v___x_2489_ == 0)
{
uint8_t v___x_2491_; 
v___x_2491_ = lean_unbox(v_a_2459_);
lean_dec(v_a_2459_);
v___y_2482_ = v___x_2491_;
goto v___jp_2481_;
}
else
{
size_t v___x_2492_; uint8_t v___x_2493_; 
lean_dec(v_a_2459_);
v___x_2492_ = lean_usize_of_nat(v___x_2488_);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(v_a_2468_, v___x_2466_, v___x_2492_);
v___y_2482_ = v___x_2493_;
goto v___jp_2481_;
}
}
v___jp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2475_ = lean_box(v___y_2473_);
v___x_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___y_2474_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2476_);
v___x_2478_ = v___x_2470_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
v___jp_2481_:
{
size_t v_sz_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_sz_2483_ = lean_array_size(v_a_2468_);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(v_sz_2483_, v___x_2466_, v_a_2468_);
v___x_2485_ = l_Lean_PostprocessTraces_TraceTree_withChildren(v_t_2454_, v___x_2484_);
if (v___y_2482_ == 0)
{
lean_dec_ref(v___f_2480_);
v___y_2473_ = v___y_2482_;
v___y_2474_ = v___x_2485_;
goto v___jp_2472_;
}
else
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_PostprocessTraces_TraceTree_modifyData(v___x_2485_, v___f_2480_);
v___y_2473_ = v___y_2482_;
v___y_2474_ = v___x_2486_;
goto v___jp_2472_;
}
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v_a_2459_);
lean_dec_ref(v_t_2454_);
v_a_2495_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2467_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2467_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
lean_dec_ref(v_p_2453_);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v_t_2454_);
lean_ctor_set(v___x_2503_, 1, v_a_2459_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2503_);
v___x_2505_ = v___x_2461_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec_ref(v_t_2454_);
lean_dec_ref(v_p_2453_);
v_a_2508_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2458_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2458_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(lean_object* v_p_2516_, size_t v_sz_2517_, size_t v_i_2518_, lean_object* v_bs_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
uint8_t v___x_2523_; 
v___x_2523_ = lean_usize_dec_lt(v_i_2518_, v_sz_2517_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
lean_dec_ref(v_p_2516_);
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_bs_2519_);
return v___x_2524_;
}
else
{
lean_object* v_v_2525_; lean_object* v___x_2526_; 
v_v_2525_ = lean_array_uget_borrowed(v_bs_2519_, v_i_2518_);
lean_inc(v_v_2525_);
lean_inc_ref(v_p_2516_);
v___x_2526_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_2516_, v_v_2525_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2528_; lean_object* v_bs_x27_2529_; size_t v___x_2530_; size_t v___x_2531_; lean_object* v___x_2532_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2526_, 1);
v___x_2528_ = lean_unsigned_to_nat(0u);
v_bs_x27_2529_ = lean_array_uset(v_bs_2519_, v_i_2518_, v___x_2528_);
v___x_2530_ = ((size_t)1ULL);
v___x_2531_ = lean_usize_add(v_i_2518_, v___x_2530_);
v___x_2532_ = lean_array_uset(v_bs_x27_2529_, v_i_2518_, v_a_2527_);
v_i_2518_ = v___x_2531_;
v_bs_2519_ = v___x_2532_;
goto _start;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec_ref(v_bs_2519_);
lean_dec_ref(v_p_2516_);
v_a_2534_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2526_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2526_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0___boxed(lean_object* v_p_2542_, lean_object* v_sz_2543_, lean_object* v_i_2544_, lean_object* v_bs_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
size_t v_sz_boxed_2549_; size_t v_i_boxed_2550_; lean_object* v_res_2551_; 
v_sz_boxed_2549_ = lean_unbox_usize(v_sz_2543_);
lean_dec(v_sz_2543_);
v_i_boxed_2550_ = lean_unbox_usize(v_i_2544_);
lean_dec(v_i_2544_);
v_res_2551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(v_p_2542_, v_sz_boxed_2549_, v_i_boxed_2550_, v_bs_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go___boxed(lean_object* v_p_2552_, lean_object* v_t_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_2552_, v_t_2553_, v_a_2554_, v_a_2555_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(lean_object* v_p_2558_, size_t v_sz_2559_, size_t v_i_2560_, lean_object* v_bs_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
uint8_t v___x_2565_; 
v___x_2565_ = lean_usize_dec_lt(v_i_2560_, v_sz_2559_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; 
lean_dec_ref(v_p_2558_);
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v_bs_2561_);
return v___x_2566_;
}
else
{
lean_object* v_v_2567_; lean_object* v___x_2568_; 
v_v_2567_ = lean_array_uget_borrowed(v_bs_2561_, v_i_2560_);
lean_inc(v_v_2567_);
lean_inc_ref(v_p_2558_);
v___x_2568_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_2558_, v_v_2567_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v_fst_2570_; lean_object* v___x_2571_; lean_object* v_bs_x27_2572_; size_t v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v_fst_2570_ = lean_ctor_get(v_a_2569_, 0);
lean_inc(v_fst_2570_);
lean_dec(v_a_2569_);
v___x_2571_ = lean_unsigned_to_nat(0u);
v_bs_x27_2572_ = lean_array_uset(v_bs_2561_, v_i_2560_, v___x_2571_);
v___x_2573_ = ((size_t)1ULL);
v___x_2574_ = lean_usize_add(v_i_2560_, v___x_2573_);
v___x_2575_ = lean_array_uset(v_bs_x27_2572_, v_i_2560_, v_fst_2570_);
v_i_2560_ = v___x_2574_;
v_bs_2561_ = v___x_2575_;
goto _start;
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec_ref(v_bs_2561_);
lean_dec_ref(v_p_2558_);
v_a_2577_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2568_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2568_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0___boxed(lean_object* v_p_2585_, lean_object* v_sz_2586_, lean_object* v_i_2587_, lean_object* v_bs_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
size_t v_sz_boxed_2592_; size_t v_i_boxed_2593_; lean_object* v_res_2594_; 
v_sz_boxed_2592_ = lean_unbox_usize(v_sz_2586_);
lean_dec(v_sz_2586_);
v_i_boxed_2593_ = lean_unbox_usize(v_i_2587_);
lean_dec(v_i_2587_);
v_res_2594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(v_p_2585_, v_sz_boxed_2592_, v_i_boxed_2593_, v_bs_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_exposeSubtrees(lean_object* v_p_2595_, lean_object* v_roots_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_){
_start:
{
size_t v_sz_2600_; size_t v___x_2601_; lean_object* v___x_2602_; 
v_sz_2600_ = lean_array_size(v_roots_2596_);
v___x_2601_ = ((size_t)0ULL);
v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(v_p_2595_, v_sz_2600_, v___x_2601_, v_roots_2596_, v_a_2597_, v_a_2598_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_exposeSubtrees___boxed(lean_object* v_p_2603_, lean_object* v_roots_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_PostprocessTraces_exposeSubtrees(v_p_2603_, v_roots_2604_, v_a_2605_, v_a_2606_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__2(lean_object* v_as_2609_, size_t v_i_2610_, size_t v_stop_2611_, lean_object* v_b_2612_){
_start:
{
uint8_t v___x_2613_; 
v___x_2613_ = lean_usize_dec_eq(v_i_2610_, v_stop_2611_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; lean_object* v_snd_2615_; lean_object* v___x_2616_; size_t v___x_2617_; size_t v___x_2618_; 
v___x_2614_ = lean_array_uget_borrowed(v_as_2609_, v_i_2610_);
v_snd_2615_ = lean_ctor_get(v___x_2614_, 1);
v___x_2616_ = lean_nat_add(v_b_2612_, v_snd_2615_);
lean_dec(v_b_2612_);
v___x_2617_ = ((size_t)1ULL);
v___x_2618_ = lean_usize_add(v_i_2610_, v___x_2617_);
v_i_2610_ = v___x_2618_;
v_b_2612_ = v___x_2616_;
goto _start;
}
else
{
return v_b_2612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__2___boxed(lean_object* v_as_2620_, lean_object* v_i_2621_, lean_object* v_stop_2622_, lean_object* v_b_2623_){
_start:
{
size_t v_i_boxed_2624_; size_t v_stop_boxed_2625_; lean_object* v_res_2626_; 
v_i_boxed_2624_ = lean_unbox_usize(v_i_2621_);
lean_dec(v_i_2621_);
v_stop_boxed_2625_ = lean_unbox_usize(v_stop_2622_);
lean_dec(v_stop_2622_);
v_res_2626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_as_2620_, v_i_boxed_2624_, v_stop_boxed_2625_, v_b_2623_);
lean_dec_ref(v_as_2620_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__1(size_t v_sz_2627_, size_t v_i_2628_, lean_object* v_bs_2629_){
_start:
{
uint8_t v___x_2630_; 
v___x_2630_ = lean_usize_dec_lt(v_i_2628_, v_sz_2627_);
if (v___x_2630_ == 0)
{
return v_bs_2629_;
}
else
{
lean_object* v_v_2631_; lean_object* v_fst_2632_; lean_object* v___x_2633_; lean_object* v_bs_x27_2634_; size_t v___x_2635_; size_t v___x_2636_; lean_object* v___x_2637_; 
v_v_2631_ = lean_array_uget_borrowed(v_bs_2629_, v_i_2628_);
v_fst_2632_ = lean_ctor_get(v_v_2631_, 0);
lean_inc(v_fst_2632_);
v___x_2633_ = lean_unsigned_to_nat(0u);
v_bs_x27_2634_ = lean_array_uset(v_bs_2629_, v_i_2628_, v___x_2633_);
v___x_2635_ = ((size_t)1ULL);
v___x_2636_ = lean_usize_add(v_i_2628_, v___x_2635_);
v___x_2637_ = lean_array_uset(v_bs_x27_2634_, v_i_2628_, v_fst_2632_);
v_i_2628_ = v___x_2636_;
v_bs_2629_ = v___x_2637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__1___boxed(lean_object* v_sz_2639_, lean_object* v_i_2640_, lean_object* v_bs_2641_){
_start:
{
size_t v_sz_boxed_2642_; size_t v_i_boxed_2643_; lean_object* v_res_2644_; 
v_sz_boxed_2642_ = lean_unbox_usize(v_sz_2639_);
lean_dec(v_sz_2639_);
v_i_boxed_2643_ = lean_unbox_usize(v_i_2640_);
lean_dec(v_i_2640_);
v_res_2644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__1(v_sz_boxed_2642_, v_i_boxed_2643_, v_bs_2641_);
return v_res_2644_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__1(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__0));
v___x_2647_ = l_Lean_stringToMessageData(v___x_2646_);
return v___x_2647_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__3(void){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__2));
v___x_2650_ = l_Lean_stringToMessageData(v___x_2649_);
return v___x_2650_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__4(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__38));
v___x_2652_ = l_Lean_stringToMessageData(v___x_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go(lean_object* v_a_2654_){
_start:
{
if (lean_obj_tag(v_a_2654_) == 0)
{
lean_object* v_data_2655_; lean_object* v_msg_2656_; lean_object* v_children_2657_; lean_object* v_wrap_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2700_; 
v_data_2655_ = lean_ctor_get(v_a_2654_, 0);
v_msg_2656_ = lean_ctor_get(v_a_2654_, 1);
v_children_2657_ = lean_ctor_get(v_a_2654_, 2);
v_wrap_2658_ = lean_ctor_get(v_a_2654_, 3);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_a_2654_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2660_ = v_a_2654_;
v_isShared_2661_ = v_isSharedCheck_2700_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_wrap_2658_);
lean_inc(v_children_2657_);
lean_inc(v_msg_2656_);
lean_inc(v_data_2655_);
lean_dec(v_a_2654_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2700_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
size_t v_sz_2662_; size_t v___x_2663_; lean_object* v_results_2664_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___x_2686_; lean_object* v___y_2688_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v_sz_2662_ = lean_array_size(v_children_2657_);
v___x_2663_ = ((size_t)0ULL);
v_results_2664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__0(v_sz_2662_, v___x_2663_, v_children_2657_);
v___x_2686_ = lean_unsigned_to_nat(1u);
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = lean_array_get_size(v_results_2664_);
v___x_2694_ = lean_nat_dec_lt(v___x_2692_, v___x_2693_);
if (v___x_2694_ == 0)
{
v___y_2688_ = v___x_2686_;
goto v___jp_2687_;
}
else
{
uint8_t v___x_2695_; 
v___x_2695_ = lean_nat_dec_le(v___x_2693_, v___x_2693_);
if (v___x_2695_ == 0)
{
if (v___x_2694_ == 0)
{
v___y_2688_ = v___x_2686_;
goto v___jp_2687_;
}
else
{
size_t v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_usize_of_nat(v___x_2693_);
v___x_2697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_results_2664_, v___x_2663_, v___x_2696_, v___x_2686_);
v___y_2688_ = v___x_2697_;
goto v___jp_2687_;
}
}
else
{
size_t v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_usize_of_nat(v___x_2693_);
v___x_2699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_results_2664_, v___x_2663_, v___x_2698_, v___x_2686_);
v___y_2688_ = v___x_2699_;
goto v___jp_2687_;
}
}
v___jp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; size_t v_sz_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2668_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__1, &l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__1_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__1);
v___x_2669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_msg_2656_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
lean_inc(v___y_2666_);
v___x_2670_ = l_Nat_reprFast(v___y_2666_);
v___x_2671_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
v___x_2672_ = l_Lean_MessageData_ofFormat(v___x_2671_);
v___x_2673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2669_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__3, &l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__3_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__3);
v___x_2675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2673_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
lean_inc_ref(v___y_2667_);
v___x_2676_ = l_Lean_stringToMessageData(v___y_2667_);
v___x_2677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2675_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
v___x_2678_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__4, &l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__4_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__4);
v___x_2679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v_sz_2680_ = lean_array_size(v_results_2664_);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__1(v_sz_2680_, v___x_2663_, v_results_2664_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 2, v___x_2681_);
lean_ctor_set(v___x_2660_, 1, v___x_2679_);
v___x_2683_ = v___x_2660_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_data_2655_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v___x_2679_);
lean_ctor_set(v_reuseFailAlloc_2685_, 2, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2685_, 3, v_wrap_2658_);
v___x_2683_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; 
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
lean_ctor_set(v___x_2684_, 1, v___y_2666_);
return v___x_2684_;
}
}
v___jp_2687_:
{
uint8_t v___x_2689_; 
v___x_2689_ = lean_nat_dec_eq(v___y_2688_, v___x_2686_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; 
v___x_2690_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__5));
v___y_2666_ = v___y_2688_;
v___y_2667_ = v___x_2690_;
goto v___jp_2665_;
}
else
{
lean_object* v___x_2691_; 
v___x_2691_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__22));
v___y_2666_ = v___y_2688_;
v___y_2667_ = v___x_2691_;
goto v___jp_2665_;
}
}
}
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_unsigned_to_nat(1u);
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v_a_2654_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
return v___x_2702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__0(size_t v_sz_2703_, size_t v_i_2704_, lean_object* v_bs_2705_){
_start:
{
uint8_t v___x_2706_; 
v___x_2706_ = lean_usize_dec_lt(v_i_2704_, v_sz_2703_);
if (v___x_2706_ == 0)
{
return v_bs_2705_;
}
else
{
lean_object* v_v_2707_; lean_object* v___x_2708_; lean_object* v_bs_x27_2709_; lean_object* v___x_2710_; size_t v___x_2711_; size_t v___x_2712_; lean_object* v___x_2713_; 
v_v_2707_ = lean_array_uget(v_bs_2705_, v_i_2704_);
v___x_2708_ = lean_unsigned_to_nat(0u);
v_bs_x27_2709_ = lean_array_uset(v_bs_2705_, v_i_2704_, v___x_2708_);
v___x_2710_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go(v_v_2707_);
v___x_2711_ = ((size_t)1ULL);
v___x_2712_ = lean_usize_add(v_i_2704_, v___x_2711_);
v___x_2713_ = lean_array_uset(v_bs_x27_2709_, v_i_2704_, v___x_2710_);
v_i_2704_ = v___x_2712_;
v_bs_2705_ = v___x_2713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__0___boxed(lean_object* v_sz_2715_, lean_object* v_i_2716_, lean_object* v_bs_2717_){
_start:
{
size_t v_sz_boxed_2718_; size_t v_i_boxed_2719_; lean_object* v_res_2720_; 
v_sz_boxed_2718_ = lean_unbox_usize(v_sz_2715_);
lean_dec(v_sz_2715_);
v_i_boxed_2719_ = lean_unbox_usize(v_i_2716_);
lean_dec(v_i_2716_);
v_res_2720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go_spec__0(v_sz_boxed_2718_, v_i_boxed_2719_, v_bs_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(size_t v_sz_2721_, size_t v_i_2722_, lean_object* v_bs_2723_){
_start:
{
uint8_t v___x_2724_; 
v___x_2724_ = lean_usize_dec_lt(v_i_2722_, v_sz_2721_);
if (v___x_2724_ == 0)
{
return v_bs_2723_;
}
else
{
lean_object* v_v_2725_; lean_object* v___x_2726_; lean_object* v_fst_2727_; lean_object* v___x_2728_; lean_object* v_bs_x27_2729_; size_t v___x_2730_; size_t v___x_2731_; lean_object* v___x_2732_; 
v_v_2725_ = lean_array_uget_borrowed(v_bs_2723_, v_i_2722_);
lean_inc(v_v_2725_);
v___x_2726_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go(v_v_2725_);
v_fst_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_fst_2727_);
lean_dec_ref(v___x_2726_);
v___x_2728_ = lean_unsigned_to_nat(0u);
v_bs_x27_2729_ = lean_array_uset(v_bs_2723_, v_i_2722_, v___x_2728_);
v___x_2730_ = ((size_t)1ULL);
v___x_2731_ = lean_usize_add(v_i_2722_, v___x_2730_);
v___x_2732_ = lean_array_uset(v_bs_x27_2729_, v_i_2722_, v_fst_2727_);
v_i_2722_ = v___x_2731_;
v_bs_2723_ = v___x_2732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0___boxed(lean_object* v_sz_2734_, lean_object* v_i_2735_, lean_object* v_bs_2736_){
_start:
{
size_t v_sz_boxed_2737_; size_t v_i_boxed_2738_; lean_object* v_res_2739_; 
v_sz_boxed_2737_ = lean_unbox_usize(v_sz_2734_);
lean_dec(v_sz_2734_);
v_i_boxed_2738_ = lean_unbox_usize(v_i_2735_);
lean_dec(v_i_2735_);
v_res_2739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(v_sz_boxed_2737_, v_i_boxed_2738_, v_bs_2736_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___redArg(lean_object* v_roots_2740_){
_start:
{
size_t v_sz_2742_; size_t v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_sz_2742_ = lean_array_size(v_roots_2740_);
v___x_2743_ = ((size_t)0ULL);
v___x_2744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(v_sz_2742_, v___x_2743_, v_roots_2740_);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___redArg___boxed(lean_object* v_roots_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_PostprocessTraces_countNodes___redArg(v_roots_2746_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes(lean_object* v_roots_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Lean_PostprocessTraces_countNodes___redArg(v_roots_2749_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___boxed(lean_object* v_roots_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_PostprocessTraces_countNodes(v_roots_2754_, v_a_2755_, v_a_2756_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
return v_res_2758_;
}
}
static double _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__0(void){
_start:
{
lean_object* v___x_2759_; double v___x_2760_; 
v___x_2759_ = lean_unsigned_to_nat(10u);
v___x_2760_ = lean_float_of_nat(v___x_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs(double v_ms_2763_){
_start:
{
lean_object* v___x_2764_; double v___x_2765_; double v___x_2766_; double v___x_2767_; uint64_t v___x_2768_; lean_object* v_tenths_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2764_ = lean_unsigned_to_nat(10u);
v___x_2765_ = lean_float_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__0, &l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__0_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__0);
v___x_2766_ = lean_float_mul(v_ms_2763_, v___x_2765_);
v___x_2767_ = round(v___x_2766_);
v___x_2768_ = lean_float_to_uint64(v___x_2767_);
v_tenths_2769_ = lean_uint64_to_nat(v___x_2768_);
v___x_2770_ = lean_nat_div(v_tenths_2769_, v___x_2764_);
v___x_2771_ = l_Nat_reprFast(v___x_2770_);
v___x_2772_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__1));
v___x_2773_ = lean_string_append(v___x_2771_, v___x_2772_);
v___x_2774_ = lean_nat_mod(v_tenths_2769_, v___x_2764_);
lean_dec(v_tenths_2769_);
v___x_2775_ = l_Nat_reprFast(v___x_2774_);
v___x_2776_ = lean_string_append(v___x_2773_, v___x_2775_);
lean_dec_ref(v___x_2775_);
v___x_2777_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___closed__2));
v___x_2778_ = lean_string_append(v___x_2776_, v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs___boxed(lean_object* v_ms_2779_){
_start:
{
double v_ms_boxed_2780_; lean_object* v_res_2781_; 
v_ms_boxed_2780_ = lean_unbox_float(v_ms_2779_);
lean_dec_ref(v_ms_2779_);
v_res_2781_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs(v_ms_boxed_2780_);
return v_res_2781_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go___closed__1(void){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go___closed__0));
v___x_2784_ = l_Lean_stringToMessageData(v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go(lean_object* v_a_2785_){
_start:
{
if (lean_obj_tag(v_a_2785_) == 0)
{
lean_object* v_data_2786_; lean_object* v_msg_2787_; lean_object* v_children_2788_; lean_object* v_wrap_2789_; lean_object* v___y_2791_; double v_startTime_2796_; double v___x_2797_; uint8_t v___x_2798_; 
v_data_2786_ = lean_ctor_get(v_a_2785_, 0);
lean_inc_ref(v_data_2786_);
v_msg_2787_ = lean_ctor_get(v_a_2785_, 1);
v_children_2788_ = lean_ctor_get(v_a_2785_, 2);
lean_inc_ref(v_children_2788_);
v_wrap_2789_ = lean_ctor_get(v_a_2785_, 3);
lean_inc_ref(v_wrap_2789_);
v_startTime_2796_ = lean_ctor_get_float(v_data_2786_, sizeof(void*)*3);
v___x_2797_ = lean_float_once(&l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0, &l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0_once, _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0);
v___x_2798_ = lean_float_beq(v_startTime_2796_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2800_; double v___x_2801_; double v___x_2802_; double v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2799_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go___closed__1, &l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go___closed__1_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go___closed__1);
lean_inc_ref(v_msg_2787_);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v_msg_2787_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_a_2785_);
lean_dec_ref_known(v_a_2785_, 4);
v___x_2802_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_2803_ = lean_float_mul(v___x_2801_, v___x_2802_);
v___x_2804_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_formatMs(v___x_2803_);
v___x_2805_ = l_Lean_stringToMessageData(v___x_2804_);
v___x_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2800_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__4, &l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__4_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_countNodes_go___closed__4);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___y_2791_ = v___x_2808_;
goto v___jp_2790_;
}
else
{
lean_inc_ref(v_msg_2787_);
lean_dec_ref_known(v_a_2785_, 4);
v___y_2791_ = v_msg_2787_;
goto v___jp_2790_;
}
v___jp_2790_:
{
size_t v_sz_2792_; size_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_sz_2792_ = lean_array_size(v_children_2788_);
v___x_2793_ = ((size_t)0ULL);
v___x_2794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_2792_, v___x_2793_, v_children_2788_);
v___x_2795_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2795_, 0, v_data_2786_);
lean_ctor_set(v___x_2795_, 1, v___y_2791_);
lean_ctor_set(v___x_2795_, 2, v___x_2794_);
lean_ctor_set(v___x_2795_, 3, v_wrap_2789_);
return v___x_2795_;
}
}
else
{
return v_a_2785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go_spec__0(size_t v_sz_2809_, size_t v_i_2810_, lean_object* v_bs_2811_){
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
lean_object* v_v_2813_; lean_object* v___x_2814_; lean_object* v_bs_x27_2815_; lean_object* v___x_2816_; size_t v___x_2817_; size_t v___x_2818_; lean_object* v___x_2819_; 
v_v_2813_ = lean_array_uget(v_bs_2811_, v_i_2810_);
v___x_2814_ = lean_unsigned_to_nat(0u);
v_bs_x27_2815_ = lean_array_uset(v_bs_2811_, v_i_2810_, v___x_2814_);
v___x_2816_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go(v_v_2813_);
v___x_2817_ = ((size_t)1ULL);
v___x_2818_ = lean_usize_add(v_i_2810_, v___x_2817_);
v___x_2819_ = lean_array_uset(v_bs_x27_2815_, v_i_2810_, v___x_2816_);
v_i_2810_ = v___x_2818_;
v_bs_2811_ = v___x_2819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go_spec__0___boxed(lean_object* v_sz_2821_, lean_object* v_i_2822_, lean_object* v_bs_2823_){
_start:
{
size_t v_sz_boxed_2824_; size_t v_i_boxed_2825_; lean_object* v_res_2826_; 
v_sz_boxed_2824_ = lean_unbox_usize(v_sz_2821_);
lean_dec(v_sz_2821_);
v_i_boxed_2825_ = lean_unbox_usize(v_i_2822_);
lean_dec(v_i_2822_);
v_res_2826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_boxed_2824_, v_i_boxed_2825_, v_bs_2823_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___redArg(lean_object* v_roots_2827_){
_start:
{
size_t v_sz_2829_; size_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_sz_2829_ = lean_array_size(v_roots_2827_);
v___x_2830_ = ((size_t)0ULL);
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_2829_, v___x_2830_, v_roots_2827_);
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___redArg___boxed(lean_object* v_roots_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_PostprocessTraces_selfTime___redArg(v_roots_2833_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime(lean_object* v_roots_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_PostprocessTraces_selfTime___redArg(v_roots_2836_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___boxed(lean_object* v_roots_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_PostprocessTraces_selfTime(v_roots_2841_, v_a_2842_, v_a_2843_);
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
return v_res_2845_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PostprocessTraces_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PostprocessTraces_instInhabitedTraceTree = _init_l_Lean_PostprocessTraces_instInhabitedTraceTree();
lean_mark_persistent(l_Lean_PostprocessTraces_instInhabitedTraceTree);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eval(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PostprocessTraces_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PostprocessTraces_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PostprocessTraces_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PostprocessTraces_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PostprocessTraces_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
