// Lean compiler output
// Module: Lean.Language.Basic
// Imports: public import Lean.Parser.Types public import Lean.Util.Trace
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
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedTraceState_default;
extern lean_object* l_Lean_instInhabitedMessageLog_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* l_instMonadST(lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_IO_CancelToken_set(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_exit(uint8_t);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
lean_object* l_Lean_Message_toJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MessageData_kind(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics_default;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics;
static lean_once_cell_t l_Lean_Language_Snapshot_Diagnostics_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_Diagnostics_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__0 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__1 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__1_value;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__2 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__2_value;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__3 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__4 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__4_value;
static const lean_array_object l_Lean_Language_Snapshot_desc___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__5 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__5_value;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__6 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__7 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__7_value;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__8 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__9 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__9_value;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__10 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__11 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__12;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__13;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__14 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__14_value;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__15 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__15_value;
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_0),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_1),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_2),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__16 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__16_value;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__17 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__17_value;
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_0),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_1),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_2),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__17_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__18 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__18_value;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__19 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__19_value;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__20;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__21;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__22;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__23;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__24 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__24_value;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__25;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__26;
static const lean_string_object l_Lean_Language_Snapshot_desc___autoParam___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toString"};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__27 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__27_value;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__28;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__29;
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__27_value),LEAN_SCALAR_PTR_LITERAL(47, 79, 177, 134, 210, 33, 7, 227)}};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__30 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__30_value;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__31;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__32;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__33;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__34;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__35;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__36;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__37;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__38;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__39;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__40;
static lean_once_cell_t l_Lean_Language_Snapshot_desc___autoParam___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__41;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_desc___autoParam;
static const lean_string_object l_Lean_Language_instInhabitedSnapshot_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Language_instInhabitedSnapshot_default___closed__0 = (const lean_object*)&l_Lean_Language_instInhabitedSnapshot_default___closed__0_value;
static lean_once_cell_t l_Lean_Language_instInhabitedSnapshot_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedSnapshot_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshot_default;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_instInhabitedReportingRange;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(lean_object*);
static lean_once_cell_t l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Language_instInhabitedSnapshotTree_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_instInhabitedSnapshotTree_default___closed__0 = (const lean_object*)&l_Lean_Language_instInhabitedSnapshotTree_default___closed__0_value;
static lean_once_cell_t l_Lean_Language_instInhabitedSnapshotTree_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedSnapshotTree_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTree_default;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTree;
static const lean_string_object l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Language"};
static const lean_object* l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value;
static const lean_string_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "SnapshotTree"};
static const lean_object* l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value;
static const lean_ctor_object l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value_aux_1),((lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value),LEAN_SCALAR_PTR_LITERAL(233, 91, 117, 52, 192, 104, 64, 53)}};
static const lean_object* l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instTypeNameSnapshotTree = (const lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0 = (const lean_object*)&l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree = (const lean_object*)&l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotLeaf_default;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotLeaf;
static const lean_string_object l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "SnapshotLeaf"};
static const lean_object* l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23_ = (const lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23__value;
static const lean_ctor_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23__value_aux_1),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(145, 226, 163, 148, 17, 100, 140, 218)}};
static const lean_object* l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23_ = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23_ = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instTypeNameSnapshotLeaf = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23__value;
static const lean_array_object l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object*);
static const lean_closure_object l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0 = (const lean_object*)&l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf = (const lean_object*)&l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0 = (const lean_object*)&l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot = (const lean_object*)&l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Language_instInhabitedDynamicSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "instInhabitedDynamicSnapshot"};
static const lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__0 = (const lean_object*)&l_Lean_Language_instInhabitedDynamicSnapshot___closed__0_value;
static const lean_ctor_object l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_1),((lean_object*)&l_Lean_Language_instInhabitedDynamicSnapshot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 233, 253, 247, 44, 199, 244, 14)}};
static const lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__1 = (const lean_object*)&l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value;
static lean_once_cell_t l_Lean_Language_instInhabitedDynamicSnapshot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__2;
static lean_once_cell_t l_Lean_Language_instInhabitedDynamicSnapshot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__3;
static lean_once_cell_t l_Lean_Language_instInhabitedDynamicSnapshot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__4;
static lean_once_cell_t l_Lean_Language_instInhabitedDynamicSnapshot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__5;
static lean_once_cell_t l_Lean_Language_instInhabitedDynamicSnapshot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__6;
static lean_once_cell_t l_Lean_Language_instInhabitedDynamicSnapshot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__7;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedDynamicSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "printMessageEndPos"};
static const lean_object* l_Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(132, 21, 81, 184, 167, 123, 94, 166)}};
static const lean_object* l_Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "print end position of each message in addition to start position"};
static const lean_object* l_Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(36, 253, 199, 254, 66, 50, 168, 11)}};
static const lean_object* l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_printMessageEndPos;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "maxErrors"};
static const lean_object* l_Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(229, 225, 16, 209, 3, 189, 8, 41)}};
static const lean_object* l_Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "maximum number of errors to report (0 for no limit)"};
static const lean_object* l_Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)&l_Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 143, 131, 92, 100, 78, 143, 101)}};
static const lean_object* l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_maxErrors;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "maximum number of errors ("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "; from option `maxErrors`) reached, exiting"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Language_SnapshotTree_getAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_SnapshotTree_getAll___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTree_getAll___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
static lean_once_cell_t l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_instMonadLiftProcessingMProcessingTIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___closed__0 = (const lean_object*)&l_Lean_Language_instMonadLiftProcessingMProcessingTIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO = (const lean_object*)&l_Lean_Language_instMonadLiftProcessingMProcessingTIO___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Language_diagnosticsOfHeaderError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<input>"};
static const lean_object* l_Lean_Language_diagnosticsOfHeaderError___closed__0 = (const lean_object*)&l_Lean_Language_diagnosticsOfHeaderError___closed__0_value;
static const lean_ctor_object l_Lean_Language_diagnosticsOfHeaderError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Language_diagnosticsOfHeaderError___closed__1 = (const lean_object*)&l_Lean_Language_diagnosticsOfHeaderError___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Language_withHeaderExceptions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "withHeaderExceptions"};
static const lean_object* l_Lean_Language_withHeaderExceptions___redArg___closed__0 = (const lean_object*)&l_Lean_Language_withHeaderExceptions___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_39__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_withHeaderExceptions___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Language_withHeaderExceptions___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 40, 33, 69, 134, 215, 3, 178)}};
static const lean_object* l_Lean_Language_withHeaderExceptions___redArg___closed__1 = (const lean_object*)&l_Lean_Language_withHeaderExceptions___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Language_withHeaderExceptions___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_withHeaderExceptions___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_instInhabitedMessageLog_default;
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0, &l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0_once, _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Lean_Language_Snapshot_instInhabitedDiagnostics_default;
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_Diagnostics_empty___closed__0(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_box(0);
v___x_7_ = l_Lean_MessageLog_empty;
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_Diagnostics_empty(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lean_Language_Snapshot_Diagnostics_empty___closed__0, &l_Lean_Language_Snapshot_Diagnostics_empty___closed__0_once, _init_l_Lean_Language_Snapshot_Diagnostics_empty___closed__0);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__12(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__10));
v___x_37_ = l_Lean_mkAtom(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__13(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__12, &l_Lean_Language_Snapshot_desc___autoParam___closed__12_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__12);
v___x_39_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__5));
v___x_40_ = lean_array_push(v___x_39_, v___x_38_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__20(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__19));
v___x_56_ = l_Lean_mkAtom(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__21(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__20, &l_Lean_Language_Snapshot_desc___autoParam___closed__20_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__20);
v___x_58_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__5));
v___x_59_ = lean_array_push(v___x_58_, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__22(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__21, &l_Lean_Language_Snapshot_desc___autoParam___closed__21_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__21);
v___x_61_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__18));
v___x_62_ = lean_box(2);
v___x_63_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
lean_ctor_set(v___x_63_, 2, v___x_60_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__23(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__22, &l_Lean_Language_Snapshot_desc___autoParam___closed__22_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__22);
v___x_65_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__5));
v___x_66_ = lean_array_push(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__25(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__24));
v___x_69_ = l_Lean_mkAtom(v___x_68_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__26(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__25, &l_Lean_Language_Snapshot_desc___autoParam___closed__25_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__25);
v___x_71_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__23, &l_Lean_Language_Snapshot_desc___autoParam___closed__23_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__23);
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__28(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__27));
v___x_75_ = lean_string_utf8_byte_size(v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__29(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__28, &l_Lean_Language_Snapshot_desc___autoParam___closed__28_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__28);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__27));
v___x_79_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_76_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__31(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_82_ = lean_box(0);
v___x_83_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__30));
v___x_84_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__29, &l_Lean_Language_Snapshot_desc___autoParam___closed__29_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__29);
v___x_85_ = lean_box(2);
v___x_86_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
lean_ctor_set(v___x_86_, 3, v___x_82_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__32(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__31, &l_Lean_Language_Snapshot_desc___autoParam___closed__31_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__31);
v___x_88_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__26, &l_Lean_Language_Snapshot_desc___autoParam___closed__26_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__26);
v___x_89_ = lean_array_push(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__33(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__32, &l_Lean_Language_Snapshot_desc___autoParam___closed__32_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__32);
v___x_91_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__16));
v___x_92_ = lean_box(2);
v___x_93_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
lean_ctor_set(v___x_93_, 2, v___x_90_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__34(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__33, &l_Lean_Language_Snapshot_desc___autoParam___closed__33_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__33);
v___x_95_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__13, &l_Lean_Language_Snapshot_desc___autoParam___closed__13_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__13);
v___x_96_ = lean_array_push(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__35(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__34, &l_Lean_Language_Snapshot_desc___autoParam___closed__34_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__34);
v___x_98_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__11));
v___x_99_ = lean_box(2);
v___x_100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_97_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__36(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__35, &l_Lean_Language_Snapshot_desc___autoParam___closed__35_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__35);
v___x_102_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__5));
v___x_103_ = lean_array_push(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__37(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__36, &l_Lean_Language_Snapshot_desc___autoParam___closed__36_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__36);
v___x_105_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__9));
v___x_106_ = lean_box(2);
v___x_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_104_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__38(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__37, &l_Lean_Language_Snapshot_desc___autoParam___closed__37_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__37);
v___x_109_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__5));
v___x_110_ = lean_array_push(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__39(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__38, &l_Lean_Language_Snapshot_desc___autoParam___closed__38_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__38);
v___x_112_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__7));
v___x_113_ = lean_box(2);
v___x_114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_111_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__40(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__39, &l_Lean_Language_Snapshot_desc___autoParam___closed__39_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__39);
v___x_116_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__5));
v___x_117_ = lean_array_push(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__41(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__40, &l_Lean_Language_Snapshot_desc___autoParam___closed__40_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__40);
v___x_119_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__4));
v___x_120_ = lean_box(2);
v___x_121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_118_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__41, &l_Lean_Language_Snapshot_desc___autoParam___closed__41_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__41);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot_default___closed__1(void){
_start:
{
uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_124_ = 0;
v___x_125_ = l_Lean_instInhabitedTraceState_default;
v___x_126_ = lean_box(0);
v___x_127_ = l_Lean_Language_Snapshot_instInhabitedDiagnostics_default;
v___x_128_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot_default___closed__0));
v___x_129_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_126_);
lean_ctor_set(v___x_129_, 3, v___x_125_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*4, v___x_124_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot_default(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot_default___closed__1, &l_Lean_Language_instInhabitedSnapshot_default___closed__1_once, _init_l_Lean_Language_instInhabitedSnapshot_default___closed__1);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot(void){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Language_instInhabitedSnapshot_default;
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(lean_object* v_x_132_){
_start:
{
switch(lean_obj_tag(v_x_132_))
{
case 0:
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(0u);
return v___x_133_;
}
case 1:
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(1u);
return v___x_134_;
}
default: 
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(2u);
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___boxed(lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(v_x_136_);
lean_dec(v_x_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(lean_object* v_t_138_, lean_object* v_k_139_){
_start:
{
if (lean_obj_tag(v_t_138_) == 1)
{
lean_object* v_range_140_; lean_object* v___x_141_; 
v_range_140_ = lean_ctor_get(v_t_138_, 0);
lean_inc_ref(v_range_140_);
lean_dec_ref(v_t_138_);
v___x_141_ = lean_apply_1(v_k_139_, v_range_140_);
return v___x_141_;
}
else
{
lean_dec(v_t_138_);
return v_k_139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(lean_object* v_motive_142_, lean_object* v_ctorIdx_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_k_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_144_, v_k_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___boxed(lean_object* v_motive_148_, lean_object* v_ctorIdx_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_k_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(v_motive_148_, v_ctorIdx_149_, v_t_150_, v_h_151_, v_k_152_);
lean_dec(v_ctorIdx_149_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim___redArg(lean_object* v_t_154_, lean_object* v_inherit_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_154_, v_inherit_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim(lean_object* v_motive_157_, lean_object* v_t_158_, lean_object* v_h_159_, lean_object* v_inherit_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_158_, v_inherit_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim___redArg(lean_object* v_t_162_, lean_object* v_some_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_162_, v_some_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim(lean_object* v_motive_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_some_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_166_, v_some_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim___redArg(lean_object* v_t_170_, lean_object* v_skip_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_170_, v_skip_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim(lean_object* v_motive_173_, lean_object* v_t_174_, lean_object* v_h_175_, lean_object* v_skip_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_174_, v_skip_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default(void){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_box(0);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange(void){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lean_box(0);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(lean_object* v_x_180_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
lean_object* v___x_181_; 
v___x_181_ = lean_box(0);
return v___x_181_;
}
else
{
lean_object* v_val_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
v_val_182_ = lean_ctor_get(v_x_180_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v_x_180_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v_x_180_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_val_182_);
lean_dec(v_x_180_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_val_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_box(0);
v___x_191_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object* v_stx_x3f_192_){
_start:
{
if (lean_obj_tag(v_stx_x3f_192_) == 0)
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0, &l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0_once, _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0);
return v___x_193_;
}
else
{
lean_object* v_val_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_val_194_ = lean_ctor_get(v_stx_x3f_192_, 0);
v___x_195_ = 1;
v___x_196_ = l_Lean_Syntax_getRange_x3f(v_val_194_, v___x_195_);
v___x_197_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___x_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange___boxed(lean_object* v_stx_x3f_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v_stx_x3f_198_);
lean_dec(v_stx_x3f_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object* v_inst_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_201_ = lean_box(0);
v___x_202_ = lean_box(0);
v___x_203_ = lean_task_pure(v_inst_200_);
v___x_204_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_204_, 0, v___x_201_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
lean_ctor_set(v___x_204_, 2, v___x_201_);
lean_ctor_set(v___x_204_, 3, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default(lean_object* v_a_205_, lean_object* v_inst_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask___redArg(lean_object* v_inst_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask(lean_object* v_a_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object* v_stx_x3f_213_, lean_object* v_cancelTk_x3f_214_, lean_object* v_reportingRange_215_, lean_object* v_act_216_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_io_as_task(v_act_216_, v___x_218_);
v___x_220_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_220_, 0, v_stx_x3f_213_);
lean_ctor_set(v___x_220_, 1, v_reportingRange_215_);
lean_ctor_set(v___x_220_, 2, v_cancelTk_x3f_214_);
lean_ctor_set(v___x_220_, 3, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg___boxed(lean_object* v_stx_x3f_221_, lean_object* v_cancelTk_x3f_222_, lean_object* v_reportingRange_223_, lean_object* v_act_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v_stx_x3f_221_, v_cancelTk_x3f_222_, v_reportingRange_223_, v_act_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object* v_00_u03b1_227_, lean_object* v_stx_x3f_228_, lean_object* v_cancelTk_x3f_229_, lean_object* v_reportingRange_230_, lean_object* v_act_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v_stx_x3f_228_, v_cancelTk_x3f_229_, v_reportingRange_230_, v_act_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___boxed(lean_object* v_00_u03b1_234_, lean_object* v_stx_x3f_235_, lean_object* v_cancelTk_x3f_236_, lean_object* v_reportingRange_237_, lean_object* v_act_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Language_SnapshotTask_ofIO(v_00_u03b1_234_, v_stx_x3f_235_, v_cancelTk_x3f_236_, v_reportingRange_237_, v_act_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object* v_stx_x3f_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_243_ = lean_box(2);
v___x_244_ = lean_box(0);
v___x_245_ = lean_task_pure(v_a_242_);
v___x_246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_246_, 0, v_stx_x3f_241_);
lean_ctor_set(v___x_246_, 1, v___x_243_);
lean_ctor_set(v___x_246_, 2, v___x_244_);
lean_ctor_set(v___x_246_, 3, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished(lean_object* v_00_u03b1_247_, lean_object* v_stx_x3f_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Language_SnapshotTask_finished___redArg(v_stx_x3f_248_, v_a_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object* v_t_251_, lean_object* v_f_252_, lean_object* v_stx_x3f_253_, lean_object* v_reportingRange_254_, uint8_t v_sync_255_){
_start:
{
lean_object* v_cancelTk_x3f_256_; lean_object* v_task_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_266_; 
v_cancelTk_x3f_256_ = lean_ctor_get(v_t_251_, 2);
v_task_257_ = lean_ctor_get(v_t_251_, 3);
v_isSharedCheck_266_ = !lean_is_exclusive(v_t_251_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; lean_object* v_unused_268_; 
v_unused_267_ = lean_ctor_get(v_t_251_, 1);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v_t_251_, 0);
lean_dec(v_unused_268_);
v___x_259_ = v_t_251_;
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_task_257_);
lean_inc(v_cancelTk_x3f_256_);
lean_dec(v_t_251_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_task_map(v_f_252_, v_task_257_, v___x_261_, v_sync_255_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 3, v___x_262_);
lean_ctor_set(v___x_259_, 1, v_reportingRange_254_);
lean_ctor_set(v___x_259_, 0, v_stx_x3f_253_);
v___x_264_ = v___x_259_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_stx_x3f_253_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_reportingRange_254_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_cancelTk_x3f_256_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg___boxed(lean_object* v_t_269_, lean_object* v_f_270_, lean_object* v_stx_x3f_271_, lean_object* v_reportingRange_272_, lean_object* v_sync_273_){
_start:
{
uint8_t v_sync_boxed_274_; lean_object* v_res_275_; 
v_sync_boxed_274_ = lean_unbox(v_sync_273_);
v_res_275_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_269_, v_f_270_, v_stx_x3f_271_, v_reportingRange_272_, v_sync_boxed_274_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map(lean_object* v_00_u03b1_276_, lean_object* v_00_u03b2_277_, lean_object* v_t_278_, lean_object* v_f_279_, lean_object* v_stx_x3f_280_, lean_object* v_reportingRange_281_, uint8_t v_sync_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_278_, v_f_279_, v_stx_x3f_280_, v_reportingRange_281_, v_sync_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___boxed(lean_object* v_00_u03b1_284_, lean_object* v_00_u03b2_285_, lean_object* v_t_286_, lean_object* v_f_287_, lean_object* v_stx_x3f_288_, lean_object* v_reportingRange_289_, lean_object* v_sync_290_){
_start:
{
uint8_t v_sync_boxed_291_; lean_object* v_res_292_; 
v_sync_boxed_291_ = lean_unbox(v_sync_290_);
v_res_292_ = l_Lean_Language_SnapshotTask_map(v_00_u03b1_284_, v_00_u03b2_285_, v_t_286_, v_f_287_, v_stx_x3f_288_, v_reportingRange_289_, v_sync_boxed_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(lean_object* v_act_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_296_; lean_object* v_task_297_; 
v___x_296_ = lean_apply_2(v_act_293_, v_a_294_, lean_box(0));
v_task_297_ = lean_ctor_get(v___x_296_, 3);
lean_inc_ref(v_task_297_);
lean_dec_ref(v___x_296_);
return v_task_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed(lean_object* v_act_298_, lean_object* v_a_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(v_act_298_, v_a_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object* v_t_302_, lean_object* v_act_303_, lean_object* v_stx_x3f_304_, lean_object* v_reportingRange_305_, lean_object* v_cancelTk_x3f_306_, uint8_t v_sync_307_){
_start:
{
lean_object* v_task_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_319_; 
v_task_309_ = lean_ctor_get(v_t_302_, 3);
v_isSharedCheck_319_ = !lean_is_exclusive(v_t_302_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; 
v_unused_320_ = lean_ctor_get(v_t_302_, 2);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_t_302_, 1);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_t_302_, 0);
lean_dec(v_unused_322_);
v___x_311_ = v_t_302_;
v_isShared_312_ = v_isSharedCheck_319_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_task_309_);
lean_dec(v_t_302_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_319_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___f_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v___f_313_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_313_, 0, v_act_303_);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_io_bind_task(v_task_309_, v___f_313_, v___x_314_, v_sync_307_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 3, v___x_315_);
lean_ctor_set(v___x_311_, 2, v_cancelTk_x3f_306_);
lean_ctor_set(v___x_311_, 1, v_reportingRange_305_);
lean_ctor_set(v___x_311_, 0, v_stx_x3f_304_);
v___x_317_ = v___x_311_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_stx_x3f_304_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_reportingRange_305_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_cancelTk_x3f_306_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___boxed(lean_object* v_t_323_, lean_object* v_act_324_, lean_object* v_stx_x3f_325_, lean_object* v_reportingRange_326_, lean_object* v_cancelTk_x3f_327_, lean_object* v_sync_328_, lean_object* v_a_329_){
_start:
{
uint8_t v_sync_boxed_330_; lean_object* v_res_331_; 
v_sync_boxed_330_ = lean_unbox(v_sync_328_);
v_res_331_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_t_323_, v_act_324_, v_stx_x3f_325_, v_reportingRange_326_, v_cancelTk_x3f_327_, v_sync_boxed_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object* v_00_u03b1_332_, lean_object* v_00_u03b2_333_, lean_object* v_t_334_, lean_object* v_act_335_, lean_object* v_stx_x3f_336_, lean_object* v_reportingRange_337_, lean_object* v_cancelTk_x3f_338_, uint8_t v_sync_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_t_334_, v_act_335_, v_stx_x3f_336_, v_reportingRange_337_, v_cancelTk_x3f_338_, v_sync_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___boxed(lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_t_344_, lean_object* v_act_345_, lean_object* v_stx_x3f_346_, lean_object* v_reportingRange_347_, lean_object* v_cancelTk_x3f_348_, lean_object* v_sync_349_, lean_object* v_a_350_){
_start:
{
uint8_t v_sync_boxed_351_; lean_object* v_res_352_; 
v_sync_boxed_351_ = lean_unbox(v_sync_349_);
v_res_352_ = l_Lean_Language_SnapshotTask_bindIO(v_00_u03b1_342_, v_00_u03b2_343_, v_t_344_, v_act_345_, v_stx_x3f_346_, v_reportingRange_347_, v_cancelTk_x3f_348_, v_sync_boxed_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object* v_t_353_){
_start:
{
lean_object* v_task_354_; lean_object* v___x_355_; 
v_task_354_ = lean_ctor_get(v_t_353_, 3);
lean_inc_ref(v_task_354_);
lean_dec_ref(v_t_353_);
v___x_355_ = lean_task_get_own(v_task_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object* v_00_u03b1_356_, lean_object* v_t_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Language_SnapshotTask_get___redArg(v_t_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object* v_t_359_){
_start:
{
lean_object* v_task_361_; uint8_t v___x_362_; 
v_task_361_ = lean_ctor_get(v_t_359_, 3);
lean_inc_ref(v_task_361_);
lean_dec_ref(v_t_359_);
v___x_362_ = lean_io_get_task_state(v_task_361_);
if (v___x_362_ == 2)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_task_get_own(v_task_361_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; 
lean_dec_ref(v_task_361_);
v___x_365_ = lean_box(0);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg___boxed(lean_object* v_t_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object* v_00_u03b1_369_, lean_object* v_t_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___boxed(lean_object* v_00_u03b1_373_, lean_object* v_t_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Language_SnapshotTask_get_x3f(v_00_u03b1_373_, v_t_374_);
return v_res_376_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshotTree_default___closed__0));
v___x_380_ = l_Lean_Language_instInhabitedSnapshot_default;
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default(void){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshotTree_default___closed__1, &l_Lean_Language_instInhabitedSnapshotTree_default___closed__1_once, _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(lean_object* v_s_392_){
_start:
{
lean_inc_ref(v_s_392_);
return v_s_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed(lean_object* v_s_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(v_s_393_);
lean_dec_ref(v_s_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object* v_inst_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v___x_399_; 
lean_dec_ref(v_inst_397_);
v___x_399_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_399_;
}
else
{
lean_object* v_val_400_; lean_object* v___x_401_; 
v_val_400_ = lean_ctor_get(v_x_398_, 0);
lean_inc(v_val_400_);
lean_dec_ref(v_x_398_);
v___x_401_ = lean_apply_1(v_inst_397_, v_val_400_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg(lean_object* v_inst_402_){
_start:
{
lean_object* v___f_403_; 
v___f_403_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_403_, 0, v_inst_402_);
return v___f_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object* v_00_u03b1_404_, lean_object* v_inst_405_){
_start:
{
lean_object* v___f_406_; 
v___f_406_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_406_, 0, v_inst_405_);
return v___f_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(lean_object* v_inst_407_, lean_object* v___x_408_, lean_object* v___f_409_, lean_object* v_snap_410_){
_start:
{
lean_object* v___x_412_; lean_object* v_children_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_412_ = lean_apply_1(v_inst_407_, v_snap_410_);
v_children_413_ = lean_ctor_get(v___x_412_, 1);
lean_inc_ref(v_children_413_);
lean_dec_ref(v___x_412_);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_array_get_size(v_children_413_);
v___x_416_ = lean_box(0);
v___x_417_ = lean_nat_dec_lt(v___x_414_, v___x_415_);
if (v___x_417_ == 0)
{
lean_dec_ref(v_children_413_);
lean_dec_ref(v___f_409_);
lean_dec_ref(v___x_408_);
return v___x_416_;
}
else
{
uint8_t v___x_418_; 
v___x_418_ = lean_nat_dec_le(v___x_415_, v___x_415_);
if (v___x_418_ == 0)
{
if (v___x_417_ == 0)
{
lean_dec_ref(v_children_413_);
lean_dec_ref(v___f_409_);
lean_dec_ref(v___x_408_);
return v___x_416_;
}
else
{
size_t v___x_419_; size_t v___x_420_; lean_object* v___x_388__overap_421_; lean_object* v___x_422_; 
v___x_419_ = ((size_t)0ULL);
v___x_420_ = lean_usize_of_nat(v___x_415_);
v___x_388__overap_421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_408_, v___f_409_, v_children_413_, v___x_419_, v___x_420_, v___x_416_);
v___x_422_ = lean_apply_1(v___x_388__overap_421_, lean_box(0));
return v___x_422_;
}
}
else
{
size_t v___x_423_; size_t v___x_424_; lean_object* v___x_391__overap_425_; lean_object* v___x_426_; 
v___x_423_ = ((size_t)0ULL);
v___x_424_ = lean_usize_of_nat(v___x_415_);
v___x_391__overap_425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_408_, v___f_409_, v_children_413_, v___x_423_, v___x_424_, v___x_416_);
v___x_426_ = lean_apply_1(v___x_391__overap_425_, lean_box(0));
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed(lean_object* v_inst_427_, lean_object* v___x_428_, lean_object* v___f_429_, lean_object* v_snap_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(v_inst_427_, v___x_428_, v___f_429_, v_snap_430_);
return v_res_432_;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0(void){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_instMonadST(lean_box(0));
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(lean_object* v___f_434_, lean_object* v_x_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(v___f_434_, v_x_435_, v___y_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object* v_inst_439_, lean_object* v_t_440_){
_start:
{
lean_object* v___x_442_; lean_object* v_cancelTk_x3f_443_; lean_object* v_task_444_; lean_object* v___f_445_; lean_object* v___f_446_; lean_object* v___f_447_; 
v___x_442_ = lean_obj_once(&l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0, &l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0_once, _init_l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0);
v_cancelTk_x3f_443_ = lean_ctor_get(v_t_440_, 2);
lean_inc(v_cancelTk_x3f_443_);
v_task_444_ = lean_ctor_get(v_t_440_, 3);
lean_inc_ref(v_task_444_);
lean_dec_ref(v_t_440_);
v___f_445_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0));
v___f_446_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_446_, 0, v___f_445_);
v___f_447_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_447_, 0, v_inst_439_);
lean_closure_set(v___f_447_, 1, v___x_442_);
lean_closure_set(v___f_447_, 2, v___f_446_);
if (lean_obj_tag(v_cancelTk_x3f_443_) == 1)
{
lean_object* v_val_452_; lean_object* v___x_453_; 
v_val_452_ = lean_ctor_get(v_cancelTk_x3f_443_, 0);
lean_inc(v_val_452_);
lean_dec_ref(v_cancelTk_x3f_443_);
v___x_453_ = l_IO_CancelToken_set(v_val_452_);
lean_dec(v_val_452_);
goto v___jp_448_;
}
else
{
lean_dec(v_cancelTk_x3f_443_);
goto v___jp_448_;
}
v___jp_448_:
{
lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = 1;
v___x_451_ = l_BaseIO_chainTask___redArg(v_task_444_, v___f_447_, v___x_449_, v___x_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object* v___f_454_, lean_object* v_x_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_454_, v___y_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___boxed(lean_object* v_inst_459_, lean_object* v_t_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_459_, v_t_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object* v_00_u03b1_463_, lean_object* v_inst_464_, lean_object* v_t_465_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_464_, v_t_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___boxed(lean_object* v_00_u03b1_468_, lean_object* v_inst_469_, lean_object* v_t_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Language_SnapshotTask_cancelRec(v_00_u03b1_468_, v_inst_469_, v_t_470_);
return v_res_472_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotLeaf_default(void){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_Language_instInhabitedSnapshot_default;
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotLeaf(void){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Language_instInhabitedSnapshot_default;
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object* v_s_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0));
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_s_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object* v_s_489_){
_start:
{
lean_object* v_tree_490_; lean_object* v___x_491_; 
v_tree_490_ = lean_ctor_get(v_s_489_, 1);
v___x_491_ = lean_thunk_get_own(v_tree_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object* v_s_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(v_s_492_);
lean_dec_ref(v_s_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0(lean_object* v_inst_496_, lean_object* v_val_497_, lean_object* v_x_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_apply_1(v_inst_496_, v_val_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_val_502_){
_start:
{
lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
lean_inc(v_val_502_);
v___f_503_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_503_, 0, v_inst_501_);
lean_closure_set(v___f_503_, 1, v_val_502_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_inst_500_);
lean_ctor_set(v___x_504_, 1, v_val_502_);
v___x_505_ = lean_mk_thunk(v___f_503_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object* v_00_u03b1_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_val_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v_inst_508_, v_inst_509_, v_val_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object* v_inst_512_, lean_object* v_snap_513_){
_start:
{
lean_object* v_val_514_; lean_object* v___x_515_; 
v_val_514_ = lean_ctor_get(v_snap_513_, 0);
v___x_515_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_514_, v_inst_512_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object* v_inst_516_, lean_object* v_snap_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_516_, v_snap_517_);
lean_dec_ref(v_snap_517_);
lean_dec(v_inst_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object* v_00_u03b1_519_, lean_object* v_inst_520_, lean_object* v_snap_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_520_, v_snap_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object* v_00_u03b1_523_, lean_object* v_inst_524_, lean_object* v_snap_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f(v_00_u03b1_523_, v_inst_524_, v_snap_525_);
lean_dec_ref(v_snap_525_);
lean_dec(v_inst_524_);
return v_res_526_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2(void){
_start:
{
uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = 1;
v___x_533_ = ((lean_object*)(l_Lean_Language_instInhabitedDynamicSnapshot___closed__1));
v___x_534_ = l_Lean_Name_toString(v___x_533_, v___x_532_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_unsigned_to_nat(32u);
v___x_536_ = lean_mk_empty_array_with_capacity(v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4(void){
_start:
{
size_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_538_ = ((size_t)5ULL);
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_unsigned_to_nat(32u);
v___x_541_ = lean_mk_empty_array_with_capacity(v___x_540_);
v___x_542_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__3, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3);
v___x_543_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___x_541_);
lean_ctor_set(v___x_543_, 2, v___x_539_);
lean_ctor_set(v___x_543_, 3, v___x_539_);
lean_ctor_set_usize(v___x_543_, 4, v___x_538_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__5(void){
_start:
{
lean_object* v___x_544_; uint64_t v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__4, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4);
v___x_545_ = 0ULL;
v___x_546_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set_uint64(v___x_546_, sizeof(void*)*1, v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__6(void){
_start:
{
uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_547_ = 0;
v___x_548_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__5, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__5_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__5);
v___x_549_ = lean_box(0);
v___x_550_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_551_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__2, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__2_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2);
v___x_552_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v___x_550_);
lean_ctor_set(v___x_552_, 2, v___x_549_);
lean_ctor_set(v___x_552_, 3, v___x_548_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*4, v___x_547_);
return v___x_552_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__7(void){
_start:
{
lean_object* v___x_553_; lean_object* v___f_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_553_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__6, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__6_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__6);
v___f_554_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0));
v___x_555_ = ((lean_object*)(l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_23_));
v___x_556_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v___x_555_, v___f_554_, v___x_553_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot(void){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__7, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__7_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__7);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object* v_children_558_, lean_object* v_toApplicative_559_, lean_object* v_inst_560_, lean_object* v___f_561_, lean_object* v_____r_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_array_get_size(v_children_558_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_nat_dec_lt(v___x_563_, v___x_564_);
if (v___x_566_ == 0)
{
lean_object* v_toPure_567_; lean_object* v___x_568_; 
lean_dec(v___f_561_);
lean_dec_ref(v_inst_560_);
lean_dec_ref(v_children_558_);
v_toPure_567_ = lean_ctor_get(v_toApplicative_559_, 1);
lean_inc(v_toPure_567_);
lean_dec_ref(v_toApplicative_559_);
v___x_568_ = lean_apply_2(v_toPure_567_, lean_box(0), v___x_565_);
return v___x_568_;
}
else
{
uint8_t v___x_569_; 
v___x_569_ = lean_nat_dec_le(v___x_564_, v___x_564_);
if (v___x_569_ == 0)
{
if (v___x_566_ == 0)
{
lean_object* v_toPure_570_; lean_object* v___x_571_; 
lean_dec(v___f_561_);
lean_dec_ref(v_inst_560_);
lean_dec_ref(v_children_558_);
v_toPure_570_ = lean_ctor_get(v_toApplicative_559_, 1);
lean_inc(v_toPure_570_);
lean_dec_ref(v_toApplicative_559_);
v___x_571_ = lean_apply_2(v_toPure_570_, lean_box(0), v___x_565_);
return v___x_571_;
}
else
{
size_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v_toApplicative_559_);
v___x_572_ = ((size_t)0ULL);
v___x_573_ = lean_usize_of_nat(v___x_564_);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_560_, v___f_561_, v_children_558_, v___x_572_, v___x_573_, v___x_565_);
return v___x_574_;
}
}
else
{
size_t v___x_575_; size_t v___x_576_; lean_object* v___x_577_; 
lean_dec_ref(v_toApplicative_559_);
v___x_575_ = ((size_t)0ULL);
v___x_576_ = lean_usize_of_nat(v___x_564_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_560_, v___f_561_, v_children_558_, v___x_575_, v___x_576_, v___x_565_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object* v_inst_578_, lean_object* v_s_579_, lean_object* v_f_580_){
_start:
{
lean_object* v_toApplicative_581_; lean_object* v_toBind_582_; lean_object* v_element_583_; lean_object* v_children_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_toApplicative_581_ = lean_ctor_get(v_inst_578_, 0);
lean_inc_ref(v_toApplicative_581_);
v_toBind_582_ = lean_ctor_get(v_inst_578_, 1);
lean_inc(v_toBind_582_);
v_element_583_ = lean_ctor_get(v_s_579_, 0);
lean_inc_ref(v_element_583_);
v_children_584_ = lean_ctor_get(v_s_579_, 1);
lean_inc_ref(v_children_584_);
lean_dec_ref(v_s_579_);
lean_inc(v_f_580_);
lean_inc_ref(v_inst_578_);
v___f_585_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_585_, 0, v_inst_578_);
lean_closure_set(v___f_585_, 1, v_f_580_);
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_586_, 0, v_children_584_);
lean_closure_set(v___f_586_, 1, v_toApplicative_581_);
lean_closure_set(v___f_586_, 2, v_inst_578_);
lean_closure_set(v___f_586_, 3, v___f_585_);
v___x_587_ = lean_apply_1(v_f_580_, v_element_583_);
v___x_588_ = lean_apply_4(v_toBind_582_, lean_box(0), lean_box(0), v___x_587_, v___f_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object* v_inst_589_, lean_object* v_f_590_, lean_object* v_x_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = l_Lean_Language_SnapshotTask_get___redArg(v___y_592_);
v___x_594_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_589_, v___x_593_, v_f_590_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object* v_m_595_, lean_object* v_inst_596_, lean_object* v_s_597_, lean_object* v_f_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_596_, v_s_597_, v_f_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object* v_children_600_, lean_object* v_toApplicative_601_, lean_object* v_inst_602_, lean_object* v___f_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = lean_array_get_size(v_children_600_);
v___x_607_ = lean_nat_dec_lt(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v_toPure_608_; lean_object* v___x_609_; 
lean_dec(v___f_603_);
lean_dec_ref(v_inst_602_);
lean_dec_ref(v_children_600_);
v_toPure_608_ = lean_ctor_get(v_toApplicative_601_, 1);
lean_inc(v_toPure_608_);
lean_dec_ref(v_toApplicative_601_);
v___x_609_ = lean_apply_2(v_toPure_608_, lean_box(0), v_a_604_);
return v___x_609_;
}
else
{
uint8_t v___x_610_; 
v___x_610_ = lean_nat_dec_le(v___x_606_, v___x_606_);
if (v___x_610_ == 0)
{
if (v___x_607_ == 0)
{
lean_object* v_toPure_611_; lean_object* v___x_612_; 
lean_dec(v___f_603_);
lean_dec_ref(v_inst_602_);
lean_dec_ref(v_children_600_);
v_toPure_611_ = lean_ctor_get(v_toApplicative_601_, 1);
lean_inc(v_toPure_611_);
lean_dec_ref(v_toApplicative_601_);
v___x_612_ = lean_apply_2(v_toPure_611_, lean_box(0), v_a_604_);
return v___x_612_;
}
else
{
size_t v___x_613_; size_t v___x_614_; lean_object* v___x_615_; 
lean_dec_ref(v_toApplicative_601_);
v___x_613_ = ((size_t)0ULL);
v___x_614_ = lean_usize_of_nat(v___x_606_);
v___x_615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_602_, v___f_603_, v_children_600_, v___x_613_, v___x_614_, v_a_604_);
return v___x_615_;
}
}
else
{
size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; 
lean_dec_ref(v_toApplicative_601_);
v___x_616_ = ((size_t)0ULL);
v___x_617_ = lean_usize_of_nat(v___x_606_);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_602_, v___f_603_, v_children_600_, v___x_616_, v___x_617_, v_a_604_);
return v___x_618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object* v_inst_619_, lean_object* v_s_620_, lean_object* v_f_621_, lean_object* v_init_622_){
_start:
{
lean_object* v_toApplicative_623_; lean_object* v_toBind_624_; lean_object* v_element_625_; lean_object* v_children_626_; lean_object* v___f_627_; lean_object* v___f_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_toApplicative_623_ = lean_ctor_get(v_inst_619_, 0);
lean_inc_ref(v_toApplicative_623_);
v_toBind_624_ = lean_ctor_get(v_inst_619_, 1);
lean_inc(v_toBind_624_);
v_element_625_ = lean_ctor_get(v_s_620_, 0);
lean_inc_ref(v_element_625_);
v_children_626_ = lean_ctor_get(v_s_620_, 1);
lean_inc_ref(v_children_626_);
lean_dec_ref(v_s_620_);
lean_inc(v_f_621_);
lean_inc_ref(v_inst_619_);
v___f_627_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_627_, 0, v_inst_619_);
lean_closure_set(v___f_627_, 1, v_f_621_);
v___f_628_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_628_, 0, v_children_626_);
lean_closure_set(v___f_628_, 1, v_toApplicative_623_);
lean_closure_set(v___f_628_, 2, v_inst_619_);
lean_closure_set(v___f_628_, 3, v___f_627_);
v___x_629_ = lean_apply_2(v_f_621_, v_init_622_, v_element_625_);
v___x_630_ = lean_apply_4(v_toBind_624_, lean_box(0), lean_box(0), v___x_629_, v___f_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object* v_inst_631_, lean_object* v_f_632_, lean_object* v_a_633_, lean_object* v_snap_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = l_Lean_Language_SnapshotTask_get___redArg(v_snap_634_);
v___x_636_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_631_, v___x_635_, v_f_632_, v_a_633_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object* v_m_637_, lean_object* v_00_u03b1_638_, lean_object* v_inst_639_, lean_object* v_s_640_, lean_object* v_f_641_, lean_object* v_init_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_639_, v_s_640_, v_f_641_, v_init_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(lean_object* v_name_644_, lean_object* v_decl_645_, lean_object* v_ref_646_){
_start:
{
lean_object* v_defValue_648_; lean_object* v_descr_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_676_; 
v_defValue_648_ = lean_ctor_get(v_decl_645_, 0);
v_descr_649_ = lean_ctor_get(v_decl_645_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_decl_645_);
if (v_isSharedCheck_676_ == 0)
{
v___x_651_ = v_decl_645_;
v_isShared_652_ = v_isSharedCheck_676_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_descr_649_);
lean_inc(v_defValue_648_);
lean_dec(v_decl_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_676_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_alloc_ctor(1, 0, 1);
v___x_654_ = lean_unbox(v_defValue_648_);
lean_ctor_set_uint8(v___x_653_, 0, v___x_654_);
lean_inc(v_name_644_);
v___x_655_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_655_, 0, v_name_644_);
lean_ctor_set(v___x_655_, 1, v_ref_646_);
lean_ctor_set(v___x_655_, 2, v___x_653_);
lean_ctor_set(v___x_655_, 3, v_descr_649_);
lean_inc(v_name_644_);
v___x_656_ = lean_register_option(v_name_644_, v___x_655_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_666_; 
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v___x_656_, 0);
lean_dec(v_unused_667_);
v___x_658_ = v___x_656_;
v_isShared_659_ = v_isSharedCheck_666_;
goto v_resetjp_657_;
}
else
{
lean_dec(v___x_656_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_666_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v_defValue_648_);
lean_ctor_set(v___x_651_, 0, v_name_644_);
v___x_661_ = v___x_651_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_name_644_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_defValue_648_);
v___x_661_ = v_reuseFailAlloc_665_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_661_);
v___x_663_ = v___x_658_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_del_object(v___x_651_);
lean_dec(v_defValue_648_);
lean_dec(v_name_644_);
v_a_668_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_656_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_656_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_677_, lean_object* v_decl_678_, lean_object* v_ref_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v_name_677_, v_decl_678_, v_ref_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_695_ = ((lean_object*)(l_Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_696_ = ((lean_object*)(l_Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_697_ = ((lean_object*)(l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_698_ = l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v___x_695_, v___x_696_, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4____boxed(lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(lean_object* v_name_701_, lean_object* v_decl_702_, lean_object* v_ref_703_){
_start:
{
lean_object* v_defValue_705_; lean_object* v_descr_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_732_; 
v_defValue_705_ = lean_ctor_get(v_decl_702_, 0);
v_descr_706_ = lean_ctor_get(v_decl_702_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_decl_702_);
if (v_isSharedCheck_732_ == 0)
{
v___x_708_ = v_decl_702_;
v_isShared_709_ = v_isSharedCheck_732_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_descr_706_);
lean_inc(v_defValue_705_);
lean_dec(v_decl_702_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_732_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_inc(v_defValue_705_);
v___x_710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_710_, 0, v_defValue_705_);
lean_inc(v_name_701_);
v___x_711_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_711_, 0, v_name_701_);
lean_ctor_set(v___x_711_, 1, v_ref_703_);
lean_ctor_set(v___x_711_, 2, v___x_710_);
lean_ctor_set(v___x_711_, 3, v_descr_706_);
lean_inc(v_name_701_);
v___x_712_ = lean_register_option(v_name_701_, v___x_711_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_722_; 
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v___x_712_, 0);
lean_dec(v_unused_723_);
v___x_714_ = v___x_712_;
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
else
{
lean_dec(v___x_712_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v_defValue_705_);
lean_ctor_set(v___x_708_, 0, v_name_701_);
v___x_717_ = v___x_708_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_name_701_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_defValue_705_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_717_);
v___x_719_ = v___x_714_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
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
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_del_object(v___x_708_);
lean_dec(v_defValue_705_);
lean_dec(v_name_701_);
v_a_724_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_712_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_712_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_733_, lean_object* v_decl_734_, lean_object* v_ref_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v_name_733_, v_decl_734_, v_ref_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_750_ = ((lean_object*)(l_Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_751_ = ((lean_object*)(l_Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_752_ = ((lean_object*)(l_Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_753_ = l_Lean_Option_register___at___00Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v___x_750_, v___x_751_, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4____boxed(lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
return v_res_755_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(lean_object* v_opts_756_, lean_object* v_opt_757_){
_start:
{
lean_object* v_name_758_; lean_object* v_defValue_759_; lean_object* v_map_760_; lean_object* v___x_761_; 
v_name_758_ = lean_ctor_get(v_opt_757_, 0);
v_defValue_759_ = lean_ctor_get(v_opt_757_, 1);
v_map_760_ = lean_ctor_get(v_opts_756_, 0);
v___x_761_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_760_, v_name_758_);
if (lean_obj_tag(v___x_761_) == 0)
{
uint8_t v___x_762_; 
v___x_762_ = lean_unbox(v_defValue_759_);
return v___x_762_;
}
else
{
lean_object* v_val_763_; 
v_val_763_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_val_763_);
lean_dec_ref(v___x_761_);
if (lean_obj_tag(v_val_763_) == 1)
{
uint8_t v_v_764_; 
v_v_764_ = lean_ctor_get_uint8(v_val_763_, 0);
lean_dec_ref(v_val_763_);
return v_v_764_;
}
else
{
uint8_t v___x_765_; 
lean_dec(v_val_763_);
v___x_765_ = lean_unbox(v_defValue_759_);
return v___x_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0___boxed(lean_object* v_opts_766_, lean_object* v_opt_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_766_, v_opt_767_);
lean_dec_ref(v_opt_767_);
lean_dec_ref(v_opts_766_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(lean_object* v_opts_770_, lean_object* v_opt_771_){
_start:
{
lean_object* v_name_772_; lean_object* v_defValue_773_; lean_object* v_map_774_; lean_object* v___x_775_; 
v_name_772_ = lean_ctor_get(v_opt_771_, 0);
v_defValue_773_ = lean_ctor_get(v_opt_771_, 1);
v_map_774_ = lean_ctor_get(v_opts_770_, 0);
v___x_775_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_774_, v_name_772_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_inc(v_defValue_773_);
return v_defValue_773_;
}
else
{
lean_object* v_val_776_; 
v_val_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_val_776_);
lean_dec_ref(v___x_775_);
if (lean_obj_tag(v_val_776_) == 3)
{
lean_object* v_v_777_; 
v_v_777_ = lean_ctor_get(v_val_776_, 0);
lean_inc(v_v_777_);
lean_dec_ref(v_val_776_);
return v_v_777_;
}
else
{
lean_dec(v_val_776_);
lean_inc(v_defValue_773_);
return v_defValue_773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1___boxed(lean_object* v_opts_778_, lean_object* v_opt_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_778_, v_opt_779_);
lean_dec_ref(v_opt_779_);
lean_dec_ref(v_opts_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(lean_object* v_s_781_){
_start:
{
lean_object* v___x_783_; lean_object* v_putStr_784_; lean_object* v___x_785_; 
v___x_783_ = lean_get_stdout();
v_putStr_784_ = lean_ctor_get(v___x_783_, 4);
lean_inc_ref(v_putStr_784_);
lean_dec_ref(v___x_783_);
v___x_785_ = lean_apply_2(v_putStr_784_, v_s_781_, lean_box(0));
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2___boxed(lean_object* v_s_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v_s_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object* v_s_789_){
_start:
{
uint32_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = 10;
v___x_792_ = lean_string_push(v_s_789_, v___x_791_);
v___x_793_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3___boxed(lean_object* v_s_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v_s_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(lean_object* v_opts_799_, uint8_t v_json_800_, uint8_t v_includeEndPos_801_, lean_object* v_severityOverrides_802_, lean_object* v_as_803_, size_t v_i_804_, size_t v_stop_805_, lean_object* v_b_806_){
_start:
{
lean_object* v_a_809_; lean_object* v___y_814_; uint8_t v___y_815_; lean_object* v___y_827_; uint8_t v___y_828_; lean_object* v___y_829_; uint8_t v_isSilent_830_; uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_eq(v_i_804_, v_stop_805_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___y_855_; lean_object* v___y_856_; uint8_t v___y_857_; lean_object* v___y_905_; uint8_t v_severity_912_; 
v___x_853_ = lean_array_uget(v_as_803_, v_i_804_);
v_severity_912_ = lean_ctor_get_uint8(v___x_853_, sizeof(void*)*5 + 1);
if (v_severity_912_ == 2)
{
lean_object* v___x_913_; 
v___x_913_ = lean_unsigned_to_nat(1u);
v___y_905_ = v___x_913_;
goto v___jp_904_;
}
else
{
lean_object* v___x_914_; 
v___x_914_ = lean_unsigned_to_nat(0u);
v___y_905_ = v___x_914_;
goto v___jp_904_;
}
v___jp_854_:
{
if (v___y_857_ == 0)
{
lean_object* v_fileName_858_; lean_object* v_pos_859_; lean_object* v_endPos_860_; uint8_t v_keepFullRange_861_; uint8_t v_isSilent_862_; lean_object* v_caption_863_; lean_object* v_data_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec(v___y_855_);
v_fileName_858_ = lean_ctor_get(v___x_853_, 0);
v_pos_859_ = lean_ctor_get(v___x_853_, 1);
v_endPos_860_ = lean_ctor_get(v___x_853_, 2);
v_keepFullRange_861_ = lean_ctor_get_uint8(v___x_853_, sizeof(void*)*5);
v_isSilent_862_ = lean_ctor_get_uint8(v___x_853_, sizeof(void*)*5 + 2);
v_caption_863_ = lean_ctor_get(v___x_853_, 3);
v_data_864_ = lean_ctor_get(v___x_853_, 4);
v___x_865_ = l_Lean_MessageData_kind(v_data_864_);
v___x_866_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_severityOverrides_802_, v___x_865_);
lean_dec(v___x_865_);
if (lean_obj_tag(v___x_866_) == 1)
{
lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_875_; 
lean_inc(v_data_864_);
lean_inc_ref(v_caption_863_);
lean_inc(v_endPos_860_);
lean_inc_ref(v_pos_859_);
lean_inc_ref(v_fileName_858_);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; lean_object* v_unused_877_; lean_object* v_unused_878_; lean_object* v_unused_879_; lean_object* v_unused_880_; 
v_unused_876_ = lean_ctor_get(v___x_853_, 4);
lean_dec(v_unused_876_);
v_unused_877_ = lean_ctor_get(v___x_853_, 3);
lean_dec(v_unused_877_);
v_unused_878_ = lean_ctor_get(v___x_853_, 2);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v___x_853_, 1);
lean_dec(v_unused_879_);
v_unused_880_ = lean_ctor_get(v___x_853_, 0);
lean_dec(v_unused_880_);
v___x_868_ = v___x_853_;
v_isShared_869_ = v_isSharedCheck_875_;
goto v_resetjp_867_;
}
else
{
lean_dec(v___x_853_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_875_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_val_870_; lean_object* v___x_872_; 
v_val_870_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_val_870_);
lean_dec_ref(v___x_866_);
if (v_isShared_869_ == 0)
{
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_fileName_858_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_pos_859_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v_endPos_860_);
lean_ctor_set(v_reuseFailAlloc_874_, 3, v_caption_863_);
lean_ctor_set(v_reuseFailAlloc_874_, 4, v_data_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_874_, sizeof(void*)*5, v_keepFullRange_861_);
v___x_872_ = v_reuseFailAlloc_874_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
uint8_t v___x_873_; 
v___x_873_ = lean_unbox(v_val_870_);
lean_dec(v_val_870_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*5 + 1, v___x_873_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*5 + 2, v_isSilent_862_);
v___y_827_ = v___y_856_;
v___y_828_ = v___y_857_;
v___y_829_ = v___x_872_;
v_isSilent_830_ = v_isSilent_862_;
goto v___jp_826_;
}
}
}
else
{
uint8_t v_isSilent_881_; 
lean_dec(v___x_866_);
v_isSilent_881_ = lean_ctor_get_uint8(v___x_853_, sizeof(void*)*5 + 2);
v___y_827_ = v___y_856_;
v___y_828_ = v___y_857_;
v___y_829_ = v___x_853_;
v_isSilent_830_ = v_isSilent_881_;
goto v___jp_826_;
}
}
else
{
lean_object* v_fileName_882_; lean_object* v_pos_883_; lean_object* v_endPos_884_; uint8_t v_keepFullRange_885_; uint8_t v_isSilent_886_; lean_object* v_caption_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_902_; 
v_fileName_882_ = lean_ctor_get(v___x_853_, 0);
v_pos_883_ = lean_ctor_get(v___x_853_, 1);
v_endPos_884_ = lean_ctor_get(v___x_853_, 2);
v_keepFullRange_885_ = lean_ctor_get_uint8(v___x_853_, sizeof(void*)*5);
v_isSilent_886_ = lean_ctor_get_uint8(v___x_853_, sizeof(void*)*5 + 2);
v_caption_887_ = lean_ctor_get(v___x_853_, 3);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v___x_853_, 4);
lean_dec(v_unused_903_);
v___x_889_ = v___x_853_;
v_isShared_890_ = v_isSharedCheck_902_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_caption_887_);
lean_inc(v_endPos_884_);
lean_inc(v_pos_883_);
lean_inc(v_fileName_882_);
lean_dec(v___x_853_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_902_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_891_ = 2;
v___x_892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0));
v___x_893_ = l_Nat_reprFast(v___y_855_);
v___x_894_ = lean_string_append(v___x_892_, v___x_893_);
lean_dec_ref(v___x_893_);
v___x_895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1));
v___x_896_ = lean_string_append(v___x_894_, v___x_895_);
v___x_897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
v___x_898_ = l_Lean_MessageData_ofFormat(v___x_897_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 4, v___x_898_);
v___x_900_ = v___x_889_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_fileName_882_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_pos_883_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_endPos_884_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v_caption_887_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v___x_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*5, v_keepFullRange_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*5 + 2, v_isSilent_886_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_ctor_set_uint8(v___x_900_, sizeof(void*)*5 + 1, v___x_891_);
v___y_827_ = v___y_856_;
v___y_828_ = v___y_857_;
v___y_829_ = v___x_900_;
v_isSilent_830_ = v_isSilent_886_;
goto v___jp_826_;
}
}
}
}
v___jp_904_:
{
lean_object* v_numErrors_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_numErrors_906_ = lean_nat_add(v_b_806_, v___y_905_);
lean_dec(v_b_806_);
v___x_907_ = l_Lean_Language_maxErrors;
v___x_908_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_799_, v___x_907_);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_nat_dec_eq(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
uint8_t v___x_911_; 
v___x_911_ = lean_nat_dec_lt(v___x_908_, v_numErrors_906_);
if (v___x_911_ == 0)
{
v___y_855_ = v___x_908_;
v___y_856_ = v_numErrors_906_;
v___y_857_ = v___x_852_;
goto v___jp_854_;
}
else
{
v___y_855_ = v___x_908_;
v___y_856_ = v_numErrors_906_;
v___y_857_ = v___x_911_;
goto v___jp_854_;
}
}
else
{
v___y_855_ = v___x_908_;
v___y_856_ = v_numErrors_906_;
v___y_857_ = v___x_852_;
goto v___jp_854_;
}
}
}
else
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v_b_806_);
return v___x_915_;
}
v___jp_808_:
{
size_t v___x_810_; size_t v___x_811_; 
v___x_810_ = ((size_t)1ULL);
v___x_811_ = lean_usize_add(v_i_804_, v___x_810_);
v_i_804_ = v___x_811_;
v_b_806_ = v_a_809_;
goto _start;
}
v___jp_813_:
{
if (v___y_815_ == 0)
{
v_a_809_ = v___y_814_;
goto v___jp_808_;
}
else
{
uint8_t v___x_816_; lean_object* v___x_817_; 
v___x_816_ = 1;
v___x_817_ = lean_io_exit(v___x_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_dec_ref(v___x_817_);
v_a_809_ = v___y_814_;
goto v___jp_808_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v___y_814_);
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
v___jp_826_:
{
if (v_isSilent_830_ == 0)
{
if (v_json_800_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = l_Lean_Message_toString(v___y_829_, v_includeEndPos_801_);
v___x_832_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_dec_ref(v___x_832_);
v___y_814_ = v___y_827_;
v___y_815_ = v___y_828_;
goto v___jp_813_;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v___y_827_);
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_841_ = l_Lean_Message_toJson(v___y_829_);
v___x_842_ = l_Lean_Json_compress(v___x_841_);
v___x_843_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_842_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_dec_ref(v___x_843_);
v___y_814_ = v___y_827_;
v___y_815_ = v___y_828_;
goto v___jp_813_;
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v___y_827_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
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
}
else
{
lean_dec_ref(v___y_829_);
v___y_814_ = v___y_827_;
v___y_815_ = v___y_828_;
goto v___jp_813_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___boxed(lean_object* v_opts_916_, lean_object* v_json_917_, lean_object* v_includeEndPos_918_, lean_object* v_severityOverrides_919_, lean_object* v_as_920_, lean_object* v_i_921_, lean_object* v_stop_922_, lean_object* v_b_923_, lean_object* v___y_924_){
_start:
{
uint8_t v_json_boxed_925_; uint8_t v_includeEndPos_boxed_926_; size_t v_i_boxed_927_; size_t v_stop_boxed_928_; lean_object* v_res_929_; 
v_json_boxed_925_ = lean_unbox(v_json_917_);
v_includeEndPos_boxed_926_ = lean_unbox(v_includeEndPos_918_);
v_i_boxed_927_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_stop_boxed_928_ = lean_unbox_usize(v_stop_922_);
lean_dec(v_stop_922_);
v_res_929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_916_, v_json_boxed_925_, v_includeEndPos_boxed_926_, v_severityOverrides_919_, v_as_920_, v_i_boxed_927_, v_stop_boxed_928_, v_b_923_);
lean_dec_ref(v_as_920_);
lean_dec(v_severityOverrides_919_);
lean_dec_ref(v_opts_916_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(lean_object* v_opts_930_, uint8_t v_json_931_, uint8_t v_includeEndPos_932_, lean_object* v_severityOverrides_933_, lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
if (lean_obj_tag(v_x_934_) == 0)
{
lean_object* v_cs_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_957_; 
v_cs_937_ = lean_ctor_get(v_x_934_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v_x_934_);
if (v_isSharedCheck_957_ == 0)
{
v___x_939_ = v_x_934_;
v_isShared_940_ = v_isSharedCheck_957_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_cs_937_);
lean_dec(v_x_934_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_957_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_array_get_size(v_cs_937_);
v___x_943_ = lean_nat_dec_lt(v___x_941_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_945_; 
lean_dec_ref(v_cs_937_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_x_935_);
v___x_945_ = v___x_939_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_x_935_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
else
{
uint8_t v___x_947_; 
v___x_947_ = lean_nat_dec_le(v___x_942_, v___x_942_);
if (v___x_947_ == 0)
{
if (v___x_943_ == 0)
{
lean_object* v___x_949_; 
lean_dec_ref(v_cs_937_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_x_935_);
v___x_949_ = v___x_939_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_x_935_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
else
{
size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
lean_del_object(v___x_939_);
v___x_951_ = ((size_t)0ULL);
v___x_952_ = lean_usize_of_nat(v___x_942_);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_930_, v_json_931_, v_includeEndPos_932_, v_severityOverrides_933_, v_cs_937_, v___x_951_, v___x_952_, v_x_935_);
lean_dec_ref(v_cs_937_);
return v___x_953_;
}
}
else
{
size_t v___x_954_; size_t v___x_955_; lean_object* v___x_956_; 
lean_del_object(v___x_939_);
v___x_954_ = ((size_t)0ULL);
v___x_955_ = lean_usize_of_nat(v___x_942_);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_930_, v_json_931_, v_includeEndPos_932_, v_severityOverrides_933_, v_cs_937_, v___x_954_, v___x_955_, v_x_935_);
lean_dec_ref(v_cs_937_);
return v___x_956_;
}
}
}
}
else
{
lean_object* v_vs_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_978_; 
v_vs_958_ = lean_ctor_get(v_x_934_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v_x_934_);
if (v_isSharedCheck_978_ == 0)
{
v___x_960_ = v_x_934_;
v_isShared_961_ = v_isSharedCheck_978_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_vs_958_);
lean_dec(v_x_934_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_978_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = lean_array_get_size(v_vs_958_);
v___x_964_ = lean_nat_dec_lt(v___x_962_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_966_; 
lean_dec_ref(v_vs_958_);
if (v_isShared_961_ == 0)
{
lean_ctor_set_tag(v___x_960_, 0);
lean_ctor_set(v___x_960_, 0, v_x_935_);
v___x_966_ = v___x_960_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_x_935_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
else
{
uint8_t v___x_968_; 
v___x_968_ = lean_nat_dec_le(v___x_963_, v___x_963_);
if (v___x_968_ == 0)
{
if (v___x_964_ == 0)
{
lean_object* v___x_970_; 
lean_dec_ref(v_vs_958_);
if (v_isShared_961_ == 0)
{
lean_ctor_set_tag(v___x_960_, 0);
lean_ctor_set(v___x_960_, 0, v_x_935_);
v___x_970_ = v___x_960_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_x_935_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
else
{
size_t v___x_972_; size_t v___x_973_; lean_object* v___x_974_; 
lean_del_object(v___x_960_);
v___x_972_ = ((size_t)0ULL);
v___x_973_ = lean_usize_of_nat(v___x_963_);
v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_930_, v_json_931_, v_includeEndPos_932_, v_severityOverrides_933_, v_vs_958_, v___x_972_, v___x_973_, v_x_935_);
lean_dec_ref(v_vs_958_);
return v___x_974_;
}
}
else
{
size_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; 
lean_del_object(v___x_960_);
v___x_975_ = ((size_t)0ULL);
v___x_976_ = lean_usize_of_nat(v___x_963_);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_930_, v_json_931_, v_includeEndPos_932_, v_severityOverrides_933_, v_vs_958_, v___x_975_, v___x_976_, v_x_935_);
lean_dec_ref(v_vs_958_);
return v___x_977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(lean_object* v_opts_979_, uint8_t v_json_980_, uint8_t v_includeEndPos_981_, lean_object* v_severityOverrides_982_, lean_object* v_as_983_, size_t v_i_984_, size_t v_stop_985_, lean_object* v_b_986_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = lean_usize_dec_eq(v_i_984_, v_stop_985_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_array_uget_borrowed(v_as_983_, v_i_984_);
lean_inc(v___x_989_);
v___x_990_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_979_, v_json_980_, v_includeEndPos_981_, v_severityOverrides_982_, v___x_989_, v_b_986_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; size_t v___x_992_; size_t v___x_993_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref(v___x_990_);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_add(v_i_984_, v___x_992_);
v_i_984_ = v___x_993_;
v_b_986_ = v_a_991_;
goto _start;
}
else
{
return v___x_990_;
}
}
else
{
lean_object* v___x_995_; 
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v_b_986_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5___boxed(lean_object* v_opts_996_, lean_object* v_json_997_, lean_object* v_includeEndPos_998_, lean_object* v_severityOverrides_999_, lean_object* v_as_1000_, lean_object* v_i_1001_, lean_object* v_stop_1002_, lean_object* v_b_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v_json_boxed_1005_; uint8_t v_includeEndPos_boxed_1006_; size_t v_i_boxed_1007_; size_t v_stop_boxed_1008_; lean_object* v_res_1009_; 
v_json_boxed_1005_ = lean_unbox(v_json_997_);
v_includeEndPos_boxed_1006_ = lean_unbox(v_includeEndPos_998_);
v_i_boxed_1007_ = lean_unbox_usize(v_i_1001_);
lean_dec(v_i_1001_);
v_stop_boxed_1008_ = lean_unbox_usize(v_stop_1002_);
lean_dec(v_stop_1002_);
v_res_1009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_996_, v_json_boxed_1005_, v_includeEndPos_boxed_1006_, v_severityOverrides_999_, v_as_1000_, v_i_boxed_1007_, v_stop_boxed_1008_, v_b_1003_);
lean_dec_ref(v_as_1000_);
lean_dec(v_severityOverrides_999_);
lean_dec_ref(v_opts_996_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6___boxed(lean_object* v_opts_1010_, lean_object* v_json_1011_, lean_object* v_includeEndPos_1012_, lean_object* v_severityOverrides_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v_json_boxed_1017_; uint8_t v_includeEndPos_boxed_1018_; lean_object* v_res_1019_; 
v_json_boxed_1017_ = lean_unbox(v_json_1011_);
v_includeEndPos_boxed_1018_ = lean_unbox(v_includeEndPos_1012_);
v_res_1019_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1010_, v_json_boxed_1017_, v_includeEndPos_boxed_1018_, v_severityOverrides_1013_, v_x_1014_, v_x_1015_);
lean_dec(v_severityOverrides_1013_);
lean_dec_ref(v_opts_1010_);
return v_res_1019_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(lean_object* v_opts_1021_, uint8_t v_json_1022_, uint8_t v_includeEndPos_1023_, lean_object* v_severityOverrides_1024_, lean_object* v_x_1025_, size_t v_x_1026_, size_t v_x_1027_, lean_object* v_x_1028_){
_start:
{
if (lean_obj_tag(v_x_1025_) == 0)
{
lean_object* v_cs_1030_; lean_object* v___x_1031_; size_t v___x_1032_; lean_object* v_j_1033_; lean_object* v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v_cs_1030_ = lean_ctor_get(v_x_1025_, 0);
lean_inc_ref(v_cs_1030_);
lean_dec_ref(v_x_1025_);
v___x_1031_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0);
v___x_1032_ = lean_usize_shift_right(v_x_1026_, v_x_1027_);
v_j_1033_ = lean_usize_to_nat(v___x_1032_);
v___x_1034_ = lean_array_get_borrowed(v___x_1031_, v_cs_1030_, v_j_1033_);
v___x_1035_ = ((size_t)1ULL);
v___x_1036_ = lean_usize_shift_left(v___x_1035_, v_x_1027_);
v___x_1037_ = lean_usize_sub(v___x_1036_, v___x_1035_);
v___x_1038_ = lean_usize_land(v_x_1026_, v___x_1037_);
v___x_1039_ = ((size_t)5ULL);
v___x_1040_ = lean_usize_sub(v_x_1027_, v___x_1039_);
lean_inc(v___x_1034_);
v___x_1041_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1021_, v_json_1022_, v_includeEndPos_1023_, v_severityOverrides_1024_, v___x_1034_, v___x_1038_, v___x_1040_, v_x_1028_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_nat_add(v_j_1033_, v___x_1043_);
lean_dec(v_j_1033_);
v___x_1045_ = lean_array_get_size(v_cs_1030_);
v___x_1046_ = lean_nat_dec_lt(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_dec(v___x_1044_);
lean_dec(v_a_1042_);
lean_dec_ref(v_cs_1030_);
return v___x_1041_;
}
else
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_nat_dec_le(v___x_1045_, v___x_1045_);
if (v___x_1047_ == 0)
{
if (v___x_1046_ == 0)
{
lean_dec(v___x_1044_);
lean_dec(v_a_1042_);
lean_dec_ref(v_cs_1030_);
return v___x_1041_;
}
else
{
size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
lean_dec_ref(v___x_1041_);
v___x_1048_ = lean_usize_of_nat(v___x_1044_);
lean_dec(v___x_1044_);
v___x_1049_ = lean_usize_of_nat(v___x_1045_);
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1021_, v_json_1022_, v_includeEndPos_1023_, v_severityOverrides_1024_, v_cs_1030_, v___x_1048_, v___x_1049_, v_a_1042_);
lean_dec_ref(v_cs_1030_);
return v___x_1050_;
}
}
else
{
size_t v___x_1051_; size_t v___x_1052_; lean_object* v___x_1053_; 
lean_dec_ref(v___x_1041_);
v___x_1051_ = lean_usize_of_nat(v___x_1044_);
lean_dec(v___x_1044_);
v___x_1052_ = lean_usize_of_nat(v___x_1045_);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1021_, v_json_1022_, v_includeEndPos_1023_, v_severityOverrides_1024_, v_cs_1030_, v___x_1051_, v___x_1052_, v_a_1042_);
lean_dec_ref(v_cs_1030_);
return v___x_1053_;
}
}
}
else
{
lean_dec(v_j_1033_);
lean_dec_ref(v_cs_1030_);
return v___x_1041_;
}
}
else
{
lean_object* v_vs_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1074_; 
v_vs_1054_ = lean_ctor_get(v_x_1025_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_x_1025_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1056_ = v_x_1025_;
v_isShared_1057_ = v_isSharedCheck_1074_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_vs_1054_);
lean_dec(v_x_1025_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1074_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1058_ = lean_usize_to_nat(v_x_1026_);
v___x_1059_ = lean_array_get_size(v_vs_1054_);
v___x_1060_ = lean_nat_dec_lt(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1062_; 
lean_dec(v___x_1058_);
lean_dec_ref(v_vs_1054_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set_tag(v___x_1056_, 0);
lean_ctor_set(v___x_1056_, 0, v_x_1028_);
v___x_1062_ = v___x_1056_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_x_1028_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_nat_dec_le(v___x_1059_, v___x_1059_);
if (v___x_1064_ == 0)
{
if (v___x_1060_ == 0)
{
lean_object* v___x_1066_; 
lean_dec(v___x_1058_);
lean_dec_ref(v_vs_1054_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set_tag(v___x_1056_, 0);
lean_ctor_set(v___x_1056_, 0, v_x_1028_);
v___x_1066_ = v___x_1056_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_x_1028_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
size_t v___x_1068_; size_t v___x_1069_; lean_object* v___x_1070_; 
lean_del_object(v___x_1056_);
v___x_1068_ = lean_usize_of_nat(v___x_1058_);
lean_dec(v___x_1058_);
v___x_1069_ = lean_usize_of_nat(v___x_1059_);
v___x_1070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1021_, v_json_1022_, v_includeEndPos_1023_, v_severityOverrides_1024_, v_vs_1054_, v___x_1068_, v___x_1069_, v_x_1028_);
lean_dec_ref(v_vs_1054_);
return v___x_1070_;
}
}
else
{
size_t v___x_1071_; size_t v___x_1072_; lean_object* v___x_1073_; 
lean_del_object(v___x_1056_);
v___x_1071_ = lean_usize_of_nat(v___x_1058_);
lean_dec(v___x_1058_);
v___x_1072_ = lean_usize_of_nat(v___x_1059_);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1021_, v_json_1022_, v_includeEndPos_1023_, v_severityOverrides_1024_, v_vs_1054_, v___x_1071_, v___x_1072_, v_x_1028_);
lean_dec_ref(v_vs_1054_);
return v___x_1073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___boxed(lean_object* v_opts_1075_, lean_object* v_json_1076_, lean_object* v_includeEndPos_1077_, lean_object* v_severityOverrides_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v_json_boxed_1084_; uint8_t v_includeEndPos_boxed_1085_; size_t v_x_4490__boxed_1086_; size_t v_x_4491__boxed_1087_; lean_object* v_res_1088_; 
v_json_boxed_1084_ = lean_unbox(v_json_1076_);
v_includeEndPos_boxed_1085_ = lean_unbox(v_includeEndPos_1077_);
v_x_4490__boxed_1086_ = lean_unbox_usize(v_x_1080_);
lean_dec(v_x_1080_);
v_x_4491__boxed_1087_ = lean_unbox_usize(v_x_1081_);
lean_dec(v_x_1081_);
v_res_1088_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1075_, v_json_boxed_1084_, v_includeEndPos_boxed_1085_, v_severityOverrides_1078_, v_x_1079_, v_x_4490__boxed_1086_, v_x_4491__boxed_1087_, v_x_1082_);
lean_dec(v_severityOverrides_1078_);
lean_dec_ref(v_opts_1075_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(lean_object* v_opts_1089_, uint8_t v_json_1090_, uint8_t v_includeEndPos_1091_, lean_object* v_severityOverrides_1092_, lean_object* v_t_1093_, lean_object* v_init_1094_, lean_object* v_start_1095_){
_start:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = lean_nat_dec_eq(v_start_1095_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v_root_1099_; lean_object* v_tail_1100_; size_t v_shift_1101_; lean_object* v_tailOff_1102_; uint8_t v___x_1103_; 
v_root_1099_ = lean_ctor_get(v_t_1093_, 0);
lean_inc_ref(v_root_1099_);
v_tail_1100_ = lean_ctor_get(v_t_1093_, 1);
lean_inc_ref(v_tail_1100_);
v_shift_1101_ = lean_ctor_get_usize(v_t_1093_, 4);
v_tailOff_1102_ = lean_ctor_get(v_t_1093_, 3);
lean_inc(v_tailOff_1102_);
lean_dec_ref(v_t_1093_);
v___x_1103_ = lean_nat_dec_le(v_tailOff_1102_, v_start_1095_);
if (v___x_1103_ == 0)
{
size_t v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v_tailOff_1102_);
v___x_1104_ = lean_usize_of_nat(v_start_1095_);
v___x_1105_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1089_, v_json_1090_, v_includeEndPos_1091_, v_severityOverrides_1092_, v_root_1099_, v___x_1104_, v_shift_1101_, v_init_1094_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
v___x_1107_ = lean_array_get_size(v_tail_1100_);
v___x_1108_ = lean_nat_dec_lt(v___x_1097_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_dec(v_a_1106_);
lean_dec_ref(v_tail_1100_);
return v___x_1105_;
}
else
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_nat_dec_le(v___x_1107_, v___x_1107_);
if (v___x_1109_ == 0)
{
if (v___x_1108_ == 0)
{
lean_dec(v_a_1106_);
lean_dec_ref(v_tail_1100_);
return v___x_1105_;
}
else
{
size_t v___x_1110_; size_t v___x_1111_; lean_object* v___x_1112_; 
lean_dec_ref(v___x_1105_);
v___x_1110_ = ((size_t)0ULL);
v___x_1111_ = lean_usize_of_nat(v___x_1107_);
v___x_1112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1089_, v_json_1090_, v_includeEndPos_1091_, v_severityOverrides_1092_, v_tail_1100_, v___x_1110_, v___x_1111_, v_a_1106_);
lean_dec_ref(v_tail_1100_);
return v___x_1112_;
}
}
else
{
size_t v___x_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
lean_dec_ref(v___x_1105_);
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = lean_usize_of_nat(v___x_1107_);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1089_, v_json_1090_, v_includeEndPos_1091_, v_severityOverrides_1092_, v_tail_1100_, v___x_1113_, v___x_1114_, v_a_1106_);
lean_dec_ref(v_tail_1100_);
return v___x_1115_;
}
}
}
else
{
lean_dec_ref(v_tail_1100_);
return v___x_1105_;
}
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
lean_dec_ref(v_root_1099_);
v___x_1116_ = lean_nat_sub(v_start_1095_, v_tailOff_1102_);
lean_dec(v_tailOff_1102_);
v___x_1117_ = lean_array_get_size(v_tail_1100_);
v___x_1118_ = lean_nat_dec_lt(v___x_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_dec(v___x_1116_);
lean_dec_ref(v_tail_1100_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_init_1094_);
return v___x_1119_;
}
else
{
uint8_t v___x_1120_; 
v___x_1120_ = lean_nat_dec_le(v___x_1117_, v___x_1117_);
if (v___x_1120_ == 0)
{
if (v___x_1118_ == 0)
{
lean_object* v___x_1121_; 
lean_dec(v___x_1116_);
lean_dec_ref(v_tail_1100_);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v_init_1094_);
return v___x_1121_;
}
else
{
size_t v___x_1122_; size_t v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_usize_of_nat(v___x_1116_);
lean_dec(v___x_1116_);
v___x_1123_ = lean_usize_of_nat(v___x_1117_);
v___x_1124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1089_, v_json_1090_, v_includeEndPos_1091_, v_severityOverrides_1092_, v_tail_1100_, v___x_1122_, v___x_1123_, v_init_1094_);
lean_dec_ref(v_tail_1100_);
return v___x_1124_;
}
}
else
{
size_t v___x_1125_; size_t v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_usize_of_nat(v___x_1116_);
lean_dec(v___x_1116_);
v___x_1126_ = lean_usize_of_nat(v___x_1117_);
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1089_, v_json_1090_, v_includeEndPos_1091_, v_severityOverrides_1092_, v_tail_1100_, v___x_1125_, v___x_1126_, v_init_1094_);
lean_dec_ref(v_tail_1100_);
return v___x_1127_;
}
}
}
}
else
{
lean_object* v_root_1128_; lean_object* v_tail_1129_; lean_object* v___x_1130_; 
v_root_1128_ = lean_ctor_get(v_t_1093_, 0);
lean_inc_ref(v_root_1128_);
v_tail_1129_ = lean_ctor_get(v_t_1093_, 1);
lean_inc_ref(v_tail_1129_);
lean_dec_ref(v_t_1093_);
v___x_1130_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1089_, v_json_1090_, v_includeEndPos_1091_, v_severityOverrides_1092_, v_root_1128_, v_init_1094_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
v___x_1132_ = lean_array_get_size(v_tail_1129_);
v___x_1133_ = lean_nat_dec_lt(v___x_1097_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_dec(v_a_1131_);
lean_dec_ref(v_tail_1129_);
return v___x_1130_;
}
else
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_nat_dec_le(v___x_1132_, v___x_1132_);
if (v___x_1134_ == 0)
{
if (v___x_1133_ == 0)
{
lean_dec(v_a_1131_);
lean_dec_ref(v_tail_1129_);
return v___x_1130_;
}
else
{
size_t v___x_1135_; size_t v___x_1136_; lean_object* v___x_1137_; 
lean_dec_ref(v___x_1130_);
v___x_1135_ = ((size_t)0ULL);
v___x_1136_ = lean_usize_of_nat(v___x_1132_);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1089_, v_json_1090_, v_includeEndPos_1091_, v_severityOverrides_1092_, v_tail_1129_, v___x_1135_, v___x_1136_, v_a_1131_);
lean_dec_ref(v_tail_1129_);
return v___x_1137_;
}
}
else
{
size_t v___x_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref(v___x_1130_);
v___x_1138_ = ((size_t)0ULL);
v___x_1139_ = lean_usize_of_nat(v___x_1132_);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1089_, v_json_1090_, v_includeEndPos_1091_, v_severityOverrides_1092_, v_tail_1129_, v___x_1138_, v___x_1139_, v_a_1131_);
lean_dec_ref(v_tail_1129_);
return v___x_1140_;
}
}
}
else
{
lean_dec_ref(v_tail_1129_);
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4___boxed(lean_object* v_opts_1141_, lean_object* v_json_1142_, lean_object* v_includeEndPos_1143_, lean_object* v_severityOverrides_1144_, lean_object* v_t_1145_, lean_object* v_init_1146_, lean_object* v_start_1147_, lean_object* v___y_1148_){
_start:
{
uint8_t v_json_boxed_1149_; uint8_t v_includeEndPos_boxed_1150_; lean_object* v_res_1151_; 
v_json_boxed_1149_ = lean_unbox(v_json_1142_);
v_includeEndPos_boxed_1150_ = lean_unbox(v_includeEndPos_1143_);
v_res_1151_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1141_, v_json_boxed_1149_, v_includeEndPos_boxed_1150_, v_severityOverrides_1144_, v_t_1145_, v_init_1146_, v_start_1147_);
lean_dec(v_start_1147_);
lean_dec(v_severityOverrides_1144_);
lean_dec_ref(v_opts_1141_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(lean_object* v_msgLog_1152_, lean_object* v_opts_1153_, uint8_t v_json_1154_, lean_object* v_severityOverrides_1155_, lean_object* v_numErrors_1156_){
_start:
{
lean_object* v_unreported_1158_; lean_object* v___x_1159_; uint8_t v_includeEndPos_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_unreported_1158_ = lean_ctor_get(v_msgLog_1152_, 1);
lean_inc_ref(v_unreported_1158_);
lean_dec_ref(v_msgLog_1152_);
v___x_1159_ = l_Lean_Language_printMessageEndPos;
v_includeEndPos_1160_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_1153_, v___x_1159_);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1153_, v_json_1154_, v_includeEndPos_1160_, v_severityOverrides_1155_, v_unreported_1158_, v_numErrors_1156_, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___boxed(lean_object* v_msgLog_1163_, lean_object* v_opts_1164_, lean_object* v_json_1165_, lean_object* v_severityOverrides_1166_, lean_object* v_numErrors_1167_, lean_object* v_a_1168_){
_start:
{
uint8_t v_json_boxed_1169_; lean_object* v_res_1170_; 
v_json_boxed_1169_ = lean_unbox(v_json_1165_);
v_res_1170_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1163_, v_opts_1164_, v_json_boxed_1169_, v_severityOverrides_1166_, v_numErrors_1167_);
lean_dec(v_severityOverrides_1166_);
lean_dec_ref(v_opts_1164_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object* v_opts_1171_, uint8_t v_json_1172_, lean_object* v_severityOverrides_1173_, lean_object* v_s_1174_, lean_object* v_init_1175_){
_start:
{
lean_object* v_element_1177_; lean_object* v_diagnostics_1178_; lean_object* v_children_1179_; lean_object* v_msgLog_1180_; lean_object* v___x_1181_; 
v_element_1177_ = lean_ctor_get(v_s_1174_, 0);
v_diagnostics_1178_ = lean_ctor_get(v_element_1177_, 1);
lean_inc_ref(v_diagnostics_1178_);
v_children_1179_ = lean_ctor_get(v_s_1174_, 1);
lean_inc_ref(v_children_1179_);
lean_dec_ref(v_s_1174_);
v_msgLog_1180_ = lean_ctor_get(v_diagnostics_1178_, 0);
lean_inc_ref(v_msgLog_1180_);
lean_dec_ref(v_diagnostics_1178_);
v___x_1181_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1180_, v_opts_1171_, v_json_1172_, v_severityOverrides_1173_, v_init_1175_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = lean_array_get_size(v_children_1179_);
v___x_1185_ = lean_nat_dec_lt(v___x_1183_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_dec(v_a_1182_);
lean_dec_ref(v_children_1179_);
return v___x_1181_;
}
else
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_nat_dec_le(v___x_1184_, v___x_1184_);
if (v___x_1186_ == 0)
{
if (v___x_1185_ == 0)
{
lean_dec(v_a_1182_);
lean_dec_ref(v_children_1179_);
return v___x_1181_;
}
else
{
size_t v___x_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v___x_1181_);
v___x_1187_ = ((size_t)0ULL);
v___x_1188_ = lean_usize_of_nat(v___x_1184_);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1171_, v_json_1172_, v_severityOverrides_1173_, v_children_1179_, v___x_1187_, v___x_1188_, v_a_1182_);
lean_dec_ref(v_children_1179_);
return v___x_1189_;
}
}
else
{
size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
lean_dec_ref(v___x_1181_);
v___x_1190_ = ((size_t)0ULL);
v___x_1191_ = lean_usize_of_nat(v___x_1184_);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1171_, v_json_1172_, v_severityOverrides_1173_, v_children_1179_, v___x_1190_, v___x_1191_, v_a_1182_);
lean_dec_ref(v_children_1179_);
return v___x_1192_;
}
}
}
else
{
lean_dec_ref(v_children_1179_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object* v_opts_1193_, uint8_t v_json_1194_, lean_object* v_severityOverrides_1195_, lean_object* v_as_1196_, size_t v_i_1197_, size_t v_stop_1198_, lean_object* v_b_1199_){
_start:
{
uint8_t v___x_1201_; 
v___x_1201_ = lean_usize_dec_eq(v_i_1197_, v_stop_1198_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_array_uget_borrowed(v_as_1196_, v_i_1197_);
lean_inc(v___x_1202_);
v___x_1203_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1202_);
v___x_1204_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1193_, v_json_1194_, v_severityOverrides_1195_, v___x_1203_, v_b_1199_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; size_t v___x_1206_; size_t v___x_1207_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref(v___x_1204_);
v___x_1206_ = ((size_t)1ULL);
v___x_1207_ = lean_usize_add(v_i_1197_, v___x_1206_);
v_i_1197_ = v___x_1207_;
v_b_1199_ = v_a_1205_;
goto _start;
}
else
{
return v___x_1204_;
}
}
else
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_b_1199_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object* v_opts_1210_, lean_object* v_json_1211_, lean_object* v_severityOverrides_1212_, lean_object* v_as_1213_, lean_object* v_i_1214_, lean_object* v_stop_1215_, lean_object* v_b_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v_json_boxed_1218_; size_t v_i_boxed_1219_; size_t v_stop_boxed_1220_; lean_object* v_res_1221_; 
v_json_boxed_1218_ = lean_unbox(v_json_1211_);
v_i_boxed_1219_ = lean_unbox_usize(v_i_1214_);
lean_dec(v_i_1214_);
v_stop_boxed_1220_ = lean_unbox_usize(v_stop_1215_);
lean_dec(v_stop_1215_);
v_res_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1210_, v_json_boxed_1218_, v_severityOverrides_1212_, v_as_1213_, v_i_boxed_1219_, v_stop_boxed_1220_, v_b_1216_);
lean_dec_ref(v_as_1213_);
lean_dec(v_severityOverrides_1212_);
lean_dec_ref(v_opts_1210_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object* v_opts_1222_, lean_object* v_json_1223_, lean_object* v_severityOverrides_1224_, lean_object* v_s_1225_, lean_object* v_init_1226_, lean_object* v___y_1227_){
_start:
{
uint8_t v_json_boxed_1228_; lean_object* v_res_1229_; 
v_json_boxed_1228_ = lean_unbox(v_json_1223_);
v_res_1229_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1222_, v_json_boxed_1228_, v_severityOverrides_1224_, v_s_1225_, v_init_1226_);
lean_dec(v_severityOverrides_1224_);
lean_dec_ref(v_opts_1222_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object* v_s_1230_, lean_object* v_opts_1231_, uint8_t v_json_1232_, lean_object* v_severityOverrides_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1231_, v_json_1232_, v_severityOverrides_1233_, v_s_1230_, v___x_1235_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1246_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1246_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1246_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1241_ = lean_nat_dec_lt(v___x_1235_, v_a_1237_);
lean_dec(v_a_1237_);
v___x_1242_ = lean_box(v___x_1241_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1242_);
v___x_1244_ = v___x_1239_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_a_1247_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1236_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1236_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object* v_s_1255_, lean_object* v_opts_1256_, lean_object* v_json_1257_, lean_object* v_severityOverrides_1258_, lean_object* v_a_1259_){
_start:
{
uint8_t v_json_boxed_1260_; lean_object* v_res_1261_; 
v_json_boxed_1260_ = lean_unbox(v_json_1257_);
v_res_1261_ = l_Lean_Language_SnapshotTree_runAndReport(v_s_1255_, v_opts_1256_, v_json_boxed_1260_, v_severityOverrides_1258_);
lean_dec(v_severityOverrides_1258_);
lean_dec_ref(v_opts_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(lean_object* v_s_1262_, lean_object* v_init_1263_){
_start:
{
lean_object* v_element_1264_; lean_object* v_children_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_element_1264_ = lean_ctor_get(v_s_1262_, 0);
lean_inc_ref(v_element_1264_);
v_children_1265_ = lean_ctor_get(v_s_1262_, 1);
lean_inc_ref(v_children_1265_);
lean_dec_ref(v_s_1262_);
v___x_1266_ = lean_array_push(v_init_1263_, v_element_1264_);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_array_get_size(v_children_1265_);
v___x_1269_ = lean_nat_dec_lt(v___x_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_dec_ref(v_children_1265_);
return v___x_1266_;
}
else
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_nat_dec_le(v___x_1268_, v___x_1268_);
if (v___x_1270_ == 0)
{
if (v___x_1269_ == 0)
{
lean_dec_ref(v_children_1265_);
return v___x_1266_;
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = lean_usize_of_nat(v___x_1268_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_1265_, v___x_1271_, v___x_1272_, v___x_1266_);
lean_dec_ref(v_children_1265_);
return v___x_1273_;
}
}
else
{
size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = lean_usize_of_nat(v___x_1268_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_1265_, v___x_1274_, v___x_1275_, v___x_1266_);
lean_dec_ref(v_children_1265_);
return v___x_1276_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object* v_as_1277_, size_t v_i_1278_, size_t v_stop_1279_, lean_object* v_b_1280_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_eq(v_i_1278_, v_stop_1279_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; 
v___x_1282_ = lean_array_uget_borrowed(v_as_1277_, v_i_1278_);
lean_inc(v___x_1282_);
v___x_1283_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1282_);
v___x_1284_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v___x_1283_, v_b_1280_);
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = lean_usize_add(v_i_1278_, v___x_1285_);
v_i_1278_ = v___x_1286_;
v_b_1280_ = v___x_1284_;
goto _start;
}
else
{
return v_b_1280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object* v_as_1288_, lean_object* v_i_1289_, lean_object* v_stop_1290_, lean_object* v_b_1291_){
_start:
{
size_t v_i_boxed_1292_; size_t v_stop_boxed_1293_; lean_object* v_res_1294_; 
v_i_boxed_1292_ = lean_unbox_usize(v_i_1289_);
lean_dec(v_i_1289_);
v_stop_boxed_1293_ = lean_unbox_usize(v_stop_1290_);
lean_dec(v_stop_1290_);
v_res_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_as_1288_, v_i_boxed_1292_, v_stop_boxed_1293_, v_b_1291_);
lean_dec_ref(v_as_1288_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object* v_s_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_Language_SnapshotTree_getAll___closed__0));
v___x_1299_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v_s_1297_, v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = lean_box(0);
v___x_1301_ = lean_task_pure(v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed(lean_object* v_tail_1302_, lean_object* v_t_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(v_tail_1302_, v_t_1303_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(lean_object* v_a_1306_){
_start:
{
if (lean_obj_tag(v_a_1306_) == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_obj_once(&l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0, &l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0_once, _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0);
return v___x_1308_;
}
else
{
lean_object* v_head_1309_; lean_object* v_tail_1310_; lean_object* v_task_1311_; lean_object* v___f_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; 
v_head_1309_ = lean_ctor_get(v_a_1306_, 0);
lean_inc(v_head_1309_);
v_tail_1310_ = lean_ctor_get(v_a_1306_, 1);
lean_inc(v_tail_1310_);
lean_dec_ref(v_a_1306_);
v_task_1311_ = lean_ctor_get(v_head_1309_, 3);
lean_inc_ref(v_task_1311_);
lean_dec(v_head_1309_);
v___f_1312_ = lean_alloc_closure((void*)(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1312_, 0, v_tail_1310_);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = 1;
v___x_1315_ = lean_io_bind_task(v_task_1311_, v___f_1312_, v___x_1313_, v___x_1314_);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object* v_tail_1316_, lean_object* v_t_1317_){
_start:
{
lean_object* v_children_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v_children_1319_ = lean_ctor_get(v_t_1317_, 1);
lean_inc_ref(v_children_1319_);
lean_dec_ref(v_t_1317_);
v___x_1320_ = lean_array_to_list(v_children_1319_);
v___x_1321_ = l_List_appendTR___redArg(v___x_1320_, v_tail_1316_);
v___x_1322_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___boxed(lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v_a_1323_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object* v_x_1326_){
_start:
{
lean_object* v_children_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_children_1328_ = lean_ctor_get(v_x_1326_, 1);
lean_inc_ref(v_children_1328_);
lean_dec_ref(v_x_1326_);
v___x_1329_ = lean_array_to_list(v_children_1328_);
v___x_1330_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll___boxed(lean_object* v_x_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Language_SnapshotTree_waitAll(v_x_1331_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object* v_00_u03b1_1334_, lean_object* v_act_1335_, lean_object* v_ctx_1336_){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_apply_2(v_act_1335_, v_ctx_1336_, lean_box(0));
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0___boxed(lean_object* v_00_u03b1_1340_, lean_object* v_act_1341_, lean_object* v_ctx_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(v_00_u03b1_1340_, v_act_1341_, v_ctx_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object* v_msgLog_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_st_mk_ref(v___x_1349_);
v___x_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_msgLog_1347_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog___boxed(lean_object* v_msgLog_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object* v_msg_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_fileMap_1363_; lean_object* v_source_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_fileMap_1363_ = lean_ctor_get(v_a_1361_, 2);
lean_inc_ref(v_fileMap_1363_);
lean_dec_ref(v_a_1361_);
v_source_1364_ = lean_ctor_get(v_fileMap_1363_, 0);
v___x_1365_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__0));
v___x_1366_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__1));
v___x_1367_ = lean_string_utf8_byte_size(v_source_1364_);
v___x_1368_ = l_Lean_FileMap_toPosition(v_fileMap_1363_, v___x_1367_);
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
v___x_1370_ = 0;
v___x_1371_ = 2;
v___x_1372_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot_default___closed__0));
v___x_1373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_msg_1360_);
v___x_1374_ = l_Lean_MessageData_ofFormat(v___x_1373_);
v___x_1375_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1375_, 0, v___x_1365_);
lean_ctor_set(v___x_1375_, 1, v___x_1366_);
lean_ctor_set(v___x_1375_, 2, v___x_1369_);
lean_ctor_set(v___x_1375_, 3, v___x_1372_);
lean_ctor_set(v___x_1375_, 4, v___x_1374_);
lean_ctor_set_uint8(v___x_1375_, sizeof(void*)*5, v___x_1370_);
lean_ctor_set_uint8(v___x_1375_, sizeof(void*)*5 + 1, v___x_1371_);
lean_ctor_set_uint8(v___x_1375_, sizeof(void*)*5 + 2, v___x_1370_);
v___x_1376_ = l_Lean_MessageLog_empty;
v___x_1377_ = l_Lean_MessageLog_add(v___x_1375_, v___x_1376_);
v___x_1378_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError___boxed(lean_object* v_msg_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_Language_diagnosticsOfHeaderError(v_msg_1379_, v_a_1380_);
return v_res_1382_;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2(void){
_start:
{
uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = 1;
v___x_1389_ = ((lean_object*)(l_Lean_Language_withHeaderExceptions___redArg___closed__1));
v___x_1390_ = l_Lean_Name_toString(v___x_1389_, v___x_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object* v_ex_1391_, lean_object* v_act_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v___x_1395_; 
lean_inc_ref(v_a_1393_);
v___x_1395_ = lean_apply_2(v_act_1392_, v_a_1393_, lean_box(0));
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; 
lean_dec_ref(v_a_1393_);
lean_dec(v_ex_1391_);
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref(v___x_1395_);
return v_a_1396_;
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_a_1397_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1397_);
lean_dec_ref(v___x_1395_);
v___x_1398_ = lean_io_error_to_string(v_a_1397_);
v___x_1399_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_1398_, v_a_1393_);
v___x_1400_ = lean_obj_once(&l_Lean_Language_withHeaderExceptions___redArg___closed__2, &l_Lean_Language_withHeaderExceptions___redArg___closed__2_once, _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2);
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__5, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__5_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__5);
v___x_1403_ = 0;
v___x_1404_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1404_, 0, v___x_1400_);
lean_ctor_set(v___x_1404_, 1, v___x_1399_);
lean_ctor_set(v___x_1404_, 2, v___x_1401_);
lean_ctor_set(v___x_1404_, 3, v___x_1402_);
lean_ctor_set_uint8(v___x_1404_, sizeof(void*)*4, v___x_1403_);
v___x_1405_ = lean_apply_1(v_ex_1391_, v___x_1404_);
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg___boxed(lean_object* v_ex_1406_, lean_object* v_act_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1406_, v_act_1407_, v_a_1408_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object* v_00_u03b1_1411_, lean_object* v_ex_1412_, lean_object* v_act_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1412_, v_act_1413_, v_a_1414_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___boxed(lean_object* v_00_u03b1_1417_, lean_object* v_ex_1418_, lean_object* v_act_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Language_withHeaderExceptions(v_00_u03b1_1417_, v_ex_1418_, v_act_1419_, v_a_1420_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object* v_val_1423_, lean_object* v_process_1424_, lean_object* v_ictx_1425_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1427_ = lean_st_ref_get(v_val_1423_);
v___x_1428_ = lean_apply_3(v_process_1424_, v___x_1427_, v_ictx_1425_, lean_box(0));
lean_inc(v___x_1428_);
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
v___x_1430_ = lean_st_ref_set(v_val_1423_, v___x_1429_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object* v_val_1431_, lean_object* v_process_1432_, lean_object* v_ictx_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(v_val_1431_, v_process_1432_, v_ictx_1433_);
lean_dec(v_val_1431_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object* v_process_1436_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; 
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_st_mk_ref(v___x_1438_);
v___f_1440_ = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1440_, 0, v___x_1439_);
lean_closure_set(v___f_1440_, 1, v_process_1436_);
return v___f_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___boxed(lean_object* v_process_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object* v_InitSnap_1444_, lean_object* v_process_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___boxed(lean_object* v_InitSnap_1448_, lean_object* v_process_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Language_mkIncrementalProcessor(v_InitSnap_1448_, v_process_1449_);
return v_res_1451_;
}
}
lean_object* runtime_initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Trace(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Language_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Language_Snapshot_instInhabitedDiagnostics_default = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics_default);
l_Lean_Language_Snapshot_instInhabitedDiagnostics = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics);
l_Lean_Language_Snapshot_Diagnostics_empty = _init_l_Lean_Language_Snapshot_Diagnostics_empty();
lean_mark_persistent(l_Lean_Language_Snapshot_Diagnostics_empty);
l_Lean_Language_instInhabitedSnapshot_default = _init_l_Lean_Language_instInhabitedSnapshot_default();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot_default);
l_Lean_Language_instInhabitedSnapshot = _init_l_Lean_Language_instInhabitedSnapshot();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot);
l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default = _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default();
lean_mark_persistent(l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default);
l_Lean_Language_SnapshotTask_instInhabitedReportingRange = _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange();
lean_mark_persistent(l_Lean_Language_SnapshotTask_instInhabitedReportingRange);
l_Lean_Language_instInhabitedSnapshotTree_default = _init_l_Lean_Language_instInhabitedSnapshotTree_default();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTree_default);
l_Lean_Language_instInhabitedSnapshotTree = _init_l_Lean_Language_instInhabitedSnapshotTree();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTree);
l_Lean_Language_instInhabitedSnapshotLeaf_default = _init_l_Lean_Language_instInhabitedSnapshotLeaf_default();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotLeaf_default);
l_Lean_Language_instInhabitedSnapshotLeaf = _init_l_Lean_Language_instInhabitedSnapshotLeaf();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotLeaf);
l_Lean_Language_instInhabitedDynamicSnapshot = _init_l_Lean_Language_instInhabitedDynamicSnapshot();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot);
res = l_Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Language_printMessageEndPos = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Language_printMessageEndPos);
lean_dec_ref(res);
res = l_Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Language_maxErrors = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Language_maxErrors);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Language_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Language_Snapshot_desc___autoParam = _init_l_Lean_Language_Snapshot_desc___autoParam();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* initialize_Lean_Util_Trace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Language_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Language_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Language_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
