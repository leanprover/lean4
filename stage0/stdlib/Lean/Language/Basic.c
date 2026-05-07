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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_task_pure(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
extern lean_object* l_instMonadBaseIO;
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_IO_CancelToken_set(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_exit(uint8_t);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
lean_object* l_Lean_Message_toJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MessageData_kind(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_mk_thunk(lean_object*);
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
static const lean_string_object l_Lean_Language_instInhabitedSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Language_instInhabitedSnapshot___closed__0 = (const lean_object*)&l_Lean_Language_instInhabitedSnapshot___closed__0_value;
static lean_once_cell_t l_Lean_Language_instInhabitedSnapshot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedSnapshot___closed__1;
static lean_once_cell_t l_Lean_Language_instInhabitedSnapshot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedSnapshot___closed__2;
static lean_once_cell_t l_Lean_Language_instInhabitedSnapshot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedSnapshot___closed__3;
static lean_once_cell_t l_Lean_Language_instInhabitedSnapshot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedSnapshot___closed__4;
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
static lean_once_cell_t l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0;
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
static const lean_string_object l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Language"};
static const lean_object* l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29_ = (const lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value;
static const lean_string_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "SnapshotTree"};
static const lean_object* l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29_ = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value;
static const lean_ctor_object l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value_aux_1),((lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(233, 91, 117, 52, 192, 104, 64, 53)}};
static const lean_object* l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29_ = (const lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29_ = (const lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instTypeNameSnapshotTree = (const lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value;
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
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "SnapshotLeaf"};
static const lean_object* l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value;
static const lean_ctor_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_1),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(145, 226, 163, 148, 17, 100, 140, 218)}};
static const lean_object* l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instTypeNameSnapshotLeaf = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotLeaf;
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
static const lean_ctor_object l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_1),((lean_object*)&l_Lean_Language_instInhabitedDynamicSnapshot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 233, 253, 247, 44, 199, 244, 14)}};
static const lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__1 = (const lean_object*)&l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value;
static lean_once_cell_t l_Lean_Language_instInhabitedDynamicSnapshot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__2;
static lean_once_cell_t l_Lean_Language_instInhabitedDynamicSnapshot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__3;
static lean_once_cell_t l_Lean_Language_instInhabitedDynamicSnapshot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__4;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedDynamicSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "printMessageEndPos"};
static const lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(132, 21, 81, 184, 167, 123, 94, 166)}};
static const lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "print end position of each message in addition to start position"};
static const lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(36, 253, 199, 254, 66, 50, 168, 11)}};
static const lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_printMessageEndPos;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "maxErrors"};
static const lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(229, 225, 16, 209, 3, 189, 8, 41)}};
static const lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "maximum number of errors to report (0 for no limit)"};
static const lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 143, 131, 92, 100, 78, 143, 101)}};
static const lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
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
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot___closed__1(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_unsigned_to_nat(32u);
v___x_125_ = lean_mk_empty_array_with_capacity(v___x_124_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot___closed__2(void){
_start:
{
size_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_127_ = ((size_t)5ULL);
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_unsigned_to_nat(32u);
v___x_130_ = lean_mk_empty_array_with_capacity(v___x_129_);
v___x_131_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__1, &l_Lean_Language_instInhabitedSnapshot___closed__1_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__1);
v___x_132_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
lean_ctor_set(v___x_132_, 2, v___x_128_);
lean_ctor_set(v___x_132_, 3, v___x_128_);
lean_ctor_set_usize(v___x_132_, 4, v___x_127_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot___closed__3(void){
_start:
{
lean_object* v___x_133_; uint64_t v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__2, &l_Lean_Language_instInhabitedSnapshot___closed__2_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__2);
v___x_134_ = 0ULL;
v___x_135_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set_uint64(v___x_135_, sizeof(void*)*1, v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot___closed__4(void){
_start:
{
uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_136_ = 0;
v___x_137_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_138_ = lean_box(0);
v___x_139_ = l_Lean_Language_Snapshot_instInhabitedDiagnostics_default;
v___x_140_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot___closed__0));
v___x_141_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
lean_ctor_set(v___x_141_, 2, v___x_138_);
lean_ctor_set(v___x_141_, 3, v___x_137_);
lean_ctor_set_uint8(v___x_141_, sizeof(void*)*4, v___x_136_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot(void){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(lean_object* v_x_143_){
_start:
{
switch(lean_obj_tag(v_x_143_))
{
case 0:
{
lean_object* v___x_144_; 
v___x_144_ = lean_unsigned_to_nat(0u);
return v___x_144_;
}
case 1:
{
lean_object* v___x_145_; 
v___x_145_ = lean_unsigned_to_nat(1u);
return v___x_145_;
}
default: 
{
lean_object* v___x_146_; 
v___x_146_ = lean_unsigned_to_nat(2u);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___boxed(lean_object* v_x_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(v_x_147_);
lean_dec(v_x_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(lean_object* v_t_149_, lean_object* v_k_150_){
_start:
{
if (lean_obj_tag(v_t_149_) == 1)
{
lean_object* v_range_151_; lean_object* v___x_152_; 
v_range_151_ = lean_ctor_get(v_t_149_, 0);
lean_inc_ref(v_range_151_);
lean_dec_ref(v_t_149_);
v___x_152_ = lean_apply_1(v_k_150_, v_range_151_);
return v___x_152_;
}
else
{
lean_dec(v_t_149_);
return v_k_150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(lean_object* v_motive_153_, lean_object* v_ctorIdx_154_, lean_object* v_t_155_, lean_object* v_h_156_, lean_object* v_k_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_155_, v_k_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___boxed(lean_object* v_motive_159_, lean_object* v_ctorIdx_160_, lean_object* v_t_161_, lean_object* v_h_162_, lean_object* v_k_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(v_motive_159_, v_ctorIdx_160_, v_t_161_, v_h_162_, v_k_163_);
lean_dec(v_ctorIdx_160_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim___redArg(lean_object* v_t_165_, lean_object* v_inherit_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_165_, v_inherit_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim(lean_object* v_motive_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_inherit_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_169_, v_inherit_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim___redArg(lean_object* v_t_173_, lean_object* v_some_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_173_, v_some_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim(lean_object* v_motive_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_some_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_177_, v_some_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim___redArg(lean_object* v_t_181_, lean_object* v_skip_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_181_, v_skip_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim(lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_skip_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_185_, v_skip_187_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default(void){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_box(0);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange(void){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(0);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(0);
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
v_val_193_ = lean_ctor_get(v_x_191_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_x_191_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v_x_191_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_val_193_);
lean_dec(v_x_191_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_val_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_box(0);
v___x_202_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object* v_stx_x3f_203_){
_start:
{
if (lean_obj_tag(v_stx_x3f_203_) == 0)
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0, &l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0_once, _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0);
return v___x_204_;
}
else
{
lean_object* v_val_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_val_205_ = lean_ctor_get(v_stx_x3f_203_, 0);
v___x_206_ = 1;
v___x_207_ = l_Lean_Syntax_getRange_x3f(v_val_205_, v___x_206_);
v___x_208_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___x_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange___boxed(lean_object* v_stx_x3f_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v_stx_x3f_209_);
lean_dec(v_stx_x3f_209_);
return v_res_210_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_box(0);
v___x_212_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object* v_inst_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_214_ = lean_box(0);
v___x_215_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0, &l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0_once, _init_l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0);
v___x_216_ = lean_task_pure(v_inst_213_);
v___x_217_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_217_, 0, v___x_214_);
lean_ctor_set(v___x_217_, 1, v___x_215_);
lean_ctor_set(v___x_217_, 2, v___x_214_);
lean_ctor_set(v___x_217_, 3, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default(lean_object* v_00_u03b1_218_, lean_object* v_inst_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask___redArg(lean_object* v_inst_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask(lean_object* v_a_223_, lean_object* v_inst_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object* v_stx_x3f_226_, lean_object* v_cancelTk_x3f_227_, lean_object* v_reportingRange_228_, lean_object* v_act_229_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_io_as_task(v_act_229_, v___x_231_);
v___x_233_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_233_, 0, v_stx_x3f_226_);
lean_ctor_set(v___x_233_, 1, v_reportingRange_228_);
lean_ctor_set(v___x_233_, 2, v_cancelTk_x3f_227_);
lean_ctor_set(v___x_233_, 3, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg___boxed(lean_object* v_stx_x3f_234_, lean_object* v_cancelTk_x3f_235_, lean_object* v_reportingRange_236_, lean_object* v_act_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v_stx_x3f_234_, v_cancelTk_x3f_235_, v_reportingRange_236_, v_act_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object* v_00_u03b1_240_, lean_object* v_stx_x3f_241_, lean_object* v_cancelTk_x3f_242_, lean_object* v_reportingRange_243_, lean_object* v_act_244_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v_stx_x3f_241_, v_cancelTk_x3f_242_, v_reportingRange_243_, v_act_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___boxed(lean_object* v_00_u03b1_247_, lean_object* v_stx_x3f_248_, lean_object* v_cancelTk_x3f_249_, lean_object* v_reportingRange_250_, lean_object* v_act_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Language_SnapshotTask_ofIO(v_00_u03b1_247_, v_stx_x3f_248_, v_cancelTk_x3f_249_, v_reportingRange_250_, v_act_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object* v_stx_x3f_254_, lean_object* v_a_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_256_ = lean_box(2);
v___x_257_ = lean_box(0);
v___x_258_ = lean_task_pure(v_a_255_);
v___x_259_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_259_, 0, v_stx_x3f_254_);
lean_ctor_set(v___x_259_, 1, v___x_256_);
lean_ctor_set(v___x_259_, 2, v___x_257_);
lean_ctor_set(v___x_259_, 3, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished(lean_object* v_00_u03b1_260_, lean_object* v_stx_x3f_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Language_SnapshotTask_finished___redArg(v_stx_x3f_261_, v_a_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object* v_t_264_, lean_object* v_f_265_, lean_object* v_stx_x3f_266_, lean_object* v_reportingRange_267_, uint8_t v_sync_268_){
_start:
{
lean_object* v_cancelTk_x3f_269_; lean_object* v_task_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_279_; 
v_cancelTk_x3f_269_ = lean_ctor_get(v_t_264_, 2);
v_task_270_ = lean_ctor_get(v_t_264_, 3);
v_isSharedCheck_279_ = !lean_is_exclusive(v_t_264_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; lean_object* v_unused_281_; 
v_unused_280_ = lean_ctor_get(v_t_264_, 1);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v_t_264_, 0);
lean_dec(v_unused_281_);
v___x_272_ = v_t_264_;
v_isShared_273_ = v_isSharedCheck_279_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_task_270_);
lean_inc(v_cancelTk_x3f_269_);
lean_dec(v_t_264_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_279_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_task_map(v_f_265_, v_task_270_, v___x_274_, v_sync_268_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 3, v___x_275_);
lean_ctor_set(v___x_272_, 1, v_reportingRange_267_);
lean_ctor_set(v___x_272_, 0, v_stx_x3f_266_);
v___x_277_ = v___x_272_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_stx_x3f_266_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_reportingRange_267_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_cancelTk_x3f_269_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg___boxed(lean_object* v_t_282_, lean_object* v_f_283_, lean_object* v_stx_x3f_284_, lean_object* v_reportingRange_285_, lean_object* v_sync_286_){
_start:
{
uint8_t v_sync_boxed_287_; lean_object* v_res_288_; 
v_sync_boxed_287_ = lean_unbox(v_sync_286_);
v_res_288_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_282_, v_f_283_, v_stx_x3f_284_, v_reportingRange_285_, v_sync_boxed_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map(lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_t_291_, lean_object* v_f_292_, lean_object* v_stx_x3f_293_, lean_object* v_reportingRange_294_, uint8_t v_sync_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_291_, v_f_292_, v_stx_x3f_293_, v_reportingRange_294_, v_sync_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___boxed(lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_t_299_, lean_object* v_f_300_, lean_object* v_stx_x3f_301_, lean_object* v_reportingRange_302_, lean_object* v_sync_303_){
_start:
{
uint8_t v_sync_boxed_304_; lean_object* v_res_305_; 
v_sync_boxed_304_ = lean_unbox(v_sync_303_);
v_res_305_ = l_Lean_Language_SnapshotTask_map(v_00_u03b1_297_, v_00_u03b2_298_, v_t_299_, v_f_300_, v_stx_x3f_301_, v_reportingRange_302_, v_sync_boxed_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(lean_object* v_act_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_309_; lean_object* v_task_310_; 
v___x_309_ = lean_apply_2(v_act_306_, v_a_307_, lean_box(0));
v_task_310_ = lean_ctor_get(v___x_309_, 3);
lean_inc_ref(v_task_310_);
lean_dec_ref(v___x_309_);
return v_task_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed(lean_object* v_act_311_, lean_object* v_a_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(v_act_311_, v_a_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object* v_t_315_, lean_object* v_act_316_, lean_object* v_stx_x3f_317_, lean_object* v_reportingRange_318_, lean_object* v_cancelTk_x3f_319_, uint8_t v_sync_320_){
_start:
{
lean_object* v_task_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_332_; 
v_task_322_ = lean_ctor_get(v_t_315_, 3);
v_isSharedCheck_332_ = !lean_is_exclusive(v_t_315_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; lean_object* v_unused_334_; lean_object* v_unused_335_; 
v_unused_333_ = lean_ctor_get(v_t_315_, 2);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_t_315_, 1);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_t_315_, 0);
lean_dec(v_unused_335_);
v___x_324_ = v_t_315_;
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_task_322_);
lean_dec(v_t_315_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___f_326_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_326_, 0, v_act_316_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_io_bind_task(v_task_322_, v___f_326_, v___x_327_, v_sync_320_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 3, v___x_328_);
lean_ctor_set(v___x_324_, 2, v_cancelTk_x3f_319_);
lean_ctor_set(v___x_324_, 1, v_reportingRange_318_);
lean_ctor_set(v___x_324_, 0, v_stx_x3f_317_);
v___x_330_ = v___x_324_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_stx_x3f_317_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_reportingRange_318_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_cancelTk_x3f_319_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___boxed(lean_object* v_t_336_, lean_object* v_act_337_, lean_object* v_stx_x3f_338_, lean_object* v_reportingRange_339_, lean_object* v_cancelTk_x3f_340_, lean_object* v_sync_341_, lean_object* v_a_342_){
_start:
{
uint8_t v_sync_boxed_343_; lean_object* v_res_344_; 
v_sync_boxed_343_ = lean_unbox(v_sync_341_);
v_res_344_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_t_336_, v_act_337_, v_stx_x3f_338_, v_reportingRange_339_, v_cancelTk_x3f_340_, v_sync_boxed_343_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object* v_00_u03b1_345_, lean_object* v_00_u03b2_346_, lean_object* v_t_347_, lean_object* v_act_348_, lean_object* v_stx_x3f_349_, lean_object* v_reportingRange_350_, lean_object* v_cancelTk_x3f_351_, uint8_t v_sync_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_t_347_, v_act_348_, v_stx_x3f_349_, v_reportingRange_350_, v_cancelTk_x3f_351_, v_sync_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___boxed(lean_object* v_00_u03b1_355_, lean_object* v_00_u03b2_356_, lean_object* v_t_357_, lean_object* v_act_358_, lean_object* v_stx_x3f_359_, lean_object* v_reportingRange_360_, lean_object* v_cancelTk_x3f_361_, lean_object* v_sync_362_, lean_object* v_a_363_){
_start:
{
uint8_t v_sync_boxed_364_; lean_object* v_res_365_; 
v_sync_boxed_364_ = lean_unbox(v_sync_362_);
v_res_365_ = l_Lean_Language_SnapshotTask_bindIO(v_00_u03b1_355_, v_00_u03b2_356_, v_t_357_, v_act_358_, v_stx_x3f_359_, v_reportingRange_360_, v_cancelTk_x3f_361_, v_sync_boxed_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object* v_t_366_){
_start:
{
lean_object* v_task_367_; lean_object* v___x_368_; 
v_task_367_ = lean_ctor_get(v_t_366_, 3);
lean_inc_ref(v_task_367_);
lean_dec_ref(v_t_366_);
v___x_368_ = lean_task_get_own(v_task_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object* v_00_u03b1_369_, lean_object* v_t_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Language_SnapshotTask_get___redArg(v_t_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object* v_t_372_){
_start:
{
lean_object* v_task_374_; uint8_t v___x_375_; 
v_task_374_ = lean_ctor_get(v_t_372_, 3);
lean_inc_ref(v_task_374_);
lean_dec_ref(v_t_372_);
v___x_375_ = lean_io_get_task_state(v_task_374_);
if (v___x_375_ == 2)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_task_get_own(v_task_374_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; 
lean_dec_ref(v_task_374_);
v___x_378_ = lean_box(0);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg___boxed(lean_object* v_t_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object* v_00_u03b1_382_, lean_object* v_t_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___boxed(lean_object* v_00_u03b1_386_, lean_object* v_t_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Language_SnapshotTask_get_x3f(v_00_u03b1_386_, v_t_387_);
return v_res_389_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshotTree_default___closed__0));
v___x_393_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default(void){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshotTree_default___closed__1, &l_Lean_Language_instInhabitedSnapshotTree_default___closed__1_once, _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree(void){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(lean_object* v_s_405_){
_start:
{
lean_inc_ref(v_s_405_);
return v_s_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed(lean_object* v_s_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(v_s_406_);
lean_dec_ref(v_s_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object* v_inst_410_, lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
lean_object* v___x_412_; 
lean_dec_ref(v_inst_410_);
v___x_412_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_412_;
}
else
{
lean_object* v_val_413_; lean_object* v___x_414_; 
v_val_413_ = lean_ctor_get(v_x_411_, 0);
lean_inc(v_val_413_);
lean_dec_ref(v_x_411_);
v___x_414_ = lean_apply_1(v_inst_410_, v_val_413_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg(lean_object* v_inst_415_){
_start:
{
lean_object* v___f_416_; 
v___f_416_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_416_, 0, v_inst_415_);
return v___f_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object* v_00_u03b1_417_, lean_object* v_inst_418_){
_start:
{
lean_object* v___f_419_; 
v___f_419_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_419_, 0, v_inst_418_);
return v___f_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(lean_object* v_inst_420_, lean_object* v___x_421_, lean_object* v___f_422_, lean_object* v_snap_423_){
_start:
{
lean_object* v___x_425_; lean_object* v_children_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_425_ = lean_apply_1(v_inst_420_, v_snap_423_);
v_children_426_ = lean_ctor_get(v___x_425_, 1);
lean_inc_ref(v_children_426_);
lean_dec_ref(v___x_425_);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_array_get_size(v_children_426_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_nat_dec_lt(v___x_427_, v___x_428_);
if (v___x_430_ == 0)
{
lean_dec_ref(v_children_426_);
lean_dec_ref(v___f_422_);
lean_dec_ref(v___x_421_);
return v___x_429_;
}
else
{
uint8_t v___x_431_; 
v___x_431_ = lean_nat_dec_le(v___x_428_, v___x_428_);
if (v___x_431_ == 0)
{
if (v___x_430_ == 0)
{
lean_dec_ref(v_children_426_);
lean_dec_ref(v___f_422_);
lean_dec_ref(v___x_421_);
return v___x_429_;
}
else
{
size_t v___x_432_; size_t v___x_433_; lean_object* v___x_219__overap_434_; lean_object* v___x_435_; 
v___x_432_ = ((size_t)0ULL);
v___x_433_ = lean_usize_of_nat(v___x_428_);
v___x_219__overap_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_421_, v___f_422_, v_children_426_, v___x_432_, v___x_433_, v___x_429_);
v___x_435_ = lean_apply_1(v___x_219__overap_434_, lean_box(0));
return v___x_435_;
}
}
else
{
size_t v___x_436_; size_t v___x_437_; lean_object* v___x_222__overap_438_; lean_object* v___x_439_; 
v___x_436_ = ((size_t)0ULL);
v___x_437_ = lean_usize_of_nat(v___x_428_);
v___x_222__overap_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_421_, v___f_422_, v_children_426_, v___x_436_, v___x_437_, v___x_429_);
v___x_439_ = lean_apply_1(v___x_222__overap_438_, lean_box(0));
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed(lean_object* v_inst_440_, lean_object* v___x_441_, lean_object* v___f_442_, lean_object* v_snap_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(v_inst_440_, v___x_441_, v___f_442_, v_snap_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(lean_object* v___f_446_, lean_object* v_x_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(v___f_446_, v_x_447_, v___y_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object* v_inst_451_, lean_object* v_t_452_){
_start:
{
lean_object* v___x_454_; lean_object* v_cancelTk_x3f_455_; lean_object* v_task_456_; lean_object* v___f_457_; lean_object* v___f_458_; lean_object* v___f_459_; 
v___x_454_ = l_instMonadBaseIO;
v_cancelTk_x3f_455_ = lean_ctor_get(v_t_452_, 2);
lean_inc(v_cancelTk_x3f_455_);
v_task_456_ = lean_ctor_get(v_t_452_, 3);
lean_inc_ref(v_task_456_);
lean_dec_ref(v_t_452_);
v___f_457_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0));
v___f_458_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_458_, 0, v___f_457_);
v___f_459_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_459_, 0, v_inst_451_);
lean_closure_set(v___f_459_, 1, v___x_454_);
lean_closure_set(v___f_459_, 2, v___f_458_);
if (lean_obj_tag(v_cancelTk_x3f_455_) == 1)
{
lean_object* v_val_464_; lean_object* v___x_465_; 
v_val_464_ = lean_ctor_get(v_cancelTk_x3f_455_, 0);
lean_inc(v_val_464_);
lean_dec_ref(v_cancelTk_x3f_455_);
v___x_465_ = l_IO_CancelToken_set(v_val_464_);
lean_dec(v_val_464_);
goto v___jp_460_;
}
else
{
lean_dec(v_cancelTk_x3f_455_);
goto v___jp_460_;
}
v___jp_460_:
{
lean_object* v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = 1;
v___x_463_ = l_BaseIO_chainTask___redArg(v_task_456_, v___f_459_, v___x_461_, v___x_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object* v___f_466_, lean_object* v_x_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_466_, v___y_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___boxed(lean_object* v_inst_471_, lean_object* v_t_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_471_, v_t_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object* v_00_u03b1_475_, lean_object* v_inst_476_, lean_object* v_t_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_476_, v_t_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___boxed(lean_object* v_00_u03b1_480_, lean_object* v_inst_481_, lean_object* v_t_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Language_SnapshotTask_cancelRec(v_00_u03b1_480_, v_inst_481_, v_t_482_);
return v_res_484_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotLeaf(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_unsigned_to_nat(32u);
v___x_493_ = lean_mk_empty_array_with_capacity(v___x_492_);
lean_dec_ref(v___x_493_);
v___x_494_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object* v_s_497_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0));
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v_s_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object* v_s_502_){
_start:
{
lean_object* v_tree_503_; lean_object* v___x_504_; 
v_tree_503_ = lean_ctor_get(v_s_502_, 1);
v___x_504_ = lean_thunk_get_own(v_tree_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object* v_s_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(v_s_505_);
lean_dec_ref(v_s_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0(lean_object* v_inst_509_, lean_object* v_val_510_, lean_object* v_x_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = lean_apply_1(v_inst_509_, v_val_510_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_val_515_){
_start:
{
lean_object* v___f_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
lean_inc(v_val_515_);
v___f_516_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_516_, 0, v_inst_514_);
lean_closure_set(v___f_516_, 1, v_val_515_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_inst_513_);
lean_ctor_set(v___x_517_, 1, v_val_515_);
v___x_518_ = lean_mk_thunk(v___f_516_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object* v_00_u03b1_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_val_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v_inst_521_, v_inst_522_, v_val_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object* v_inst_525_, lean_object* v_snap_526_){
_start:
{
lean_object* v_val_527_; lean_object* v___x_528_; 
v_val_527_ = lean_ctor_get(v_snap_526_, 0);
v___x_528_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_527_, v_inst_525_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object* v_inst_529_, lean_object* v_snap_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_529_, v_snap_530_);
lean_dec_ref(v_snap_530_);
lean_dec(v_inst_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object* v_00_u03b1_532_, lean_object* v_inst_533_, lean_object* v_snap_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_533_, v_snap_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object* v_00_u03b1_536_, lean_object* v_inst_537_, lean_object* v_snap_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f(v_00_u03b1_536_, v_inst_537_, v_snap_538_);
lean_dec_ref(v_snap_538_);
lean_dec(v_inst_537_);
return v_res_539_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2(void){
_start:
{
uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = 1;
v___x_546_ = ((lean_object*)(l_Lean_Language_instInhabitedDynamicSnapshot___closed__1));
v___x_547_ = l_Lean_Name_toString(v___x_546_, v___x_545_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3(void){
_start:
{
uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_548_ = 0;
v___x_549_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_550_ = lean_box(0);
v___x_551_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_552_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__2, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__2_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2);
v___x_553_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v___x_551_);
lean_ctor_set(v___x_553_, 2, v___x_550_);
lean_ctor_set(v___x_553_, 3, v___x_549_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*4, v___x_548_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4(void){
_start:
{
lean_object* v___x_554_; lean_object* v___f_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_554_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__3, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3);
v___f_555_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0));
v___x_556_ = ((lean_object*)(l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_));
v___x_557_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v___x_556_, v___f_555_, v___x_554_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot(void){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__4, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object* v_children_559_, lean_object* v_toApplicative_560_, lean_object* v_inst_561_, lean_object* v___f_562_, lean_object* v_____r_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_array_get_size(v_children_559_);
v___x_566_ = lean_box(0);
v___x_567_ = lean_nat_dec_lt(v___x_564_, v___x_565_);
if (v___x_567_ == 0)
{
lean_object* v_toPure_568_; lean_object* v___x_569_; 
lean_dec(v___f_562_);
lean_dec_ref(v_inst_561_);
lean_dec_ref(v_children_559_);
v_toPure_568_ = lean_ctor_get(v_toApplicative_560_, 1);
lean_inc(v_toPure_568_);
lean_dec_ref(v_toApplicative_560_);
v___x_569_ = lean_apply_2(v_toPure_568_, lean_box(0), v___x_566_);
return v___x_569_;
}
else
{
uint8_t v___x_570_; 
v___x_570_ = lean_nat_dec_le(v___x_565_, v___x_565_);
if (v___x_570_ == 0)
{
if (v___x_567_ == 0)
{
lean_object* v_toPure_571_; lean_object* v___x_572_; 
lean_dec(v___f_562_);
lean_dec_ref(v_inst_561_);
lean_dec_ref(v_children_559_);
v_toPure_571_ = lean_ctor_get(v_toApplicative_560_, 1);
lean_inc(v_toPure_571_);
lean_dec_ref(v_toApplicative_560_);
v___x_572_ = lean_apply_2(v_toPure_571_, lean_box(0), v___x_566_);
return v___x_572_;
}
else
{
size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; 
lean_dec_ref(v_toApplicative_560_);
v___x_573_ = ((size_t)0ULL);
v___x_574_ = lean_usize_of_nat(v___x_565_);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_561_, v___f_562_, v_children_559_, v___x_573_, v___x_574_, v___x_566_);
return v___x_575_;
}
}
else
{
size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; 
lean_dec_ref(v_toApplicative_560_);
v___x_576_ = ((size_t)0ULL);
v___x_577_ = lean_usize_of_nat(v___x_565_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_561_, v___f_562_, v_children_559_, v___x_576_, v___x_577_, v___x_566_);
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object* v_inst_579_, lean_object* v_s_580_, lean_object* v_f_581_){
_start:
{
lean_object* v_toApplicative_582_; lean_object* v_toBind_583_; lean_object* v_element_584_; lean_object* v_children_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_toApplicative_582_ = lean_ctor_get(v_inst_579_, 0);
lean_inc_ref(v_toApplicative_582_);
v_toBind_583_ = lean_ctor_get(v_inst_579_, 1);
lean_inc(v_toBind_583_);
v_element_584_ = lean_ctor_get(v_s_580_, 0);
lean_inc_ref(v_element_584_);
v_children_585_ = lean_ctor_get(v_s_580_, 1);
lean_inc_ref(v_children_585_);
lean_dec_ref(v_s_580_);
lean_inc(v_f_581_);
lean_inc_ref(v_inst_579_);
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_586_, 0, v_inst_579_);
lean_closure_set(v___f_586_, 1, v_f_581_);
v___f_587_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_587_, 0, v_children_585_);
lean_closure_set(v___f_587_, 1, v_toApplicative_582_);
lean_closure_set(v___f_587_, 2, v_inst_579_);
lean_closure_set(v___f_587_, 3, v___f_586_);
v___x_588_ = lean_apply_1(v_f_581_, v_element_584_);
v___x_589_ = lean_apply_4(v_toBind_583_, lean_box(0), lean_box(0), v___x_588_, v___f_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object* v_inst_590_, lean_object* v_f_591_, lean_object* v_x_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_Lean_Language_SnapshotTask_get___redArg(v___y_593_);
v___x_595_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_590_, v___x_594_, v_f_591_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object* v_m_596_, lean_object* v_inst_597_, lean_object* v_s_598_, lean_object* v_f_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_597_, v_s_598_, v_f_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object* v_children_601_, lean_object* v_toApplicative_602_, lean_object* v_inst_603_, lean_object* v___f_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_array_get_size(v_children_601_);
v___x_608_ = lean_nat_dec_lt(v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v_toPure_609_; lean_object* v___x_610_; 
lean_dec(v___f_604_);
lean_dec_ref(v_inst_603_);
lean_dec_ref(v_children_601_);
v_toPure_609_ = lean_ctor_get(v_toApplicative_602_, 1);
lean_inc(v_toPure_609_);
lean_dec_ref(v_toApplicative_602_);
v___x_610_ = lean_apply_2(v_toPure_609_, lean_box(0), v_a_605_);
return v___x_610_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = lean_nat_dec_le(v___x_607_, v___x_607_);
if (v___x_611_ == 0)
{
if (v___x_608_ == 0)
{
lean_object* v_toPure_612_; lean_object* v___x_613_; 
lean_dec(v___f_604_);
lean_dec_ref(v_inst_603_);
lean_dec_ref(v_children_601_);
v_toPure_612_ = lean_ctor_get(v_toApplicative_602_, 1);
lean_inc(v_toPure_612_);
lean_dec_ref(v_toApplicative_602_);
v___x_613_ = lean_apply_2(v_toPure_612_, lean_box(0), v_a_605_);
return v___x_613_;
}
else
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
lean_dec_ref(v_toApplicative_602_);
v___x_614_ = ((size_t)0ULL);
v___x_615_ = lean_usize_of_nat(v___x_607_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_603_, v___f_604_, v_children_601_, v___x_614_, v___x_615_, v_a_605_);
return v___x_616_;
}
}
else
{
size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; 
lean_dec_ref(v_toApplicative_602_);
v___x_617_ = ((size_t)0ULL);
v___x_618_ = lean_usize_of_nat(v___x_607_);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_603_, v___f_604_, v_children_601_, v___x_617_, v___x_618_, v_a_605_);
return v___x_619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object* v_inst_620_, lean_object* v_s_621_, lean_object* v_f_622_, lean_object* v_init_623_){
_start:
{
lean_object* v_toApplicative_624_; lean_object* v_toBind_625_; lean_object* v_element_626_; lean_object* v_children_627_; lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_toApplicative_624_ = lean_ctor_get(v_inst_620_, 0);
lean_inc_ref(v_toApplicative_624_);
v_toBind_625_ = lean_ctor_get(v_inst_620_, 1);
lean_inc(v_toBind_625_);
v_element_626_ = lean_ctor_get(v_s_621_, 0);
lean_inc_ref(v_element_626_);
v_children_627_ = lean_ctor_get(v_s_621_, 1);
lean_inc_ref(v_children_627_);
lean_dec_ref(v_s_621_);
lean_inc(v_f_622_);
lean_inc_ref(v_inst_620_);
v___f_628_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_628_, 0, v_inst_620_);
lean_closure_set(v___f_628_, 1, v_f_622_);
v___f_629_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_629_, 0, v_children_627_);
lean_closure_set(v___f_629_, 1, v_toApplicative_624_);
lean_closure_set(v___f_629_, 2, v_inst_620_);
lean_closure_set(v___f_629_, 3, v___f_628_);
v___x_630_ = lean_apply_2(v_f_622_, v_init_623_, v_element_626_);
v___x_631_ = lean_apply_4(v_toBind_625_, lean_box(0), lean_box(0), v___x_630_, v___f_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object* v_inst_632_, lean_object* v_f_633_, lean_object* v_a_634_, lean_object* v_snap_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = l_Lean_Language_SnapshotTask_get___redArg(v_snap_635_);
v___x_637_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_632_, v___x_636_, v_f_633_, v_a_634_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object* v_m_638_, lean_object* v_00_u03b1_639_, lean_object* v_inst_640_, lean_object* v_s_641_, lean_object* v_f_642_, lean_object* v_init_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_640_, v_s_641_, v_f_642_, v_init_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(lean_object* v_name_645_, lean_object* v_decl_646_, lean_object* v_ref_647_){
_start:
{
lean_object* v_defValue_649_; lean_object* v_descr_650_; lean_object* v_deprecation_x3f_651_; lean_object* v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_defValue_649_ = lean_ctor_get(v_decl_646_, 0);
v_descr_650_ = lean_ctor_get(v_decl_646_, 1);
v_deprecation_x3f_651_ = lean_ctor_get(v_decl_646_, 2);
v___x_652_ = lean_alloc_ctor(1, 0, 1);
v___x_653_ = lean_unbox(v_defValue_649_);
lean_ctor_set_uint8(v___x_652_, 0, v___x_653_);
lean_inc(v_deprecation_x3f_651_);
lean_inc_ref(v_descr_650_);
lean_inc_n(v_name_645_, 2);
v___x_654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_654_, 0, v_name_645_);
lean_ctor_set(v___x_654_, 1, v_ref_647_);
lean_ctor_set(v___x_654_, 2, v___x_652_);
lean_ctor_set(v___x_654_, 3, v_descr_650_);
lean_ctor_set(v___x_654_, 4, v_deprecation_x3f_651_);
v___x_655_ = lean_register_option(v_name_645_, v___x_654_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v___x_655_, 0);
lean_dec(v_unused_664_);
v___x_657_ = v___x_655_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_dec(v___x_655_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_inc(v_defValue_649_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_name_645_);
lean_ctor_set(v___x_659_, 1, v_defValue_649_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_name_645_);
v_a_665_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_655_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_655_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_673_, lean_object* v_decl_674_, lean_object* v_ref_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v_name_673_, v_decl_674_, v_ref_675_);
lean_dec_ref(v_decl_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_692_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_693_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_694_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_695_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v___x_692_, v___x_693_, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4____boxed(lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(lean_object* v_name_698_, lean_object* v_decl_699_, lean_object* v_ref_700_){
_start:
{
lean_object* v_defValue_702_; lean_object* v_descr_703_; lean_object* v_deprecation_x3f_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_defValue_702_ = lean_ctor_get(v_decl_699_, 0);
v_descr_703_ = lean_ctor_get(v_decl_699_, 1);
v_deprecation_x3f_704_ = lean_ctor_get(v_decl_699_, 2);
lean_inc(v_defValue_702_);
v___x_705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_705_, 0, v_defValue_702_);
lean_inc(v_deprecation_x3f_704_);
lean_inc_ref(v_descr_703_);
lean_inc_n(v_name_698_, 2);
v___x_706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_706_, 0, v_name_698_);
lean_ctor_set(v___x_706_, 1, v_ref_700_);
lean_ctor_set(v___x_706_, 2, v___x_705_);
lean_ctor_set(v___x_706_, 3, v_descr_703_);
lean_ctor_set(v___x_706_, 4, v_deprecation_x3f_704_);
v___x_707_ = lean_register_option(v_name_698_, v___x_706_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_715_; 
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v___x_707_, 0);
lean_dec(v_unused_716_);
v___x_709_ = v___x_707_;
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
else
{
lean_dec(v___x_707_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
lean_inc(v_defValue_702_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_name_698_);
lean_ctor_set(v___x_711_, 1, v_defValue_702_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_name_698_);
v_a_717_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_707_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_707_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_725_, lean_object* v_decl_726_, lean_object* v_ref_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v_name_725_, v_decl_726_, v_ref_727_);
lean_dec_ref(v_decl_726_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_744_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_745_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_746_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v___x_743_, v___x_744_, v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4____boxed(lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
return v_res_748_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(lean_object* v_opts_749_, lean_object* v_opt_750_){
_start:
{
lean_object* v_name_751_; lean_object* v_defValue_752_; lean_object* v_map_753_; lean_object* v___x_754_; 
v_name_751_ = lean_ctor_get(v_opt_750_, 0);
v_defValue_752_ = lean_ctor_get(v_opt_750_, 1);
v_map_753_ = lean_ctor_get(v_opts_749_, 0);
v___x_754_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_753_, v_name_751_);
if (lean_obj_tag(v___x_754_) == 0)
{
uint8_t v___x_755_; 
v___x_755_ = lean_unbox(v_defValue_752_);
return v___x_755_;
}
else
{
lean_object* v_val_756_; 
v_val_756_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_val_756_);
lean_dec_ref(v___x_754_);
if (lean_obj_tag(v_val_756_) == 1)
{
uint8_t v_v_757_; 
v_v_757_ = lean_ctor_get_uint8(v_val_756_, 0);
lean_dec_ref(v_val_756_);
return v_v_757_;
}
else
{
uint8_t v___x_758_; 
lean_dec(v_val_756_);
v___x_758_ = lean_unbox(v_defValue_752_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0___boxed(lean_object* v_opts_759_, lean_object* v_opt_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_759_, v_opt_760_);
lean_dec_ref(v_opt_760_);
lean_dec_ref(v_opts_759_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(lean_object* v_opts_763_, lean_object* v_opt_764_){
_start:
{
lean_object* v_name_765_; lean_object* v_defValue_766_; lean_object* v_map_767_; lean_object* v___x_768_; 
v_name_765_ = lean_ctor_get(v_opt_764_, 0);
v_defValue_766_ = lean_ctor_get(v_opt_764_, 1);
v_map_767_ = lean_ctor_get(v_opts_763_, 0);
v___x_768_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_767_, v_name_765_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_inc(v_defValue_766_);
return v_defValue_766_;
}
else
{
lean_object* v_val_769_; 
v_val_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_769_);
lean_dec_ref(v___x_768_);
if (lean_obj_tag(v_val_769_) == 3)
{
lean_object* v_v_770_; 
v_v_770_ = lean_ctor_get(v_val_769_, 0);
lean_inc(v_v_770_);
lean_dec_ref(v_val_769_);
return v_v_770_;
}
else
{
lean_dec(v_val_769_);
lean_inc(v_defValue_766_);
return v_defValue_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1___boxed(lean_object* v_opts_771_, lean_object* v_opt_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_771_, v_opt_772_);
lean_dec_ref(v_opt_772_);
lean_dec_ref(v_opts_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(lean_object* v_s_774_){
_start:
{
lean_object* v___x_776_; lean_object* v_putStr_777_; lean_object* v___x_778_; 
v___x_776_ = lean_get_stdout();
v_putStr_777_ = lean_ctor_get(v___x_776_, 4);
lean_inc_ref(v_putStr_777_);
lean_dec_ref(v___x_776_);
v___x_778_ = lean_apply_2(v_putStr_777_, v_s_774_, lean_box(0));
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2___boxed(lean_object* v_s_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v_s_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object* v_s_782_){
_start:
{
uint32_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = 10;
v___x_785_ = lean_string_push(v_s_782_, v___x_784_);
v___x_786_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3___boxed(lean_object* v_s_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v_s_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(lean_object* v_opts_792_, uint8_t v_json_793_, uint8_t v_includeEndPos_794_, lean_object* v_severityOverrides_795_, lean_object* v_as_796_, size_t v_i_797_, size_t v_stop_798_, lean_object* v_b_799_){
_start:
{
lean_object* v_a_802_; lean_object* v___y_807_; uint8_t v___y_808_; lean_object* v___y_820_; uint8_t v___y_821_; lean_object* v___y_822_; uint8_t v_isSilent_823_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; uint8_t v___y_849_; uint8_t v___x_873_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_884_; uint8_t v_severity_885_; 
v___x_873_ = lean_usize_dec_eq(v_i_797_, v_stop_798_);
if (v___x_873_ == 0)
{
lean_object* v___x_888_; lean_object* v_fileName_889_; lean_object* v_pos_890_; lean_object* v_endPos_891_; uint8_t v_keepFullRange_892_; uint8_t v_isSilent_893_; lean_object* v_caption_894_; lean_object* v_data_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_888_ = lean_array_uget(v_as_796_, v_i_797_);
v_fileName_889_ = lean_ctor_get(v___x_888_, 0);
v_pos_890_ = lean_ctor_get(v___x_888_, 1);
v_endPos_891_ = lean_ctor_get(v___x_888_, 2);
v_keepFullRange_892_ = lean_ctor_get_uint8(v___x_888_, sizeof(void*)*5);
v_isSilent_893_ = lean_ctor_get_uint8(v___x_888_, sizeof(void*)*5 + 2);
v_caption_894_ = lean_ctor_get(v___x_888_, 3);
v_data_895_ = lean_ctor_get(v___x_888_, 4);
v___x_896_ = l_Lean_MessageData_kind(v_data_895_);
v___x_897_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_severityOverrides_795_, v___x_896_);
lean_dec(v___x_896_);
if (lean_obj_tag(v___x_897_) == 1)
{
lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_907_; 
lean_inc(v_data_895_);
lean_inc_ref(v_caption_894_);
lean_inc(v_endPos_891_);
lean_inc_ref(v_pos_890_);
lean_inc_ref(v_fileName_889_);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; lean_object* v_unused_910_; lean_object* v_unused_911_; lean_object* v_unused_912_; 
v_unused_908_ = lean_ctor_get(v___x_888_, 4);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v___x_888_, 3);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v___x_888_, 2);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v___x_888_, 1);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v___x_888_, 0);
lean_dec(v_unused_912_);
v___x_899_ = v___x_888_;
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
else
{
lean_dec(v___x_888_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_val_901_; lean_object* v___x_903_; 
v_val_901_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_val_901_);
lean_dec_ref(v___x_897_);
if (v_isShared_900_ == 0)
{
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_fileName_889_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_pos_890_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_endPos_891_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_caption_894_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_data_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*5, v_keepFullRange_892_);
v___x_903_ = v_reuseFailAlloc_906_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
uint8_t v___x_904_; uint8_t v___x_905_; 
v___x_904_ = lean_unbox(v_val_901_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*5 + 1, v___x_904_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*5 + 2, v_isSilent_893_);
v___x_905_ = lean_unbox(v_val_901_);
lean_dec(v_val_901_);
v___y_884_ = v___x_903_;
v_severity_885_ = v___x_905_;
goto v___jp_883_;
}
}
}
else
{
uint8_t v_severity_913_; 
lean_dec(v___x_897_);
v_severity_913_ = lean_ctor_get_uint8(v___x_888_, sizeof(void*)*5 + 1);
v___y_884_ = v___x_888_;
v_severity_885_ = v_severity_913_;
goto v___jp_883_;
}
}
else
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v_b_799_);
return v___x_914_;
}
v___jp_801_:
{
size_t v___x_803_; size_t v___x_804_; 
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_add(v_i_797_, v___x_803_);
v_i_797_ = v___x_804_;
v_b_799_ = v_a_802_;
goto _start;
}
v___jp_806_:
{
if (v___y_808_ == 0)
{
v_a_802_ = v___y_807_;
goto v___jp_801_;
}
else
{
uint8_t v___x_809_; lean_object* v___x_810_; 
v___x_809_ = 1;
v___x_810_ = lean_io_exit(v___x_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_dec_ref(v___x_810_);
v_a_802_ = v___y_807_;
goto v___jp_801_;
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v___y_807_);
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
v___jp_819_:
{
if (v_isSilent_823_ == 0)
{
if (v_json_793_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = l_Lean_Message_toString(v___y_822_, v_includeEndPos_794_);
v___x_825_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_824_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_dec_ref(v___x_825_);
v___y_807_ = v___y_820_;
v___y_808_ = v___y_821_;
goto v___jp_806_;
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v___y_820_);
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = l_Lean_Message_toJson(v___y_822_);
v___x_835_ = l_Lean_Json_compress(v___x_834_);
v___x_836_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_dec_ref(v___x_836_);
v___y_807_ = v___y_820_;
v___y_808_ = v___y_821_;
goto v___jp_806_;
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v___y_820_);
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_822_);
v___y_807_ = v___y_820_;
v___y_808_ = v___y_821_;
goto v___jp_806_;
}
}
v___jp_845_:
{
if (v___y_849_ == 0)
{
uint8_t v_isSilent_850_; 
lean_dec(v___y_846_);
v_isSilent_850_ = lean_ctor_get_uint8(v___y_848_, sizeof(void*)*5 + 2);
v___y_820_ = v___y_847_;
v___y_821_ = v___y_849_;
v___y_822_ = v___y_848_;
v_isSilent_823_ = v_isSilent_850_;
goto v___jp_819_;
}
else
{
lean_object* v_fileName_851_; lean_object* v_pos_852_; lean_object* v_endPos_853_; uint8_t v_keepFullRange_854_; uint8_t v_isSilent_855_; lean_object* v_caption_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_871_; 
v_fileName_851_ = lean_ctor_get(v___y_848_, 0);
v_pos_852_ = lean_ctor_get(v___y_848_, 1);
v_endPos_853_ = lean_ctor_get(v___y_848_, 2);
v_keepFullRange_854_ = lean_ctor_get_uint8(v___y_848_, sizeof(void*)*5);
v_isSilent_855_ = lean_ctor_get_uint8(v___y_848_, sizeof(void*)*5 + 2);
v_caption_856_ = lean_ctor_get(v___y_848_, 3);
v_isSharedCheck_871_ = !lean_is_exclusive(v___y_848_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___y_848_, 4);
lean_dec(v_unused_872_);
v___x_858_ = v___y_848_;
v_isShared_859_ = v_isSharedCheck_871_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_caption_856_);
lean_inc(v_endPos_853_);
lean_inc(v_pos_852_);
lean_inc(v_fileName_851_);
lean_dec(v___y_848_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_871_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_860_ = 2;
v___x_861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0));
v___x_862_ = l_Nat_reprFast(v___y_846_);
v___x_863_ = lean_string_append(v___x_861_, v___x_862_);
lean_dec_ref(v___x_862_);
v___x_864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1));
v___x_865_ = lean_string_append(v___x_863_, v___x_864_);
v___x_866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
v___x_867_ = l_Lean_MessageData_ofFormat(v___x_866_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 4, v___x_867_);
v___x_869_ = v___x_858_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_fileName_851_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_pos_852_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_endPos_853_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_caption_856_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v___x_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_870_, sizeof(void*)*5, v_keepFullRange_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_870_, sizeof(void*)*5 + 2, v_isSilent_855_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*5 + 1, v___x_860_);
v___y_820_ = v___y_847_;
v___y_821_ = v___y_849_;
v___y_822_ = v___x_869_;
v_isSilent_823_ = v_isSilent_855_;
goto v___jp_819_;
}
}
}
}
v___jp_874_:
{
lean_object* v_numErrors_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v_numErrors_877_ = lean_nat_add(v_b_799_, v___y_876_);
lean_dec(v_b_799_);
v___x_878_ = l_Lean_Language_maxErrors;
v___x_879_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_792_, v___x_878_);
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_nat_dec_eq(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
uint8_t v___x_882_; 
v___x_882_ = lean_nat_dec_lt(v___x_879_, v_numErrors_877_);
if (v___x_882_ == 0)
{
v___y_846_ = v___x_879_;
v___y_847_ = v_numErrors_877_;
v___y_848_ = v___y_875_;
v___y_849_ = v___x_873_;
goto v___jp_845_;
}
else
{
v___y_846_ = v___x_879_;
v___y_847_ = v_numErrors_877_;
v___y_848_ = v___y_875_;
v___y_849_ = v___x_882_;
goto v___jp_845_;
}
}
else
{
v___y_846_ = v___x_879_;
v___y_847_ = v_numErrors_877_;
v___y_848_ = v___y_875_;
v___y_849_ = v___x_873_;
goto v___jp_845_;
}
}
v___jp_883_:
{
if (v_severity_885_ == 2)
{
lean_object* v___x_886_; 
v___x_886_ = lean_unsigned_to_nat(1u);
v___y_875_ = v___y_884_;
v___y_876_ = v___x_886_;
goto v___jp_874_;
}
else
{
lean_object* v___x_887_; 
v___x_887_ = lean_unsigned_to_nat(0u);
v___y_875_ = v___y_884_;
v___y_876_ = v___x_887_;
goto v___jp_874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___boxed(lean_object* v_opts_915_, lean_object* v_json_916_, lean_object* v_includeEndPos_917_, lean_object* v_severityOverrides_918_, lean_object* v_as_919_, lean_object* v_i_920_, lean_object* v_stop_921_, lean_object* v_b_922_, lean_object* v___y_923_){
_start:
{
uint8_t v_json_boxed_924_; uint8_t v_includeEndPos_boxed_925_; size_t v_i_boxed_926_; size_t v_stop_boxed_927_; lean_object* v_res_928_; 
v_json_boxed_924_ = lean_unbox(v_json_916_);
v_includeEndPos_boxed_925_ = lean_unbox(v_includeEndPos_917_);
v_i_boxed_926_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_stop_boxed_927_ = lean_unbox_usize(v_stop_921_);
lean_dec(v_stop_921_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_915_, v_json_boxed_924_, v_includeEndPos_boxed_925_, v_severityOverrides_918_, v_as_919_, v_i_boxed_926_, v_stop_boxed_927_, v_b_922_);
lean_dec_ref(v_as_919_);
lean_dec(v_severityOverrides_918_);
lean_dec_ref(v_opts_915_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(lean_object* v_opts_929_, uint8_t v_json_930_, uint8_t v_includeEndPos_931_, lean_object* v_severityOverrides_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
if (lean_obj_tag(v_x_933_) == 0)
{
lean_object* v_cs_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_956_; 
v_cs_936_ = lean_ctor_get(v_x_933_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_x_933_);
if (v_isSharedCheck_956_ == 0)
{
v___x_938_ = v_x_933_;
v_isShared_939_ = v_isSharedCheck_956_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_cs_936_);
lean_dec(v_x_933_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_956_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_array_get_size(v_cs_936_);
v___x_942_ = lean_nat_dec_lt(v___x_940_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_944_; 
lean_dec_ref(v_cs_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v_x_934_);
v___x_944_ = v___x_938_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_x_934_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
else
{
uint8_t v___x_946_; 
v___x_946_ = lean_nat_dec_le(v___x_941_, v___x_941_);
if (v___x_946_ == 0)
{
if (v___x_942_ == 0)
{
lean_object* v___x_948_; 
lean_dec_ref(v_cs_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v_x_934_);
v___x_948_ = v___x_938_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_x_934_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
else
{
size_t v___x_950_; size_t v___x_951_; lean_object* v___x_952_; 
lean_del_object(v___x_938_);
v___x_950_ = ((size_t)0ULL);
v___x_951_ = lean_usize_of_nat(v___x_941_);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_929_, v_json_930_, v_includeEndPos_931_, v_severityOverrides_932_, v_cs_936_, v___x_950_, v___x_951_, v_x_934_);
lean_dec_ref(v_cs_936_);
return v___x_952_;
}
}
else
{
size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
lean_del_object(v___x_938_);
v___x_953_ = ((size_t)0ULL);
v___x_954_ = lean_usize_of_nat(v___x_941_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_929_, v_json_930_, v_includeEndPos_931_, v_severityOverrides_932_, v_cs_936_, v___x_953_, v___x_954_, v_x_934_);
lean_dec_ref(v_cs_936_);
return v___x_955_;
}
}
}
}
else
{
lean_object* v_vs_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_977_; 
v_vs_957_ = lean_ctor_get(v_x_933_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v_x_933_);
if (v_isSharedCheck_977_ == 0)
{
v___x_959_ = v_x_933_;
v_isShared_960_ = v_isSharedCheck_977_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_vs_957_);
lean_dec(v_x_933_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_977_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = lean_array_get_size(v_vs_957_);
v___x_963_ = lean_nat_dec_lt(v___x_961_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_965_; 
lean_dec_ref(v_vs_957_);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 0);
lean_ctor_set(v___x_959_, 0, v_x_934_);
v___x_965_ = v___x_959_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_x_934_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
uint8_t v___x_967_; 
v___x_967_ = lean_nat_dec_le(v___x_962_, v___x_962_);
if (v___x_967_ == 0)
{
if (v___x_963_ == 0)
{
lean_object* v___x_969_; 
lean_dec_ref(v_vs_957_);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 0);
lean_ctor_set(v___x_959_, 0, v_x_934_);
v___x_969_ = v___x_959_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_x_934_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
else
{
size_t v___x_971_; size_t v___x_972_; lean_object* v___x_973_; 
lean_del_object(v___x_959_);
v___x_971_ = ((size_t)0ULL);
v___x_972_ = lean_usize_of_nat(v___x_962_);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_929_, v_json_930_, v_includeEndPos_931_, v_severityOverrides_932_, v_vs_957_, v___x_971_, v___x_972_, v_x_934_);
lean_dec_ref(v_vs_957_);
return v___x_973_;
}
}
else
{
size_t v___x_974_; size_t v___x_975_; lean_object* v___x_976_; 
lean_del_object(v___x_959_);
v___x_974_ = ((size_t)0ULL);
v___x_975_ = lean_usize_of_nat(v___x_962_);
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_929_, v_json_930_, v_includeEndPos_931_, v_severityOverrides_932_, v_vs_957_, v___x_974_, v___x_975_, v_x_934_);
lean_dec_ref(v_vs_957_);
return v___x_976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(lean_object* v_opts_978_, uint8_t v_json_979_, uint8_t v_includeEndPos_980_, lean_object* v_severityOverrides_981_, lean_object* v_as_982_, size_t v_i_983_, size_t v_stop_984_, lean_object* v_b_985_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = lean_usize_dec_eq(v_i_983_, v_stop_984_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_array_uget_borrowed(v_as_982_, v_i_983_);
lean_inc(v___x_988_);
v___x_989_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_978_, v_json_979_, v_includeEndPos_980_, v_severityOverrides_981_, v___x_988_, v_b_985_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; size_t v___x_991_; size_t v___x_992_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref(v___x_989_);
v___x_991_ = ((size_t)1ULL);
v___x_992_ = lean_usize_add(v_i_983_, v___x_991_);
v_i_983_ = v___x_992_;
v_b_985_ = v_a_990_;
goto _start;
}
else
{
return v___x_989_;
}
}
else
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v_b_985_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5___boxed(lean_object* v_opts_995_, lean_object* v_json_996_, lean_object* v_includeEndPos_997_, lean_object* v_severityOverrides_998_, lean_object* v_as_999_, lean_object* v_i_1000_, lean_object* v_stop_1001_, lean_object* v_b_1002_, lean_object* v___y_1003_){
_start:
{
uint8_t v_json_boxed_1004_; uint8_t v_includeEndPos_boxed_1005_; size_t v_i_boxed_1006_; size_t v_stop_boxed_1007_; lean_object* v_res_1008_; 
v_json_boxed_1004_ = lean_unbox(v_json_996_);
v_includeEndPos_boxed_1005_ = lean_unbox(v_includeEndPos_997_);
v_i_boxed_1006_ = lean_unbox_usize(v_i_1000_);
lean_dec(v_i_1000_);
v_stop_boxed_1007_ = lean_unbox_usize(v_stop_1001_);
lean_dec(v_stop_1001_);
v_res_1008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_995_, v_json_boxed_1004_, v_includeEndPos_boxed_1005_, v_severityOverrides_998_, v_as_999_, v_i_boxed_1006_, v_stop_boxed_1007_, v_b_1002_);
lean_dec_ref(v_as_999_);
lean_dec(v_severityOverrides_998_);
lean_dec_ref(v_opts_995_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6___boxed(lean_object* v_opts_1009_, lean_object* v_json_1010_, lean_object* v_includeEndPos_1011_, lean_object* v_severityOverrides_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v_json_boxed_1016_; uint8_t v_includeEndPos_boxed_1017_; lean_object* v_res_1018_; 
v_json_boxed_1016_ = lean_unbox(v_json_1010_);
v_includeEndPos_boxed_1017_ = lean_unbox(v_includeEndPos_1011_);
v_res_1018_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1009_, v_json_boxed_1016_, v_includeEndPos_boxed_1017_, v_severityOverrides_1012_, v_x_1013_, v_x_1014_);
lean_dec(v_severityOverrides_1012_);
lean_dec_ref(v_opts_1009_);
return v_res_1018_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(lean_object* v_opts_1020_, uint8_t v_json_1021_, uint8_t v_includeEndPos_1022_, lean_object* v_severityOverrides_1023_, lean_object* v_x_1024_, size_t v_x_1025_, size_t v_x_1026_, lean_object* v_x_1027_){
_start:
{
if (lean_obj_tag(v_x_1024_) == 0)
{
lean_object* v_cs_1029_; lean_object* v___x_1030_; size_t v___x_1031_; lean_object* v_j_1032_; lean_object* v___x_1033_; size_t v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
v_cs_1029_ = lean_ctor_get(v_x_1024_, 0);
lean_inc_ref(v_cs_1029_);
lean_dec_ref(v_x_1024_);
v___x_1030_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0);
v___x_1031_ = lean_usize_shift_right(v_x_1025_, v_x_1026_);
v_j_1032_ = lean_usize_to_nat(v___x_1031_);
v___x_1033_ = lean_array_get_borrowed(v___x_1030_, v_cs_1029_, v_j_1032_);
v___x_1034_ = ((size_t)1ULL);
v___x_1035_ = lean_usize_shift_left(v___x_1034_, v_x_1026_);
v___x_1036_ = lean_usize_sub(v___x_1035_, v___x_1034_);
v___x_1037_ = lean_usize_land(v_x_1025_, v___x_1036_);
v___x_1038_ = ((size_t)5ULL);
v___x_1039_ = lean_usize_sub(v_x_1026_, v___x_1038_);
lean_inc(v___x_1033_);
v___x_1040_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1020_, v_json_1021_, v_includeEndPos_1022_, v_severityOverrides_1023_, v___x_1033_, v___x_1037_, v___x_1039_, v_x_1027_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = lean_nat_add(v_j_1032_, v___x_1042_);
lean_dec(v_j_1032_);
v___x_1044_ = lean_array_get_size(v_cs_1029_);
v___x_1045_ = lean_nat_dec_lt(v___x_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_dec(v___x_1043_);
lean_dec(v_a_1041_);
lean_dec_ref(v_cs_1029_);
return v___x_1040_;
}
else
{
uint8_t v___x_1046_; 
v___x_1046_ = lean_nat_dec_le(v___x_1044_, v___x_1044_);
if (v___x_1046_ == 0)
{
if (v___x_1045_ == 0)
{
lean_dec(v___x_1043_);
lean_dec(v_a_1041_);
lean_dec_ref(v_cs_1029_);
return v___x_1040_;
}
else
{
size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref(v___x_1040_);
v___x_1047_ = lean_usize_of_nat(v___x_1043_);
lean_dec(v___x_1043_);
v___x_1048_ = lean_usize_of_nat(v___x_1044_);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1020_, v_json_1021_, v_includeEndPos_1022_, v_severityOverrides_1023_, v_cs_1029_, v___x_1047_, v___x_1048_, v_a_1041_);
lean_dec_ref(v_cs_1029_);
return v___x_1049_;
}
}
else
{
size_t v___x_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
lean_dec_ref(v___x_1040_);
v___x_1050_ = lean_usize_of_nat(v___x_1043_);
lean_dec(v___x_1043_);
v___x_1051_ = lean_usize_of_nat(v___x_1044_);
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1020_, v_json_1021_, v_includeEndPos_1022_, v_severityOverrides_1023_, v_cs_1029_, v___x_1050_, v___x_1051_, v_a_1041_);
lean_dec_ref(v_cs_1029_);
return v___x_1052_;
}
}
}
else
{
lean_dec(v_j_1032_);
lean_dec_ref(v_cs_1029_);
return v___x_1040_;
}
}
else
{
lean_object* v_vs_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1073_; 
v_vs_1053_ = lean_ctor_get(v_x_1024_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1055_ = v_x_1024_;
v_isShared_1056_ = v_isSharedCheck_1073_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_vs_1053_);
lean_dec(v_x_1024_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1073_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1057_ = lean_usize_to_nat(v_x_1025_);
v___x_1058_ = lean_array_get_size(v_vs_1053_);
v___x_1059_ = lean_nat_dec_lt(v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1061_; 
lean_dec(v___x_1057_);
lean_dec_ref(v_vs_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 0);
lean_ctor_set(v___x_1055_, 0, v_x_1027_);
v___x_1061_ = v___x_1055_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_x_1027_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_nat_dec_le(v___x_1058_, v___x_1058_);
if (v___x_1063_ == 0)
{
if (v___x_1059_ == 0)
{
lean_object* v___x_1065_; 
lean_dec(v___x_1057_);
lean_dec_ref(v_vs_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 0);
lean_ctor_set(v___x_1055_, 0, v_x_1027_);
v___x_1065_ = v___x_1055_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_x_1027_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
else
{
size_t v___x_1067_; size_t v___x_1068_; lean_object* v___x_1069_; 
lean_del_object(v___x_1055_);
v___x_1067_ = lean_usize_of_nat(v___x_1057_);
lean_dec(v___x_1057_);
v___x_1068_ = lean_usize_of_nat(v___x_1058_);
v___x_1069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1020_, v_json_1021_, v_includeEndPos_1022_, v_severityOverrides_1023_, v_vs_1053_, v___x_1067_, v___x_1068_, v_x_1027_);
lean_dec_ref(v_vs_1053_);
return v___x_1069_;
}
}
else
{
size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
lean_del_object(v___x_1055_);
v___x_1070_ = lean_usize_of_nat(v___x_1057_);
lean_dec(v___x_1057_);
v___x_1071_ = lean_usize_of_nat(v___x_1058_);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1020_, v_json_1021_, v_includeEndPos_1022_, v_severityOverrides_1023_, v_vs_1053_, v___x_1070_, v___x_1071_, v_x_1027_);
lean_dec_ref(v_vs_1053_);
return v___x_1072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___boxed(lean_object* v_opts_1074_, lean_object* v_json_1075_, lean_object* v_includeEndPos_1076_, lean_object* v_severityOverrides_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v___y_1082_){
_start:
{
uint8_t v_json_boxed_1083_; uint8_t v_includeEndPos_boxed_1084_; size_t v_x_2643__boxed_1085_; size_t v_x_2644__boxed_1086_; lean_object* v_res_1087_; 
v_json_boxed_1083_ = lean_unbox(v_json_1075_);
v_includeEndPos_boxed_1084_ = lean_unbox(v_includeEndPos_1076_);
v_x_2643__boxed_1085_ = lean_unbox_usize(v_x_1079_);
lean_dec(v_x_1079_);
v_x_2644__boxed_1086_ = lean_unbox_usize(v_x_1080_);
lean_dec(v_x_1080_);
v_res_1087_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1074_, v_json_boxed_1083_, v_includeEndPos_boxed_1084_, v_severityOverrides_1077_, v_x_1078_, v_x_2643__boxed_1085_, v_x_2644__boxed_1086_, v_x_1081_);
lean_dec(v_severityOverrides_1077_);
lean_dec_ref(v_opts_1074_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(lean_object* v_opts_1088_, uint8_t v_json_1089_, uint8_t v_includeEndPos_1090_, lean_object* v_severityOverrides_1091_, lean_object* v_t_1092_, lean_object* v_init_1093_, lean_object* v_start_1094_){
_start:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = lean_nat_dec_eq(v_start_1094_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v_root_1098_; lean_object* v_tail_1099_; size_t v_shift_1100_; lean_object* v_tailOff_1101_; uint8_t v___x_1102_; 
v_root_1098_ = lean_ctor_get(v_t_1092_, 0);
lean_inc_ref(v_root_1098_);
v_tail_1099_ = lean_ctor_get(v_t_1092_, 1);
lean_inc_ref(v_tail_1099_);
v_shift_1100_ = lean_ctor_get_usize(v_t_1092_, 4);
v_tailOff_1101_ = lean_ctor_get(v_t_1092_, 3);
lean_inc(v_tailOff_1101_);
lean_dec_ref(v_t_1092_);
v___x_1102_ = lean_nat_dec_le(v_tailOff_1101_, v_start_1094_);
if (v___x_1102_ == 0)
{
size_t v___x_1103_; lean_object* v___x_1104_; 
lean_dec(v_tailOff_1101_);
v___x_1103_ = lean_usize_of_nat(v_start_1094_);
v___x_1104_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1088_, v_json_1089_, v_includeEndPos_1090_, v_severityOverrides_1091_, v_root_1098_, v___x_1103_, v_shift_1100_, v_init_1093_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
v___x_1106_ = lean_array_get_size(v_tail_1099_);
v___x_1107_ = lean_nat_dec_lt(v___x_1096_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_dec(v_a_1105_);
lean_dec_ref(v_tail_1099_);
return v___x_1104_;
}
else
{
uint8_t v___x_1108_; 
v___x_1108_ = lean_nat_dec_le(v___x_1106_, v___x_1106_);
if (v___x_1108_ == 0)
{
if (v___x_1107_ == 0)
{
lean_dec(v_a_1105_);
lean_dec_ref(v_tail_1099_);
return v___x_1104_;
}
else
{
size_t v___x_1109_; size_t v___x_1110_; lean_object* v___x_1111_; 
lean_dec_ref(v___x_1104_);
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = lean_usize_of_nat(v___x_1106_);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1088_, v_json_1089_, v_includeEndPos_1090_, v_severityOverrides_1091_, v_tail_1099_, v___x_1109_, v___x_1110_, v_a_1105_);
lean_dec_ref(v_tail_1099_);
return v___x_1111_;
}
}
else
{
size_t v___x_1112_; size_t v___x_1113_; lean_object* v___x_1114_; 
lean_dec_ref(v___x_1104_);
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = lean_usize_of_nat(v___x_1106_);
v___x_1114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1088_, v_json_1089_, v_includeEndPos_1090_, v_severityOverrides_1091_, v_tail_1099_, v___x_1112_, v___x_1113_, v_a_1105_);
lean_dec_ref(v_tail_1099_);
return v___x_1114_;
}
}
}
else
{
lean_dec_ref(v_tail_1099_);
return v___x_1104_;
}
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
lean_dec_ref(v_root_1098_);
v___x_1115_ = lean_nat_sub(v_start_1094_, v_tailOff_1101_);
lean_dec(v_tailOff_1101_);
v___x_1116_ = lean_array_get_size(v_tail_1099_);
v___x_1117_ = lean_nat_dec_lt(v___x_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_dec(v___x_1115_);
lean_dec_ref(v_tail_1099_);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_init_1093_);
return v___x_1118_;
}
else
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_nat_dec_le(v___x_1116_, v___x_1116_);
if (v___x_1119_ == 0)
{
if (v___x_1117_ == 0)
{
lean_object* v___x_1120_; 
lean_dec(v___x_1115_);
lean_dec_ref(v_tail_1099_);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_init_1093_);
return v___x_1120_;
}
else
{
size_t v___x_1121_; size_t v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_usize_of_nat(v___x_1115_);
lean_dec(v___x_1115_);
v___x_1122_ = lean_usize_of_nat(v___x_1116_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1088_, v_json_1089_, v_includeEndPos_1090_, v_severityOverrides_1091_, v_tail_1099_, v___x_1121_, v___x_1122_, v_init_1093_);
lean_dec_ref(v_tail_1099_);
return v___x_1123_;
}
}
else
{
size_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = lean_usize_of_nat(v___x_1115_);
lean_dec(v___x_1115_);
v___x_1125_ = lean_usize_of_nat(v___x_1116_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1088_, v_json_1089_, v_includeEndPos_1090_, v_severityOverrides_1091_, v_tail_1099_, v___x_1124_, v___x_1125_, v_init_1093_);
lean_dec_ref(v_tail_1099_);
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_root_1127_; lean_object* v_tail_1128_; lean_object* v___x_1129_; 
v_root_1127_ = lean_ctor_get(v_t_1092_, 0);
lean_inc_ref(v_root_1127_);
v_tail_1128_ = lean_ctor_get(v_t_1092_, 1);
lean_inc_ref(v_tail_1128_);
lean_dec_ref(v_t_1092_);
v___x_1129_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1088_, v_json_1089_, v_includeEndPos_1090_, v_severityOverrides_1091_, v_root_1127_, v_init_1093_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
v___x_1131_ = lean_array_get_size(v_tail_1128_);
v___x_1132_ = lean_nat_dec_lt(v___x_1096_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_dec(v_a_1130_);
lean_dec_ref(v_tail_1128_);
return v___x_1129_;
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_nat_dec_le(v___x_1131_, v___x_1131_);
if (v___x_1133_ == 0)
{
if (v___x_1132_ == 0)
{
lean_dec(v_a_1130_);
lean_dec_ref(v_tail_1128_);
return v___x_1129_;
}
else
{
size_t v___x_1134_; size_t v___x_1135_; lean_object* v___x_1136_; 
lean_dec_ref(v___x_1129_);
v___x_1134_ = ((size_t)0ULL);
v___x_1135_ = lean_usize_of_nat(v___x_1131_);
v___x_1136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1088_, v_json_1089_, v_includeEndPos_1090_, v_severityOverrides_1091_, v_tail_1128_, v___x_1134_, v___x_1135_, v_a_1130_);
lean_dec_ref(v_tail_1128_);
return v___x_1136_;
}
}
else
{
size_t v___x_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
lean_dec_ref(v___x_1129_);
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = lean_usize_of_nat(v___x_1131_);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1088_, v_json_1089_, v_includeEndPos_1090_, v_severityOverrides_1091_, v_tail_1128_, v___x_1137_, v___x_1138_, v_a_1130_);
lean_dec_ref(v_tail_1128_);
return v___x_1139_;
}
}
}
else
{
lean_dec_ref(v_tail_1128_);
return v___x_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4___boxed(lean_object* v_opts_1140_, lean_object* v_json_1141_, lean_object* v_includeEndPos_1142_, lean_object* v_severityOverrides_1143_, lean_object* v_t_1144_, lean_object* v_init_1145_, lean_object* v_start_1146_, lean_object* v___y_1147_){
_start:
{
uint8_t v_json_boxed_1148_; uint8_t v_includeEndPos_boxed_1149_; lean_object* v_res_1150_; 
v_json_boxed_1148_ = lean_unbox(v_json_1141_);
v_includeEndPos_boxed_1149_ = lean_unbox(v_includeEndPos_1142_);
v_res_1150_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1140_, v_json_boxed_1148_, v_includeEndPos_boxed_1149_, v_severityOverrides_1143_, v_t_1144_, v_init_1145_, v_start_1146_);
lean_dec(v_start_1146_);
lean_dec(v_severityOverrides_1143_);
lean_dec_ref(v_opts_1140_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(lean_object* v_msgLog_1151_, lean_object* v_opts_1152_, uint8_t v_json_1153_, lean_object* v_severityOverrides_1154_, lean_object* v_numErrors_1155_){
_start:
{
lean_object* v_unreported_1157_; lean_object* v___x_1158_; uint8_t v_includeEndPos_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_unreported_1157_ = lean_ctor_get(v_msgLog_1151_, 1);
lean_inc_ref(v_unreported_1157_);
lean_dec_ref(v_msgLog_1151_);
v___x_1158_ = l_Lean_Language_printMessageEndPos;
v_includeEndPos_1159_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_1152_, v___x_1158_);
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1152_, v_json_1153_, v_includeEndPos_1159_, v_severityOverrides_1154_, v_unreported_1157_, v_numErrors_1155_, v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___boxed(lean_object* v_msgLog_1162_, lean_object* v_opts_1163_, lean_object* v_json_1164_, lean_object* v_severityOverrides_1165_, lean_object* v_numErrors_1166_, lean_object* v_a_1167_){
_start:
{
uint8_t v_json_boxed_1168_; lean_object* v_res_1169_; 
v_json_boxed_1168_ = lean_unbox(v_json_1164_);
v_res_1169_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1162_, v_opts_1163_, v_json_boxed_1168_, v_severityOverrides_1165_, v_numErrors_1166_);
lean_dec(v_severityOverrides_1165_);
lean_dec_ref(v_opts_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object* v_opts_1170_, uint8_t v_json_1171_, lean_object* v_severityOverrides_1172_, lean_object* v_s_1173_, lean_object* v_init_1174_){
_start:
{
lean_object* v_element_1176_; lean_object* v_diagnostics_1177_; lean_object* v_children_1178_; lean_object* v_msgLog_1179_; lean_object* v___x_1180_; 
v_element_1176_ = lean_ctor_get(v_s_1173_, 0);
v_diagnostics_1177_ = lean_ctor_get(v_element_1176_, 1);
lean_inc_ref(v_diagnostics_1177_);
v_children_1178_ = lean_ctor_get(v_s_1173_, 1);
lean_inc_ref(v_children_1178_);
lean_dec_ref(v_s_1173_);
v_msgLog_1179_ = lean_ctor_get(v_diagnostics_1177_, 0);
lean_inc_ref(v_msgLog_1179_);
lean_dec_ref(v_diagnostics_1177_);
v___x_1180_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1179_, v_opts_1170_, v_json_1171_, v_severityOverrides_1172_, v_init_1174_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = lean_array_get_size(v_children_1178_);
v___x_1184_ = lean_nat_dec_lt(v___x_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_dec(v_a_1181_);
lean_dec_ref(v_children_1178_);
return v___x_1180_;
}
else
{
uint8_t v___x_1185_; 
v___x_1185_ = lean_nat_dec_le(v___x_1183_, v___x_1183_);
if (v___x_1185_ == 0)
{
if (v___x_1184_ == 0)
{
lean_dec(v_a_1181_);
lean_dec_ref(v_children_1178_);
return v___x_1180_;
}
else
{
size_t v___x_1186_; size_t v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref(v___x_1180_);
v___x_1186_ = ((size_t)0ULL);
v___x_1187_ = lean_usize_of_nat(v___x_1183_);
v___x_1188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1170_, v_json_1171_, v_severityOverrides_1172_, v_children_1178_, v___x_1186_, v___x_1187_, v_a_1181_);
lean_dec_ref(v_children_1178_);
return v___x_1188_;
}
}
else
{
size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v___x_1180_);
v___x_1189_ = ((size_t)0ULL);
v___x_1190_ = lean_usize_of_nat(v___x_1183_);
v___x_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1170_, v_json_1171_, v_severityOverrides_1172_, v_children_1178_, v___x_1189_, v___x_1190_, v_a_1181_);
lean_dec_ref(v_children_1178_);
return v___x_1191_;
}
}
}
else
{
lean_dec_ref(v_children_1178_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object* v_opts_1192_, uint8_t v_json_1193_, lean_object* v_severityOverrides_1194_, lean_object* v_as_1195_, size_t v_i_1196_, size_t v_stop_1197_, lean_object* v_b_1198_){
_start:
{
uint8_t v___x_1200_; 
v___x_1200_ = lean_usize_dec_eq(v_i_1196_, v_stop_1197_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_array_uget_borrowed(v_as_1195_, v_i_1196_);
lean_inc(v___x_1201_);
v___x_1202_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1201_);
v___x_1203_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1192_, v_json_1193_, v_severityOverrides_1194_, v___x_1202_, v_b_1198_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; size_t v___x_1205_; size_t v___x_1206_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref(v___x_1203_);
v___x_1205_ = ((size_t)1ULL);
v___x_1206_ = lean_usize_add(v_i_1196_, v___x_1205_);
v_i_1196_ = v___x_1206_;
v_b_1198_ = v_a_1204_;
goto _start;
}
else
{
return v___x_1203_;
}
}
else
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_b_1198_);
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object* v_opts_1209_, lean_object* v_json_1210_, lean_object* v_severityOverrides_1211_, lean_object* v_as_1212_, lean_object* v_i_1213_, lean_object* v_stop_1214_, lean_object* v_b_1215_, lean_object* v___y_1216_){
_start:
{
uint8_t v_json_boxed_1217_; size_t v_i_boxed_1218_; size_t v_stop_boxed_1219_; lean_object* v_res_1220_; 
v_json_boxed_1217_ = lean_unbox(v_json_1210_);
v_i_boxed_1218_ = lean_unbox_usize(v_i_1213_);
lean_dec(v_i_1213_);
v_stop_boxed_1219_ = lean_unbox_usize(v_stop_1214_);
lean_dec(v_stop_1214_);
v_res_1220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1209_, v_json_boxed_1217_, v_severityOverrides_1211_, v_as_1212_, v_i_boxed_1218_, v_stop_boxed_1219_, v_b_1215_);
lean_dec_ref(v_as_1212_);
lean_dec(v_severityOverrides_1211_);
lean_dec_ref(v_opts_1209_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object* v_opts_1221_, lean_object* v_json_1222_, lean_object* v_severityOverrides_1223_, lean_object* v_s_1224_, lean_object* v_init_1225_, lean_object* v___y_1226_){
_start:
{
uint8_t v_json_boxed_1227_; lean_object* v_res_1228_; 
v_json_boxed_1227_ = lean_unbox(v_json_1222_);
v_res_1228_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1221_, v_json_boxed_1227_, v_severityOverrides_1223_, v_s_1224_, v_init_1225_);
lean_dec(v_severityOverrides_1223_);
lean_dec_ref(v_opts_1221_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object* v_s_1229_, lean_object* v_opts_1230_, uint8_t v_json_1231_, lean_object* v_severityOverrides_1232_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1230_, v_json_1231_, v_severityOverrides_1232_, v_s_1229_, v___x_1234_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1245_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1245_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1245_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
uint8_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1240_ = lean_nat_dec_lt(v___x_1234_, v_a_1236_);
lean_dec(v_a_1236_);
v___x_1241_ = lean_box(v___x_1240_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1241_);
v___x_1243_ = v___x_1238_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
v_a_1246_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1235_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1235_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object* v_s_1254_, lean_object* v_opts_1255_, lean_object* v_json_1256_, lean_object* v_severityOverrides_1257_, lean_object* v_a_1258_){
_start:
{
uint8_t v_json_boxed_1259_; lean_object* v_res_1260_; 
v_json_boxed_1259_ = lean_unbox(v_json_1256_);
v_res_1260_ = l_Lean_Language_SnapshotTree_runAndReport(v_s_1254_, v_opts_1255_, v_json_boxed_1259_, v_severityOverrides_1257_);
lean_dec(v_severityOverrides_1257_);
lean_dec_ref(v_opts_1255_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(lean_object* v_s_1261_, lean_object* v_init_1262_){
_start:
{
lean_object* v_element_1263_; lean_object* v_children_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_element_1263_ = lean_ctor_get(v_s_1261_, 0);
lean_inc_ref(v_element_1263_);
v_children_1264_ = lean_ctor_get(v_s_1261_, 1);
lean_inc_ref(v_children_1264_);
lean_dec_ref(v_s_1261_);
v___x_1265_ = lean_array_push(v_init_1262_, v_element_1263_);
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = lean_array_get_size(v_children_1264_);
v___x_1268_ = lean_nat_dec_lt(v___x_1266_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_dec_ref(v_children_1264_);
return v___x_1265_;
}
else
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_nat_dec_le(v___x_1267_, v___x_1267_);
if (v___x_1269_ == 0)
{
if (v___x_1268_ == 0)
{
lean_dec_ref(v_children_1264_);
return v___x_1265_;
}
else
{
size_t v___x_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = ((size_t)0ULL);
v___x_1271_ = lean_usize_of_nat(v___x_1267_);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_1264_, v___x_1270_, v___x_1271_, v___x_1265_);
lean_dec_ref(v_children_1264_);
return v___x_1272_;
}
}
else
{
size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = lean_usize_of_nat(v___x_1267_);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_1264_, v___x_1273_, v___x_1274_, v___x_1265_);
lean_dec_ref(v_children_1264_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object* v_as_1276_, size_t v_i_1277_, size_t v_stop_1278_, lean_object* v_b_1279_){
_start:
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_usize_dec_eq(v_i_1277_, v_stop_1278_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; 
v___x_1281_ = lean_array_uget_borrowed(v_as_1276_, v_i_1277_);
lean_inc(v___x_1281_);
v___x_1282_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1281_);
v___x_1283_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v___x_1282_, v_b_1279_);
v___x_1284_ = ((size_t)1ULL);
v___x_1285_ = lean_usize_add(v_i_1277_, v___x_1284_);
v_i_1277_ = v___x_1285_;
v_b_1279_ = v___x_1283_;
goto _start;
}
else
{
return v_b_1279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object* v_as_1287_, lean_object* v_i_1288_, lean_object* v_stop_1289_, lean_object* v_b_1290_){
_start:
{
size_t v_i_boxed_1291_; size_t v_stop_boxed_1292_; lean_object* v_res_1293_; 
v_i_boxed_1291_ = lean_unbox_usize(v_i_1288_);
lean_dec(v_i_1288_);
v_stop_boxed_1292_ = lean_unbox_usize(v_stop_1289_);
lean_dec(v_stop_1289_);
v_res_1293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_as_1287_, v_i_boxed_1291_, v_stop_boxed_1292_, v_b_1290_);
lean_dec_ref(v_as_1287_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object* v_s_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lean_Language_SnapshotTree_getAll___closed__0));
v___x_1298_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v_s_1296_, v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_task_pure(v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed(lean_object* v_tail_1301_, lean_object* v_t_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(v_tail_1301_, v_t_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(lean_object* v_a_1305_){
_start:
{
if (lean_obj_tag(v_a_1305_) == 0)
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_obj_once(&l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0, &l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0_once, _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0);
return v___x_1307_;
}
else
{
lean_object* v_head_1308_; lean_object* v_tail_1309_; lean_object* v_task_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; 
v_head_1308_ = lean_ctor_get(v_a_1305_, 0);
lean_inc(v_head_1308_);
v_tail_1309_ = lean_ctor_get(v_a_1305_, 1);
lean_inc(v_tail_1309_);
lean_dec_ref(v_a_1305_);
v_task_1310_ = lean_ctor_get(v_head_1308_, 3);
lean_inc_ref(v_task_1310_);
lean_dec(v_head_1308_);
v___f_1311_ = lean_alloc_closure((void*)(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1311_, 0, v_tail_1309_);
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = 1;
v___x_1314_ = lean_io_bind_task(v_task_1310_, v___f_1311_, v___x_1312_, v___x_1313_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object* v_tail_1315_, lean_object* v_t_1316_){
_start:
{
lean_object* v_children_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_children_1318_ = lean_ctor_get(v_t_1316_, 1);
lean_inc_ref(v_children_1318_);
lean_dec_ref(v_t_1316_);
v___x_1319_ = lean_array_to_list(v_children_1318_);
v___x_1320_ = l_List_appendTR___redArg(v___x_1319_, v_tail_1315_);
v___x_1321_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___boxed(lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v_a_1322_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object* v_x_1325_){
_start:
{
lean_object* v_children_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_children_1327_ = lean_ctor_get(v_x_1325_, 1);
lean_inc_ref(v_children_1327_);
lean_dec_ref(v_x_1325_);
v___x_1328_ = lean_array_to_list(v_children_1327_);
v___x_1329_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll___boxed(lean_object* v_x_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Language_SnapshotTree_waitAll(v_x_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object* v_00_u03b1_1333_, lean_object* v_act_1334_, lean_object* v_ctx_1335_){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_apply_2(v_act_1334_, v_ctx_1335_, lean_box(0));
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_act_1340_, lean_object* v_ctx_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(v_00_u03b1_1339_, v_act_1340_, v_ctx_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object* v_msgLog_1346_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_st_mk_ref(v___x_1348_);
v___x_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_msgLog_1346_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog___boxed(lean_object* v_msgLog_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object* v_msg_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_fileMap_1362_; lean_object* v_source_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_fileMap_1362_ = lean_ctor_get(v_a_1360_, 2);
v_source_1363_ = lean_ctor_get(v_fileMap_1362_, 0);
v___x_1364_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__0));
v___x_1365_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__1));
v___x_1366_ = lean_string_utf8_byte_size(v_source_1363_);
lean_inc_ref(v_fileMap_1362_);
v___x_1367_ = l_Lean_FileMap_toPosition(v_fileMap_1362_, v___x_1366_);
v___x_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
v___x_1369_ = 0;
v___x_1370_ = 2;
v___x_1371_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot___closed__0));
v___x_1372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_msg_1359_);
v___x_1373_ = l_Lean_MessageData_ofFormat(v___x_1372_);
v___x_1374_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1374_, 0, v___x_1364_);
lean_ctor_set(v___x_1374_, 1, v___x_1365_);
lean_ctor_set(v___x_1374_, 2, v___x_1368_);
lean_ctor_set(v___x_1374_, 3, v___x_1371_);
lean_ctor_set(v___x_1374_, 4, v___x_1373_);
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*5, v___x_1369_);
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*5 + 1, v___x_1370_);
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*5 + 2, v___x_1369_);
v___x_1375_ = l_Lean_MessageLog_empty;
v___x_1376_ = l_Lean_MessageLog_add(v___x_1374_, v___x_1375_);
v___x_1377_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError___boxed(lean_object* v_msg_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Language_diagnosticsOfHeaderError(v_msg_1378_, v_a_1379_);
lean_dec_ref(v_a_1379_);
return v_res_1381_;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2(void){
_start:
{
uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = 1;
v___x_1388_ = ((lean_object*)(l_Lean_Language_withHeaderExceptions___redArg___closed__1));
v___x_1389_ = l_Lean_Name_toString(v___x_1388_, v___x_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object* v_ex_1390_, lean_object* v_act_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1394_; 
lean_inc_ref(v_a_1392_);
v___x_1394_ = lean_apply_2(v_act_1391_, v_a_1392_, lean_box(0));
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; 
lean_dec(v_ex_1390_);
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref(v___x_1394_);
return v_a_1395_;
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_a_1396_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1396_);
lean_dec_ref(v___x_1394_);
v___x_1397_ = lean_io_error_to_string(v_a_1396_);
v___x_1398_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_1397_, v_a_1392_);
v___x_1399_ = lean_obj_once(&l_Lean_Language_withHeaderExceptions___redArg___closed__2, &l_Lean_Language_withHeaderExceptions___redArg___closed__2_once, _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2);
v___x_1400_ = lean_box(0);
v___x_1401_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_1402_ = 0;
v___x_1403_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1403_, 0, v___x_1399_);
lean_ctor_set(v___x_1403_, 1, v___x_1398_);
lean_ctor_set(v___x_1403_, 2, v___x_1400_);
lean_ctor_set(v___x_1403_, 3, v___x_1401_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*4, v___x_1402_);
v___x_1404_ = lean_apply_1(v_ex_1390_, v___x_1403_);
return v___x_1404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg___boxed(lean_object* v_ex_1405_, lean_object* v_act_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1405_, v_act_1406_, v_a_1407_);
lean_dec_ref(v_a_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object* v_00_u03b1_1410_, lean_object* v_ex_1411_, lean_object* v_act_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1411_, v_act_1412_, v_a_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_ex_1417_, lean_object* v_act_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Language_withHeaderExceptions(v_00_u03b1_1416_, v_ex_1417_, v_act_1418_, v_a_1419_);
lean_dec_ref(v_a_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object* v_val_1422_, lean_object* v_process_1423_, lean_object* v_ictx_1424_){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = lean_st_ref_get(v_val_1422_);
v___x_1427_ = lean_apply_3(v_process_1423_, v___x_1426_, v_ictx_1424_, lean_box(0));
lean_inc(v___x_1427_);
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
v___x_1429_ = lean_st_ref_set(v_val_1422_, v___x_1428_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object* v_val_1430_, lean_object* v_process_1431_, lean_object* v_ictx_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(v_val_1430_, v_process_1431_, v_ictx_1432_);
lean_dec(v_val_1430_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object* v_process_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___f_1439_; 
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_st_mk_ref(v___x_1437_);
v___f_1439_ = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1439_, 0, v___x_1438_);
lean_closure_set(v___f_1439_, 1, v_process_1435_);
return v___f_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___boxed(lean_object* v_process_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object* v_InitSnap_1443_, lean_object* v_process_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___boxed(lean_object* v_InitSnap_1447_, lean_object* v_process_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Language_mkIncrementalProcessor(v_InitSnap_1447_, v_process_1448_);
return v_res_1450_;
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
l_Lean_Language_instInhabitedSnapshotLeaf = _init_l_Lean_Language_instInhabitedSnapshotLeaf();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotLeaf);
l_Lean_Language_instInhabitedDynamicSnapshot = _init_l_Lean_Language_instInhabitedDynamicSnapshot();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot);
res = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Language_printMessageEndPos = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Language_printMessageEndPos);
lean_dec_ref(res);
res = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
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
