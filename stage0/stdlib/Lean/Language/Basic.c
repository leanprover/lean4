// Lean compiler output
// Module: Lean.Language.Basic
// Imports: public import Lean.Parser.Types public import Lean.Util.Trace import Lean.Elab.InfoTree.Basic
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_addTrailing_x3f(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedMessageLog_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
extern lean_object* l_instMonadBaseIO;
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_IO_CancelToken_set(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_addTrailing(lean_object*, lean_object*);
lean_object* lean_io_exit(uint8_t);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
lean_object* l_Lean_Message_toJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Elab_InfoTree_addTrailing(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__28 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__28_value;
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__27_value),LEAN_SCALAR_PTR_LITERAL(47, 79, 177, 134, 210, 33, 7, 227)}};
static const lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__29 = (const lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__29_value;
static const lean_ctor_object l_Lean_Language_Snapshot_desc___autoParam___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__28_value),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Language"};
static const lean_object* l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30_ = (const lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value;
static const lean_string_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "SnapshotTree"};
static const lean_object* l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30_ = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value;
static const lean_ctor_object l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value_aux_1),((lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value),LEAN_SCALAR_PTR_LITERAL(233, 91, 117, 52, 192, 104, 64, 53)}};
static const lean_object* l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30_ = (const lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30_ = (const lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instTypeNameSnapshotTree = (const lean_object*)&l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value;
static const lean_ctor_object l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Language_instInhabitedSnapshot___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__0 = (const lean_object*)&l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default = (const lean_object*)&l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform = (const lean_object*)&l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Language_SnapshotTreeTransform_isIdentity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_isIdentity___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformInfoTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformInfoTree_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_compose(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_compose___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_transform(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_transform___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_transform(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedTransformedSnap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedTransformedSnap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_TransformedSnap_compose___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_TransformedSnap_compose(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_transform___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0 = (const lean_object*)&l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree = (const lean_object*)&l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_1),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(145, 226, 163, 148, 17, 100, 140, 218)}};
static const lean_object* l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Language_instTypeNameSnapshotLeaf = (const lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotLeaf;
static const lean_array_object l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0 = (const lean_object*)&l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf = (const lean_object*)&l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0 = (const lean_object*)&l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot = (const lean_object*)&l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Language_instInhabitedDynamicSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "instInhabitedDynamicSnapshot"};
static const lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__0 = (const lean_object*)&l_Lean_Language_instInhabitedDynamicSnapshot___closed__0_value;
static const lean_ctor_object l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Language_Snapshot_desc___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
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
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
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
static const lean_ctor_object l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
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
static const lean_ctor_object l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_30__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
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
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__31(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__30));
v___x_86_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__26, &l_Lean_Language_Snapshot_desc___autoParam___closed__26_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__26);
v___x_87_ = lean_array_push(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__32(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__31, &l_Lean_Language_Snapshot_desc___autoParam___closed__31_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__31);
v___x_89_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__16));
v___x_90_ = lean_box(2);
v___x_91_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
lean_ctor_set(v___x_91_, 2, v___x_88_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__33(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__32, &l_Lean_Language_Snapshot_desc___autoParam___closed__32_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__32);
v___x_93_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__13, &l_Lean_Language_Snapshot_desc___autoParam___closed__13_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__13);
v___x_94_ = lean_array_push(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__34(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__33, &l_Lean_Language_Snapshot_desc___autoParam___closed__33_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__33);
v___x_96_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__11));
v___x_97_ = lean_box(2);
v___x_98_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
lean_ctor_set(v___x_98_, 2, v___x_95_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__35(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__34, &l_Lean_Language_Snapshot_desc___autoParam___closed__34_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__34);
v___x_100_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__5));
v___x_101_ = lean_array_push(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__36(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__35, &l_Lean_Language_Snapshot_desc___autoParam___closed__35_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__35);
v___x_103_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__9));
v___x_104_ = lean_box(2);
v___x_105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_103_);
lean_ctor_set(v___x_105_, 2, v___x_102_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__37(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__36, &l_Lean_Language_Snapshot_desc___autoParam___closed__36_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__36);
v___x_107_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__5));
v___x_108_ = lean_array_push(v___x_107_, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__38(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_109_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__37, &l_Lean_Language_Snapshot_desc___autoParam___closed__37_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__37);
v___x_110_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__7));
v___x_111_ = lean_box(2);
v___x_112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_110_);
lean_ctor_set(v___x_112_, 2, v___x_109_);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__39(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__38, &l_Lean_Language_Snapshot_desc___autoParam___closed__38_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__38);
v___x_114_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__5));
v___x_115_ = lean_array_push(v___x_114_, v___x_113_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__40(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_116_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__39, &l_Lean_Language_Snapshot_desc___autoParam___closed__39_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__39);
v___x_117_ = ((lean_object*)(l_Lean_Language_Snapshot_desc___autoParam___closed__4));
v___x_118_ = lean_box(2);
v___x_119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_117_);
lean_ctor_set(v___x_119_, 2, v___x_116_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_obj_once(&l_Lean_Language_Snapshot_desc___autoParam___closed__40, &l_Lean_Language_Snapshot_desc___autoParam___closed__40_once, _init_l_Lean_Language_Snapshot_desc___autoParam___closed__40);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot___closed__1(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_unsigned_to_nat(32u);
v___x_123_ = lean_mk_empty_array_with_capacity(v___x_122_);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot___closed__2(void){
_start:
{
size_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_125_ = ((size_t)5ULL);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_unsigned_to_nat(32u);
v___x_128_ = lean_mk_empty_array_with_capacity(v___x_127_);
v___x_129_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__1, &l_Lean_Language_instInhabitedSnapshot___closed__1_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__1);
v___x_130_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
lean_ctor_set(v___x_130_, 2, v___x_126_);
lean_ctor_set(v___x_130_, 3, v___x_126_);
lean_ctor_set_usize(v___x_130_, 4, v___x_125_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot___closed__3(void){
_start:
{
lean_object* v___x_131_; uint64_t v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__2, &l_Lean_Language_instInhabitedSnapshot___closed__2_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__2);
v___x_132_ = 0ULL;
v___x_133_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set_uint64(v___x_133_, sizeof(void*)*1, v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot___closed__4(void){
_start:
{
uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_134_ = 0;
v___x_135_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_136_ = lean_box(0);
v___x_137_ = l_Lean_Language_Snapshot_instInhabitedDiagnostics_default;
v___x_138_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot___closed__0));
v___x_139_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_137_);
lean_ctor_set(v___x_139_, 2, v___x_136_);
lean_ctor_set(v___x_139_, 3, v___x_135_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*4, v___x_134_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___impl(lean_object* v_x_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_tag_nat(v_x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___impl___boxed(lean_object* v_x_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___impl(v_x_143_);
lean_dec(v_x_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(lean_object* v_t_145_, lean_object* v_k_146_){
_start:
{
if (lean_obj_tag(v_t_145_) == 1)
{
lean_object* v_range_147_; lean_object* v___x_148_; 
v_range_147_ = lean_ctor_get(v_t_145_, 0);
lean_inc_ref(v_range_147_);
lean_dec_ref_known(v_t_145_, 1);
v___x_148_ = lean_apply_1(v_k_146_, v_range_147_);
return v___x_148_;
}
else
{
lean_dec(v_t_145_);
return v_k_146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(lean_object* v_motive_149_, lean_object* v_ctorIdx_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_k_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_151_, v_k_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___boxed(lean_object* v_motive_155_, lean_object* v_ctorIdx_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_k_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(v_motive_155_, v_ctorIdx_156_, v_t_157_, v_h_158_, v_k_159_);
lean_dec(v_ctorIdx_156_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim___redArg(lean_object* v_t_161_, lean_object* v_inherit_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_161_, v_inherit_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim(lean_object* v_motive_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_inherit_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_165_, v_inherit_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim___redArg(lean_object* v_t_169_, lean_object* v_some_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_169_, v_some_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim(lean_object* v_motive_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_some_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_173_, v_some_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim___redArg(lean_object* v_t_177_, lean_object* v_skip_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_177_, v_skip_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim(lean_object* v_motive_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_skip_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_181_, v_skip_183_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_box(0);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(0);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(0);
return v___x_188_;
}
else
{
lean_object* v_val_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v_val_189_ = lean_ctor_get(v_x_187_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_187_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v_x_187_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_val_189_);
lean_dec(v_x_187_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_val_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_box(0);
v___x_198_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object* v_stx_x3f_199_){
_start:
{
if (lean_obj_tag(v_stx_x3f_199_) == 0)
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0, &l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0_once, _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0);
return v___x_200_;
}
else
{
lean_object* v_val_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_val_201_ = lean_ctor_get(v_stx_x3f_199_, 0);
v___x_202_ = 1;
v___x_203_ = l_Lean_Syntax_getRange_x3f(v_val_201_, v___x_202_);
v___x_204_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___x_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange___boxed(lean_object* v_stx_x3f_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v_stx_x3f_205_);
lean_dec(v_stx_x3f_205_);
return v_res_206_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_box(0);
v___x_208_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object* v_inst_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = lean_box(0);
v___x_211_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0, &l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0_once, _init_l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0);
v___x_212_ = lean_task_pure(v_inst_209_);
v___x_213_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_213_, 0, v___x_210_);
lean_ctor_set(v___x_213_, 1, v___x_211_);
lean_ctor_set(v___x_213_, 2, v___x_210_);
lean_ctor_set(v___x_213_, 3, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default(lean_object* v_00_u03b1_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask___redArg(lean_object* v_inst_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask(lean_object* v_a_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object* v_stx_x3f_222_, lean_object* v_cancelTk_x3f_223_, lean_object* v_reportingRange_224_, lean_object* v_act_225_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_io_as_task(v_act_225_, v___x_227_);
v___x_229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_229_, 0, v_stx_x3f_222_);
lean_ctor_set(v___x_229_, 1, v_reportingRange_224_);
lean_ctor_set(v___x_229_, 2, v_cancelTk_x3f_223_);
lean_ctor_set(v___x_229_, 3, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg___boxed(lean_object* v_stx_x3f_230_, lean_object* v_cancelTk_x3f_231_, lean_object* v_reportingRange_232_, lean_object* v_act_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v_stx_x3f_230_, v_cancelTk_x3f_231_, v_reportingRange_232_, v_act_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object* v_00_u03b1_236_, lean_object* v_stx_x3f_237_, lean_object* v_cancelTk_x3f_238_, lean_object* v_reportingRange_239_, lean_object* v_act_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v_stx_x3f_237_, v_cancelTk_x3f_238_, v_reportingRange_239_, v_act_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___boxed(lean_object* v_00_u03b1_243_, lean_object* v_stx_x3f_244_, lean_object* v_cancelTk_x3f_245_, lean_object* v_reportingRange_246_, lean_object* v_act_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Language_SnapshotTask_ofIO(v_00_u03b1_243_, v_stx_x3f_244_, v_cancelTk_x3f_245_, v_reportingRange_246_, v_act_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object* v_stx_x3f_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_252_ = lean_box(2);
v___x_253_ = lean_box(0);
v___x_254_ = lean_task_pure(v_a_251_);
v___x_255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_255_, 0, v_stx_x3f_250_);
lean_ctor_set(v___x_255_, 1, v___x_252_);
lean_ctor_set(v___x_255_, 2, v___x_253_);
lean_ctor_set(v___x_255_, 3, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished(lean_object* v_00_u03b1_256_, lean_object* v_stx_x3f_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Language_SnapshotTask_finished___redArg(v_stx_x3f_257_, v_a_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object* v_t_260_, lean_object* v_f_261_, lean_object* v_stx_x3f_262_, lean_object* v_reportingRange_263_, uint8_t v_sync_264_){
_start:
{
lean_object* v_cancelTk_x3f_265_; lean_object* v_task_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_275_; 
v_cancelTk_x3f_265_ = lean_ctor_get(v_t_260_, 2);
v_task_266_ = lean_ctor_get(v_t_260_, 3);
v_isSharedCheck_275_ = !lean_is_exclusive(v_t_260_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; lean_object* v_unused_277_; 
v_unused_276_ = lean_ctor_get(v_t_260_, 1);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_t_260_, 0);
lean_dec(v_unused_277_);
v___x_268_ = v_t_260_;
v_isShared_269_ = v_isSharedCheck_275_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_task_266_);
lean_inc(v_cancelTk_x3f_265_);
lean_dec(v_t_260_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_275_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_task_map(v_f_261_, v_task_266_, v___x_270_, v_sync_264_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 3, v___x_271_);
lean_ctor_set(v___x_268_, 1, v_reportingRange_263_);
lean_ctor_set(v___x_268_, 0, v_stx_x3f_262_);
v___x_273_ = v___x_268_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_stx_x3f_262_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_reportingRange_263_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_cancelTk_x3f_265_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg___boxed(lean_object* v_t_278_, lean_object* v_f_279_, lean_object* v_stx_x3f_280_, lean_object* v_reportingRange_281_, lean_object* v_sync_282_){
_start:
{
uint8_t v_sync_boxed_283_; lean_object* v_res_284_; 
v_sync_boxed_283_ = lean_unbox(v_sync_282_);
v_res_284_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_278_, v_f_279_, v_stx_x3f_280_, v_reportingRange_281_, v_sync_boxed_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map(lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_t_287_, lean_object* v_f_288_, lean_object* v_stx_x3f_289_, lean_object* v_reportingRange_290_, uint8_t v_sync_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_287_, v_f_288_, v_stx_x3f_289_, v_reportingRange_290_, v_sync_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___boxed(lean_object* v_00_u03b1_293_, lean_object* v_00_u03b2_294_, lean_object* v_t_295_, lean_object* v_f_296_, lean_object* v_stx_x3f_297_, lean_object* v_reportingRange_298_, lean_object* v_sync_299_){
_start:
{
uint8_t v_sync_boxed_300_; lean_object* v_res_301_; 
v_sync_boxed_300_ = lean_unbox(v_sync_299_);
v_res_301_ = l_Lean_Language_SnapshotTask_map(v_00_u03b1_293_, v_00_u03b2_294_, v_t_295_, v_f_296_, v_stx_x3f_297_, v_reportingRange_298_, v_sync_boxed_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(lean_object* v_act_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_305_; lean_object* v_task_306_; 
v___x_305_ = lean_apply_2(v_act_302_, v_a_303_, lean_box(0));
v_task_306_ = lean_ctor_get(v___x_305_, 3);
lean_inc_ref(v_task_306_);
lean_dec_ref(v___x_305_);
return v_task_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed(lean_object* v_act_307_, lean_object* v_a_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(v_act_307_, v_a_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object* v_t_311_, lean_object* v_act_312_, lean_object* v_stx_x3f_313_, lean_object* v_reportingRange_314_, lean_object* v_cancelTk_x3f_315_, uint8_t v_sync_316_){
_start:
{
lean_object* v_task_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v_task_318_ = lean_ctor_get(v_t_311_, 3);
v_isSharedCheck_328_ = !lean_is_exclusive(v_t_311_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; lean_object* v_unused_330_; lean_object* v_unused_331_; 
v_unused_329_ = lean_ctor_get(v_t_311_, 2);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_t_311_, 1);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_t_311_, 0);
lean_dec(v_unused_331_);
v___x_320_ = v_t_311_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_task_318_);
lean_dec(v_t_311_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___f_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___f_322_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_322_, 0, v_act_312_);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_io_bind_task(v_task_318_, v___f_322_, v___x_323_, v_sync_316_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 3, v___x_324_);
lean_ctor_set(v___x_320_, 2, v_cancelTk_x3f_315_);
lean_ctor_set(v___x_320_, 1, v_reportingRange_314_);
lean_ctor_set(v___x_320_, 0, v_stx_x3f_313_);
v___x_326_ = v___x_320_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_stx_x3f_313_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_reportingRange_314_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_cancelTk_x3f_315_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___boxed(lean_object* v_t_332_, lean_object* v_act_333_, lean_object* v_stx_x3f_334_, lean_object* v_reportingRange_335_, lean_object* v_cancelTk_x3f_336_, lean_object* v_sync_337_, lean_object* v_a_338_){
_start:
{
uint8_t v_sync_boxed_339_; lean_object* v_res_340_; 
v_sync_boxed_339_ = lean_unbox(v_sync_337_);
v_res_340_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_t_332_, v_act_333_, v_stx_x3f_334_, v_reportingRange_335_, v_cancelTk_x3f_336_, v_sync_boxed_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_t_343_, lean_object* v_act_344_, lean_object* v_stx_x3f_345_, lean_object* v_reportingRange_346_, lean_object* v_cancelTk_x3f_347_, uint8_t v_sync_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_t_343_, v_act_344_, v_stx_x3f_345_, v_reportingRange_346_, v_cancelTk_x3f_347_, v_sync_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___boxed(lean_object* v_00_u03b1_351_, lean_object* v_00_u03b2_352_, lean_object* v_t_353_, lean_object* v_act_354_, lean_object* v_stx_x3f_355_, lean_object* v_reportingRange_356_, lean_object* v_cancelTk_x3f_357_, lean_object* v_sync_358_, lean_object* v_a_359_){
_start:
{
uint8_t v_sync_boxed_360_; lean_object* v_res_361_; 
v_sync_boxed_360_ = lean_unbox(v_sync_358_);
v_res_361_ = l_Lean_Language_SnapshotTask_bindIO(v_00_u03b1_351_, v_00_u03b2_352_, v_t_353_, v_act_354_, v_stx_x3f_355_, v_reportingRange_356_, v_cancelTk_x3f_357_, v_sync_boxed_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object* v_t_362_){
_start:
{
lean_object* v_task_363_; lean_object* v___x_364_; 
v_task_363_ = lean_ctor_get(v_t_362_, 3);
lean_inc_ref(v_task_363_);
lean_dec_ref(v_t_362_);
v___x_364_ = lean_task_get_own(v_task_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object* v_00_u03b1_365_, lean_object* v_t_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Language_SnapshotTask_get___redArg(v_t_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object* v_t_368_){
_start:
{
lean_object* v_task_370_; uint8_t v___x_371_; 
v_task_370_ = lean_ctor_get(v_t_368_, 3);
lean_inc_ref(v_task_370_);
lean_dec_ref(v_t_368_);
v___x_371_ = lean_io_get_task_state(v_task_370_);
if (v___x_371_ == 2)
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_task_get_own(v_task_370_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; 
lean_dec_ref(v_task_370_);
v___x_374_ = lean_box(0);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg___boxed(lean_object* v_t_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object* v_00_u03b1_378_, lean_object* v_t_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___boxed(lean_object* v_00_u03b1_382_, lean_object* v_t_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Language_SnapshotTask_get_x3f(v_00_u03b1_382_, v_t_383_);
return v_res_385_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshotTree_default___closed__0));
v___x_389_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_388_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default(void){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshotTree_default___closed__1, &l_Lean_Language_instInhabitedSnapshotTree_default___closed__1_once, _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree(void){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Language_SnapshotTreeTransform_isIdentity(lean_object* v_trans_406_){
_start:
{
lean_object* v_startPos_407_; lean_object* v_stopPos_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_startPos_407_ = lean_ctor_get(v_trans_406_, 1);
v_stopPos_408_ = lean_ctor_get(v_trans_406_, 2);
v___x_409_ = lean_nat_sub(v_stopPos_408_, v_startPos_407_);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_nat_dec_eq(v___x_409_, v___x_410_);
lean_dec(v___x_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_isIdentity___boxed(lean_object* v_trans_412_){
_start:
{
uint8_t v_res_413_; lean_object* v_r_414_; 
v_res_413_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_trans_412_);
lean_dec_ref(v_trans_412_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformSyntax(lean_object* v_trans_415_, lean_object* v_stx_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Syntax_addTrailing(v_stx_416_, v_trans_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformInfoTree(lean_object* v_trans_418_, lean_object* v_t_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Elab_InfoTree_addTrailing(v_trans_418_, v_t_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformInfoTree_x3f(lean_object* v_trans_421_, lean_object* v_t_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Elab_InfoTree_addTrailing_x3f(v_trans_421_, v_t_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_compose(lean_object* v_outer_424_, lean_object* v_inner_425_){
_start:
{
lean_object* v_str_426_; lean_object* v_startPos_427_; lean_object* v_stopPos_428_; lean_object* v_startPos_429_; lean_object* v_stopPos_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_438_; 
v_str_426_ = lean_ctor_get(v_inner_425_, 0);
v_startPos_427_ = lean_ctor_get(v_inner_425_, 1);
v_stopPos_428_ = lean_ctor_get(v_inner_425_, 2);
v_startPos_429_ = lean_ctor_get(v_outer_424_, 1);
v_stopPos_430_ = lean_ctor_get(v_outer_424_, 2);
v_isSharedCheck_438_ = !lean_is_exclusive(v_outer_424_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v_outer_424_, 0);
lean_dec(v_unused_439_);
v___x_432_ = v_outer_424_;
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_stopPos_430_);
lean_inc(v_startPos_429_);
lean_dec(v_outer_424_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
uint8_t v_decide_434_; 
v_decide_434_ = lean_nat_dec_eq(v_stopPos_428_, v_startPos_429_);
lean_dec(v_startPos_429_);
if (v_decide_434_ == 0)
{
lean_del_object(v___x_432_);
lean_dec(v_stopPos_430_);
lean_inc_ref(v_inner_425_);
return v_inner_425_;
}
else
{
lean_object* v___x_436_; 
lean_inc(v_startPos_427_);
lean_inc_ref(v_str_426_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v_startPos_427_);
lean_ctor_set(v___x_432_, 0, v_str_426_);
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_str_426_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_startPos_427_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_stopPos_430_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_compose___boxed(lean_object* v_outer_440_, lean_object* v_inner_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Language_SnapshotTreeTransform_compose(v_outer_440_, v_inner_441_);
lean_dec_ref(v_inner_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_transform(lean_object* v_s_443_, lean_object* v_a_444_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_a_444_);
if (v___x_445_ == 0)
{
lean_object* v_infoTree_x3f_446_; 
v_infoTree_x3f_446_ = lean_ctor_get(v_s_443_, 2);
if (lean_obj_tag(v_infoTree_x3f_446_) == 0)
{
return v_s_443_;
}
else
{
lean_object* v_desc_447_; lean_object* v_diagnostics_448_; lean_object* v_traces_449_; uint8_t v_isFatal_450_; lean_object* v_val_451_; lean_object* v___x_452_; 
v_desc_447_ = lean_ctor_get(v_s_443_, 0);
v_diagnostics_448_ = lean_ctor_get(v_s_443_, 1);
v_traces_449_ = lean_ctor_get(v_s_443_, 3);
v_isFatal_450_ = lean_ctor_get_uint8(v_s_443_, sizeof(void*)*4);
v_val_451_ = lean_ctor_get(v_infoTree_x3f_446_, 0);
lean_inc(v_val_451_);
lean_inc_ref(v_a_444_);
v___x_452_ = l_Lean_Elab_InfoTree_addTrailing_x3f(v_a_444_, v_val_451_);
if (lean_obj_tag(v___x_452_) == 0)
{
return v_s_443_;
}
else
{
lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_inc_ref(v_traces_449_);
lean_inc_ref(v_diagnostics_448_);
lean_inc_ref(v_desc_447_);
v_isSharedCheck_459_ = !lean_is_exclusive(v_s_443_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; lean_object* v_unused_461_; lean_object* v_unused_462_; lean_object* v_unused_463_; 
v_unused_460_ = lean_ctor_get(v_s_443_, 3);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_s_443_, 2);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v_s_443_, 1);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_s_443_, 0);
lean_dec(v_unused_463_);
v___x_454_ = v_s_443_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_dec(v_s_443_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 2, v___x_452_);
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_desc_447_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_diagnostics_448_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_traces_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_458_, sizeof(void*)*4, v_isFatal_450_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
else
{
return v_s_443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_transform___boxed(lean_object* v_s_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Language_Snapshot_transform(v_s_464_, v_a_465_);
lean_dec_ref(v_a_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0___boxed(lean_object* v_a_467_, lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0(v_a_467_, v_x_468_);
lean_dec_ref(v_a_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(lean_object* v_a_470_, size_t v_sz_471_, size_t v_i_472_, lean_object* v_bs_473_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = lean_usize_dec_lt(v_i_472_, v_sz_471_);
if (v___x_474_ == 0)
{
return v_bs_473_;
}
else
{
lean_object* v_v_475_; lean_object* v_stx_x3f_476_; lean_object* v_reportingRange_477_; lean_object* v___f_478_; lean_object* v___x_479_; lean_object* v_bs_x27_480_; lean_object* v___x_481_; size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v_v_475_ = lean_array_uget(v_bs_473_, v_i_472_);
v_stx_x3f_476_ = lean_ctor_get(v_v_475_, 0);
lean_inc(v_stx_x3f_476_);
v_reportingRange_477_ = lean_ctor_get(v_v_475_, 1);
lean_inc(v_reportingRange_477_);
lean_inc_ref(v_a_470_);
v___f_478_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_478_, 0, v_a_470_);
v___x_479_ = lean_unsigned_to_nat(0u);
v_bs_x27_480_ = lean_array_uset(v_bs_473_, v_i_472_, v___x_479_);
v___x_481_ = l_Lean_Language_SnapshotTask_map___redArg(v_v_475_, v___f_478_, v_stx_x3f_476_, v_reportingRange_477_, v___x_474_);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_add(v_i_472_, v___x_482_);
v___x_484_ = lean_array_uset(v_bs_x27_480_, v_i_472_, v___x_481_);
v_i_472_ = v___x_483_;
v_bs_473_ = v___x_484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_transform(lean_object* v_t_486_, lean_object* v_a_487_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_a_487_);
if (v___x_488_ == 0)
{
lean_object* v_element_489_; lean_object* v_children_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_501_; 
v_element_489_ = lean_ctor_get(v_t_486_, 0);
v_children_490_ = lean_ctor_get(v_t_486_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_t_486_);
if (v_isSharedCheck_501_ == 0)
{
v___x_492_ = v_t_486_;
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_children_490_);
lean_inc(v_element_489_);
lean_dec(v_t_486_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; size_t v_sz_495_; size_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_494_ = l_Lean_Language_Snapshot_transform(v_element_489_, v_a_487_);
v_sz_495_ = lean_array_size(v_children_490_);
v___x_496_ = ((size_t)0ULL);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(v_a_487_, v_sz_495_, v___x_496_, v_children_490_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 1, v___x_497_);
lean_ctor_set(v___x_492_, 0, v___x_494_);
v___x_499_ = v___x_492_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
else
{
return v_t_486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0(lean_object* v_a_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Language_SnapshotTree_transform(v_x_503_, v_a_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object* v_t_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Language_SnapshotTree_transform(v_t_505_, v_a_506_);
lean_dec_ref(v_a_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___boxed(lean_object* v_a_508_, lean_object* v_sz_509_, lean_object* v_i_510_, lean_object* v_bs_511_){
_start:
{
size_t v_sz_boxed_512_; size_t v_i_boxed_513_; lean_object* v_res_514_; 
v_sz_boxed_512_ = lean_unbox_usize(v_sz_509_);
lean_dec(v_sz_509_);
v_i_boxed_513_ = lean_unbox_usize(v_i_510_);
lean_dec(v_i_510_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(v_a_508_, v_sz_boxed_512_, v_i_boxed_513_, v_bs_511_);
lean_dec_ref(v_a_508_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___redArg(lean_object* v_inst_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshotTreeTransform_default));
v___x_518_ = lean_apply_2(v_inst_515_, v_a_516_, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree(lean_object* v_00_u03b1_519_, lean_object* v_inst_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Language_toSnapshotTree___redArg(v_inst_520_, v_a_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedTransformedSnap___redArg(lean_object* v_inst_523_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshotTreeTransform_default));
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v_inst_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedTransformedSnap(lean_object* v_00_u03b1_526_, lean_object* v_inst_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Language_instInhabitedTransformedSnap___redArg(v_inst_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0(lean_object* v_inst_529_, lean_object* v_s_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_raw_532_; lean_object* v_transform_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_raw_532_ = lean_ctor_get(v_s_530_, 0);
lean_inc(v_raw_532_);
v_transform_533_ = lean_ctor_get(v_s_530_, 1);
lean_inc_ref(v_transform_533_);
lean_dec_ref(v_s_530_);
lean_inc_ref(v___y_531_);
v___x_534_ = l_Lean_Language_SnapshotTreeTransform_compose(v___y_531_, v_transform_533_);
lean_dec_ref(v_transform_533_);
v___x_535_ = lean_apply_2(v_inst_529_, v_raw_532_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed(lean_object* v_inst_536_, lean_object* v_s_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0(v_inst_536_, v_s_537_, v___y_538_);
lean_dec_ref(v___y_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg(lean_object* v_inst_540_){
_start:
{
lean_object* v___f_541_; 
v___f_541_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_541_, 0, v_inst_540_);
return v___f_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap(lean_object* v_00_u03b1_542_, lean_object* v_inst_543_){
_start:
{
lean_object* v___f_544_; 
v___f_544_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_544_, 0, v_inst_543_);
return v___f_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_TransformedSnap_compose___redArg(lean_object* v_outer_545_, lean_object* v_s_546_){
_start:
{
lean_object* v_raw_547_; lean_object* v_transform_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_556_; 
v_raw_547_ = lean_ctor_get(v_s_546_, 0);
v_transform_548_ = lean_ctor_get(v_s_546_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_s_546_);
if (v_isSharedCheck_556_ == 0)
{
v___x_550_ = v_s_546_;
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_transform_548_);
lean_inc(v_raw_547_);
lean_dec(v_s_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = l_Lean_Language_SnapshotTreeTransform_compose(v_outer_545_, v_transform_548_);
lean_dec_ref(v_transform_548_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_552_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_raw_547_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_552_);
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
LEAN_EXPORT lean_object* l_Lean_Language_TransformedSnap_compose(lean_object* v_00_u03b1_557_, lean_object* v_outer_558_, lean_object* v_s_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Language_TransformedSnap_compose___redArg(v_outer_558_, v_s_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0(lean_object* v_f_561_, lean_object* v_a_562_, lean_object* v_x_563_){
_start:
{
lean_object* v___x_564_; 
lean_inc_ref(v_a_562_);
v___x_564_ = lean_apply_2(v_f_561_, v_x_563_, v_a_562_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0___boxed(lean_object* v_f_565_, lean_object* v_a_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0(v_f_565_, v_a_566_, v_x_567_);
lean_dec_ref(v_a_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object* v_t_569_, lean_object* v_f_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_stx_x3f_572_; lean_object* v_reportingRange_573_; lean_object* v___f_574_; uint8_t v___x_575_; lean_object* v___x_576_; 
v_stx_x3f_572_ = lean_ctor_get(v_t_569_, 0);
lean_inc(v_stx_x3f_572_);
v_reportingRange_573_ = lean_ctor_get(v_t_569_, 1);
lean_inc(v_reportingRange_573_);
lean_inc_ref(v_a_571_);
v___f_574_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_574_, 0, v_f_570_);
lean_closure_set(v___f_574_, 1, v_a_571_);
v___x_575_ = 1;
v___x_576_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_569_, v___f_574_, v_stx_x3f_572_, v_reportingRange_573_, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___boxed(lean_object* v_t_577_, lean_object* v_f_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_577_, v_f_578_, v_a_579_);
lean_dec_ref(v_a_579_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith(lean_object* v_00_u03b1_581_, lean_object* v_t_582_, lean_object* v_f_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_582_, v_f_583_, v_a_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___boxed(lean_object* v_00_u03b1_586_, lean_object* v_t_587_, lean_object* v_f_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Language_SnapshotTask_transformWith(v_00_u03b1_586_, v_t_587_, v_f_588_, v_a_589_);
lean_dec_ref(v_a_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___redArg(lean_object* v_inst_591_, lean_object* v_t_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_592_, v_inst_591_, v_a_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___redArg___boxed(lean_object* v_inst_595_, lean_object* v_t_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Language_SnapshotTask_transform___redArg(v_inst_595_, v_t_596_, v_a_597_);
lean_dec_ref(v_a_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform(lean_object* v_00_u03b1_599_, lean_object* v_inst_600_, lean_object* v_t_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_601_, v_inst_600_, v_a_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___boxed(lean_object* v_00_u03b1_604_, lean_object* v_inst_605_, lean_object* v_t_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Language_SnapshotTask_transform(v_00_u03b1_604_, v_inst_605_, v_t_606_, v_a_607_);
lean_dec_ref(v_a_607_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object* v_inst_611_, lean_object* v_x_612_, lean_object* v___y_613_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
lean_object* v___x_614_; 
lean_dec_ref(v_inst_611_);
v___x_614_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_614_;
}
else
{
lean_object* v_val_615_; lean_object* v___x_616_; 
v_val_615_ = lean_ctor_get(v_x_612_, 0);
lean_inc(v_val_615_);
lean_dec_ref_known(v_x_612_, 1);
lean_inc_ref(v___y_613_);
v___x_616_ = lean_apply_2(v_inst_611_, v_val_615_, v___y_613_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed(lean_object* v_inst_617_, lean_object* v_x_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(v_inst_617_, v_x_618_, v___y_619_);
lean_dec_ref(v___y_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg(lean_object* v_inst_621_){
_start:
{
lean_object* v___f_622_; 
v___f_622_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_622_, 0, v_inst_621_);
return v___f_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object* v_00_u03b1_623_, lean_object* v_inst_624_){
_start:
{
lean_object* v___f_625_; 
v___f_625_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_625_, 0, v_inst_624_);
return v___f_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(lean_object* v_inst_626_, lean_object* v___x_627_, lean_object* v___f_628_, lean_object* v_snap_629_){
_start:
{
lean_object* v___x_631_; lean_object* v_children_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_631_ = l_Lean_Language_toSnapshotTree___redArg(v_inst_626_, v_snap_629_);
v_children_632_ = lean_ctor_get(v___x_631_, 1);
lean_inc_ref(v_children_632_);
lean_dec_ref(v___x_631_);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_array_get_size(v_children_632_);
v___x_635_ = lean_box(0);
v___x_636_ = lean_nat_dec_lt(v___x_633_, v___x_634_);
if (v___x_636_ == 0)
{
lean_dec_ref(v_children_632_);
lean_dec_ref(v___f_628_);
lean_dec_ref(v___x_627_);
return v___x_635_;
}
else
{
size_t v___x_637_; size_t v___x_638_; lean_object* v___x_203__overap_639_; lean_object* v___x_640_; 
v___x_637_ = ((size_t)0ULL);
v___x_638_ = lean_usize_of_nat(v___x_634_);
v___x_203__overap_639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_627_, v___f_628_, v_children_632_, v___x_637_, v___x_638_, v___x_635_);
v___x_640_ = lean_apply_1(v___x_203__overap_639_, lean_box(0));
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed(lean_object* v_inst_641_, lean_object* v___x_642_, lean_object* v___f_643_, lean_object* v_snap_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(v_inst_641_, v___x_642_, v___f_643_, v_snap_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(lean_object* v___f_647_, lean_object* v_x_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(v___f_647_, v_x_648_, v___y_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object* v_inst_652_, lean_object* v_t_653_){
_start:
{
lean_object* v___x_655_; lean_object* v_cancelTk_x3f_656_; lean_object* v_task_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___f_660_; 
v___x_655_ = l_instMonadBaseIO;
v_cancelTk_x3f_656_ = lean_ctor_get(v_t_653_, 2);
lean_inc(v_cancelTk_x3f_656_);
v_task_657_ = lean_ctor_get(v_t_653_, 3);
lean_inc_ref(v_task_657_);
lean_dec_ref(v_t_653_);
v___f_658_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0));
v___f_659_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_659_, 0, v___f_658_);
v___f_660_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_660_, 0, v_inst_652_);
lean_closure_set(v___f_660_, 1, v___x_655_);
lean_closure_set(v___f_660_, 2, v___f_659_);
if (lean_obj_tag(v_cancelTk_x3f_656_) == 1)
{
lean_object* v_val_665_; lean_object* v___x_666_; 
v_val_665_ = lean_ctor_get(v_cancelTk_x3f_656_, 0);
lean_inc(v_val_665_);
lean_dec_ref_known(v_cancelTk_x3f_656_, 1);
v___x_666_ = l_IO_CancelToken_set(v_val_665_);
lean_dec(v_val_665_);
goto v___jp_661_;
}
else
{
lean_dec(v_cancelTk_x3f_656_);
goto v___jp_661_;
}
v___jp_661_:
{
lean_object* v___x_662_; uint8_t v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = 1;
v___x_664_ = l_BaseIO_chainTask___redArg(v_task_657_, v___f_660_, v___x_662_, v___x_663_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object* v___f_667_, lean_object* v_x_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_667_, v___y_669_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___boxed(lean_object* v_inst_672_, lean_object* v_t_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_672_, v_t_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object* v_00_u03b1_676_, lean_object* v_inst_677_, lean_object* v_t_678_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_677_, v_t_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___boxed(lean_object* v_00_u03b1_681_, lean_object* v_inst_682_, lean_object* v_t_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Language_SnapshotTask_cancelRec(v_00_u03b1_681_, v_inst_682_, v_t_683_);
return v_res_685_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotLeaf(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = lean_unsigned_to_nat(32u);
v___x_694_ = lean_mk_empty_array_with_capacity(v___x_693_);
lean_dec_ref(v___x_694_);
v___x_695_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object* v_s_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = l_Lean_Language_Snapshot_transform(v_s_698_, v___y_699_);
v___x_701_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0));
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___boxed(lean_object* v_s_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(v_s_703_, v___y_704_);
lean_dec_ref(v___y_704_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object* v_s_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_toSnapshotTreeM_710_; lean_object* v___x_711_; 
v_toSnapshotTreeM_710_ = lean_ctor_get(v_s_708_, 1);
lean_inc_ref(v_toSnapshotTreeM_710_);
lean_dec_ref(v_s_708_);
lean_inc_ref(v___y_709_);
v___x_711_ = lean_apply_1(v_toSnapshotTreeM_710_, v___y_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object* v_s_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(v_s_712_, v___y_713_);
lean_dec_ref(v___y_713_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_val_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_inc(v_val_719_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_inst_717_);
lean_ctor_set(v___x_720_, 1, v_val_719_);
v___x_721_ = lean_apply_1(v_inst_718_, v_val_719_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object* v_00_u03b1_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_val_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v_inst_724_, v_inst_725_, v_val_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object* v_inst_728_, lean_object* v_snap_729_){
_start:
{
lean_object* v_val_730_; lean_object* v___x_731_; 
v_val_730_ = lean_ctor_get(v_snap_729_, 0);
v___x_731_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_730_, v_inst_728_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object* v_inst_732_, lean_object* v_snap_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_732_, v_snap_733_);
lean_dec_ref(v_snap_733_);
lean_dec(v_inst_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object* v_00_u03b1_735_, lean_object* v_inst_736_, lean_object* v_snap_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_736_, v_snap_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object* v_00_u03b1_739_, lean_object* v_inst_740_, lean_object* v_snap_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f(v_00_u03b1_739_, v_inst_740_, v_snap_741_);
lean_dec_ref(v_snap_741_);
lean_dec(v_inst_740_);
return v_res_742_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2(void){
_start:
{
uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = 1;
v___x_749_ = ((lean_object*)(l_Lean_Language_instInhabitedDynamicSnapshot___closed__1));
v___x_750_ = l_Lean_Name_toString(v___x_749_, v___x_748_);
return v___x_750_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3(void){
_start:
{
uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_751_ = 0;
v___x_752_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_753_ = lean_box(0);
v___x_754_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_755_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__2, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__2_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2);
v___x_756_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_754_);
lean_ctor_set(v___x_756_, 2, v___x_753_);
lean_ctor_set(v___x_756_, 3, v___x_752_);
lean_ctor_set_uint8(v___x_756_, sizeof(void*)*4, v___x_751_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4(void){
_start:
{
lean_object* v___x_757_; lean_object* v___f_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_757_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__3, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3);
v___f_758_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0));
v___x_759_ = ((lean_object*)(l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_));
v___x_760_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v___x_759_, v___f_758_, v___x_757_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot(void){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__4, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object* v_toApplicative_762_, lean_object* v_children_763_, lean_object* v_inst_764_, lean_object* v___f_765_, lean_object* v_____r_766_){
_start:
{
lean_object* v_toPure_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_toPure_767_ = lean_ctor_get(v_toApplicative_762_, 1);
lean_inc(v_toPure_767_);
lean_dec_ref(v_toApplicative_762_);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_array_get_size(v_children_763_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_nat_dec_lt(v___x_768_, v___x_769_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_dec(v___f_765_);
lean_dec_ref(v_inst_764_);
lean_dec_ref(v_children_763_);
v___x_772_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_770_);
return v___x_772_;
}
else
{
size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; 
lean_dec(v_toPure_767_);
v___x_773_ = ((size_t)0ULL);
v___x_774_ = lean_usize_of_nat(v___x_769_);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_764_, v___f_765_, v_children_763_, v___x_773_, v___x_774_, v___x_770_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object* v_inst_776_, lean_object* v_s_777_, lean_object* v_f_778_){
_start:
{
lean_object* v_toApplicative_779_; lean_object* v_toBind_780_; lean_object* v_element_781_; lean_object* v_children_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_toApplicative_779_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_779_);
v_toBind_780_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_780_);
v_element_781_ = lean_ctor_get(v_s_777_, 0);
lean_inc_ref(v_element_781_);
v_children_782_ = lean_ctor_get(v_s_777_, 1);
lean_inc_ref(v_children_782_);
lean_dec_ref(v_s_777_);
lean_inc(v_f_778_);
lean_inc_ref(v_inst_776_);
v___f_783_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_783_, 0, v_inst_776_);
lean_closure_set(v___f_783_, 1, v_f_778_);
v___f_784_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_784_, 0, v_toApplicative_779_);
lean_closure_set(v___f_784_, 1, v_children_782_);
lean_closure_set(v___f_784_, 2, v_inst_776_);
lean_closure_set(v___f_784_, 3, v___f_783_);
v___x_785_ = lean_apply_1(v_f_778_, v_element_781_);
v___x_786_ = lean_apply_4(v_toBind_780_, lean_box(0), lean_box(0), v___x_785_, v___f_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object* v_inst_787_, lean_object* v_f_788_, lean_object* v_x_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = l_Lean_Language_SnapshotTask_get___redArg(v___y_790_);
v___x_792_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_787_, v___x_791_, v_f_788_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object* v_m_793_, lean_object* v_inst_794_, lean_object* v_s_795_, lean_object* v_f_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_794_, v_s_795_, v_f_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object* v_toApplicative_798_, lean_object* v_children_799_, lean_object* v_inst_800_, lean_object* v___f_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_toPure_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_toPure_803_ = lean_ctor_get(v_toApplicative_798_, 1);
lean_inc(v_toPure_803_);
lean_dec_ref(v_toApplicative_798_);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_array_get_size(v_children_799_);
v___x_806_ = lean_nat_dec_lt(v___x_804_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_dec(v___f_801_);
lean_dec_ref(v_inst_800_);
lean_dec_ref(v_children_799_);
v___x_807_ = lean_apply_2(v_toPure_803_, lean_box(0), v_a_802_);
return v___x_807_;
}
else
{
size_t v___x_808_; size_t v___x_809_; lean_object* v___x_810_; 
lean_dec(v_toPure_803_);
v___x_808_ = ((size_t)0ULL);
v___x_809_ = lean_usize_of_nat(v___x_805_);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_800_, v___f_801_, v_children_799_, v___x_808_, v___x_809_, v_a_802_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object* v_inst_811_, lean_object* v_s_812_, lean_object* v_f_813_, lean_object* v_init_814_){
_start:
{
lean_object* v_toApplicative_815_; lean_object* v_toBind_816_; lean_object* v_element_817_; lean_object* v_children_818_; lean_object* v___f_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_toApplicative_815_ = lean_ctor_get(v_inst_811_, 0);
lean_inc_ref(v_toApplicative_815_);
v_toBind_816_ = lean_ctor_get(v_inst_811_, 1);
lean_inc(v_toBind_816_);
v_element_817_ = lean_ctor_get(v_s_812_, 0);
lean_inc_ref(v_element_817_);
v_children_818_ = lean_ctor_get(v_s_812_, 1);
lean_inc_ref(v_children_818_);
lean_dec_ref(v_s_812_);
lean_inc(v_f_813_);
lean_inc_ref(v_inst_811_);
v___f_819_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_819_, 0, v_inst_811_);
lean_closure_set(v___f_819_, 1, v_f_813_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_820_, 0, v_toApplicative_815_);
lean_closure_set(v___f_820_, 1, v_children_818_);
lean_closure_set(v___f_820_, 2, v_inst_811_);
lean_closure_set(v___f_820_, 3, v___f_819_);
v___x_821_ = lean_apply_2(v_f_813_, v_init_814_, v_element_817_);
v___x_822_ = lean_apply_4(v_toBind_816_, lean_box(0), lean_box(0), v___x_821_, v___f_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object* v_inst_823_, lean_object* v_f_824_, lean_object* v_a_825_, lean_object* v_snap_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = l_Lean_Language_SnapshotTask_get___redArg(v_snap_826_);
v___x_828_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_823_, v___x_827_, v_f_824_, v_a_825_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object* v_m_829_, lean_object* v_00_u03b1_830_, lean_object* v_inst_831_, lean_object* v_s_832_, lean_object* v_f_833_, lean_object* v_init_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_831_, v_s_832_, v_f_833_, v_init_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(lean_object* v_name_836_, lean_object* v_decl_837_, lean_object* v_ref_838_){
_start:
{
lean_object* v_defValue_840_; lean_object* v_descr_841_; lean_object* v_deprecation_x3f_842_; lean_object* v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_defValue_840_ = lean_ctor_get(v_decl_837_, 0);
v_descr_841_ = lean_ctor_get(v_decl_837_, 1);
v_deprecation_x3f_842_ = lean_ctor_get(v_decl_837_, 2);
v___x_843_ = lean_alloc_ctor(1, 0, 1);
v___x_844_ = lean_unbox(v_defValue_840_);
lean_ctor_set_uint8(v___x_843_, 0, v___x_844_);
lean_inc(v_deprecation_x3f_842_);
lean_inc_ref(v_descr_841_);
lean_inc_n(v_name_836_, 2);
v___x_845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_845_, 0, v_name_836_);
lean_ctor_set(v___x_845_, 1, v_ref_838_);
lean_ctor_set(v___x_845_, 2, v___x_843_);
lean_ctor_set(v___x_845_, 3, v_descr_841_);
lean_ctor_set(v___x_845_, 4, v_deprecation_x3f_842_);
v___x_846_ = lean_register_option(v_name_836_, v___x_845_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v___x_846_, 0);
lean_dec(v_unused_855_);
v___x_848_ = v___x_846_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_dec(v___x_846_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
lean_inc(v_defValue_840_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_name_836_);
lean_ctor_set(v___x_850_, 1, v_defValue_840_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_name_836_);
v_a_856_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_846_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_846_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_864_, lean_object* v_decl_865_, lean_object* v_ref_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v_name_864_, v_decl_865_, v_ref_866_);
lean_dec_ref(v_decl_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_883_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_884_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_885_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_886_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v___x_883_, v___x_884_, v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4____boxed(lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(lean_object* v_name_889_, lean_object* v_decl_890_, lean_object* v_ref_891_){
_start:
{
lean_object* v_defValue_893_; lean_object* v_descr_894_; lean_object* v_deprecation_x3f_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_defValue_893_ = lean_ctor_get(v_decl_890_, 0);
v_descr_894_ = lean_ctor_get(v_decl_890_, 1);
v_deprecation_x3f_895_ = lean_ctor_get(v_decl_890_, 2);
lean_inc(v_defValue_893_);
v___x_896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_896_, 0, v_defValue_893_);
lean_inc(v_deprecation_x3f_895_);
lean_inc_ref(v_descr_894_);
lean_inc_n(v_name_889_, 2);
v___x_897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_897_, 0, v_name_889_);
lean_ctor_set(v___x_897_, 1, v_ref_891_);
lean_ctor_set(v___x_897_, 2, v___x_896_);
lean_ctor_set(v___x_897_, 3, v_descr_894_);
lean_ctor_set(v___x_897_, 4, v_deprecation_x3f_895_);
v___x_898_ = lean_register_option(v_name_889_, v___x_897_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_906_; 
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v___x_898_, 0);
lean_dec(v_unused_907_);
v___x_900_ = v___x_898_;
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
else
{
lean_dec(v___x_898_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
lean_inc(v_defValue_893_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v_name_889_);
lean_ctor_set(v___x_902_, 1, v_defValue_893_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_902_);
v___x_904_ = v___x_900_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_name_889_);
v_a_908_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_898_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_898_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_916_, lean_object* v_decl_917_, lean_object* v_ref_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v_name_916_, v_decl_917_, v_ref_918_);
lean_dec_ref(v_decl_917_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_934_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_935_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_936_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_937_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v___x_934_, v___x_935_, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4____boxed(lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
return v_res_939_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(lean_object* v_opts_940_, lean_object* v_opt_941_){
_start:
{
lean_object* v_name_942_; lean_object* v_defValue_943_; lean_object* v_map_944_; lean_object* v___x_945_; 
v_name_942_ = lean_ctor_get(v_opt_941_, 0);
v_defValue_943_ = lean_ctor_get(v_opt_941_, 1);
v_map_944_ = lean_ctor_get(v_opts_940_, 0);
v___x_945_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_944_, v_name_942_);
if (lean_obj_tag(v___x_945_) == 0)
{
uint8_t v___x_946_; 
v___x_946_ = lean_unbox(v_defValue_943_);
return v___x_946_;
}
else
{
lean_object* v_val_947_; 
v_val_947_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_val_947_);
lean_dec_ref_known(v___x_945_, 1);
if (lean_obj_tag(v_val_947_) == 1)
{
uint8_t v_v_948_; 
v_v_948_ = lean_ctor_get_uint8(v_val_947_, 0);
lean_dec_ref_known(v_val_947_, 0);
return v_v_948_;
}
else
{
uint8_t v___x_949_; 
lean_dec(v_val_947_);
v___x_949_ = lean_unbox(v_defValue_943_);
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0___boxed(lean_object* v_opts_950_, lean_object* v_opt_951_){
_start:
{
uint8_t v_res_952_; lean_object* v_r_953_; 
v_res_952_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_950_, v_opt_951_);
lean_dec_ref(v_opt_951_);
lean_dec_ref(v_opts_950_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(lean_object* v_opts_954_, lean_object* v_opt_955_){
_start:
{
lean_object* v_name_956_; lean_object* v_defValue_957_; lean_object* v_map_958_; lean_object* v___x_959_; 
v_name_956_ = lean_ctor_get(v_opt_955_, 0);
v_defValue_957_ = lean_ctor_get(v_opt_955_, 1);
v_map_958_ = lean_ctor_get(v_opts_954_, 0);
v___x_959_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_958_, v_name_956_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_inc(v_defValue_957_);
return v_defValue_957_;
}
else
{
lean_object* v_val_960_; 
v_val_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_val_960_);
lean_dec_ref_known(v___x_959_, 1);
if (lean_obj_tag(v_val_960_) == 3)
{
lean_object* v_v_961_; 
v_v_961_ = lean_ctor_get(v_val_960_, 0);
lean_inc(v_v_961_);
lean_dec_ref_known(v_val_960_, 1);
return v_v_961_;
}
else
{
lean_dec(v_val_960_);
lean_inc(v_defValue_957_);
return v_defValue_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1___boxed(lean_object* v_opts_962_, lean_object* v_opt_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_962_, v_opt_963_);
lean_dec_ref(v_opt_963_);
lean_dec_ref(v_opts_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(lean_object* v_s_965_){
_start:
{
lean_object* v___x_967_; lean_object* v_putStr_968_; lean_object* v___x_969_; 
v___x_967_ = lean_get_stdout();
v_putStr_968_ = lean_ctor_get(v___x_967_, 4);
lean_inc_ref(v_putStr_968_);
lean_dec_ref(v___x_967_);
v___x_969_ = lean_apply_2(v_putStr_968_, v_s_965_, lean_box(0));
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2___boxed(lean_object* v_s_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v_s_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object* v_s_973_){
_start:
{
uint32_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = 10;
v___x_976_ = lean_string_push(v_s_973_, v___x_975_);
v___x_977_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3___boxed(lean_object* v_s_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v_s_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(lean_object* v_opts_983_, uint8_t v_json_984_, uint8_t v_includeEndPos_985_, lean_object* v_severityOverrides_986_, lean_object* v_as_987_, size_t v_i_988_, size_t v_stop_989_, lean_object* v_b_990_){
_start:
{
lean_object* v_a_993_; lean_object* v___y_998_; uint8_t v___y_999_; lean_object* v___y_1011_; uint8_t v___y_1012_; lean_object* v___y_1013_; uint8_t v_isSilent_1014_; lean_object* v___y_1037_; lean_object* v___y_1038_; uint8_t v___y_1039_; uint8_t v___x_1041_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1074_; uint8_t v_severity_1075_; 
v___x_1041_ = lean_usize_dec_eq(v_i_988_, v_stop_989_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1078_; lean_object* v_fileName_1079_; lean_object* v_pos_1080_; lean_object* v_endPos_1081_; uint8_t v_keepFullRange_1082_; uint8_t v_severity_1083_; uint8_t v_isSilent_1084_; lean_object* v_caption_1085_; lean_object* v_data_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1078_ = lean_array_uget(v_as_987_, v_i_988_);
v_fileName_1079_ = lean_ctor_get(v___x_1078_, 0);
v_pos_1080_ = lean_ctor_get(v___x_1078_, 1);
v_endPos_1081_ = lean_ctor_get(v___x_1078_, 2);
v_keepFullRange_1082_ = lean_ctor_get_uint8(v___x_1078_, sizeof(void*)*5);
v_severity_1083_ = lean_ctor_get_uint8(v___x_1078_, sizeof(void*)*5 + 1);
v_isSilent_1084_ = lean_ctor_get_uint8(v___x_1078_, sizeof(void*)*5 + 2);
v_caption_1085_ = lean_ctor_get(v___x_1078_, 3);
v_data_1086_ = lean_ctor_get(v___x_1078_, 4);
v___x_1087_ = l_Lean_MessageData_kind(v_data_1086_);
v___x_1088_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_severityOverrides_986_, v___x_1087_);
lean_dec(v___x_1087_);
if (lean_obj_tag(v___x_1088_) == 1)
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1098_; 
lean_inc(v_data_1086_);
lean_inc_ref(v_caption_1085_);
lean_inc(v_endPos_1081_);
lean_inc_ref(v_pos_1080_);
lean_inc_ref(v_fileName_1079_);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; lean_object* v_unused_1100_; lean_object* v_unused_1101_; lean_object* v_unused_1102_; lean_object* v_unused_1103_; 
v_unused_1099_ = lean_ctor_get(v___x_1078_, 4);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v___x_1078_, 3);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v___x_1078_, 2);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v___x_1078_, 1);
lean_dec(v_unused_1102_);
v_unused_1103_ = lean_ctor_get(v___x_1078_, 0);
lean_dec(v_unused_1103_);
v___x_1090_ = v___x_1078_;
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v___x_1078_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_val_1092_; lean_object* v___x_1094_; 
v_val_1092_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_val_1092_);
lean_dec_ref_known(v___x_1088_, 1);
if (v_isShared_1091_ == 0)
{
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_fileName_1079_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_pos_1080_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_endPos_1081_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_caption_1085_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_data_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*5, v_keepFullRange_1082_);
v___x_1094_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
uint8_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = lean_unbox(v_val_1092_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*5 + 1, v___x_1095_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*5 + 2, v_isSilent_1084_);
v___x_1096_ = lean_unbox(v_val_1092_);
lean_dec(v_val_1092_);
v___y_1074_ = v___x_1094_;
v_severity_1075_ = v___x_1096_;
goto v___jp_1073_;
}
}
}
else
{
lean_dec(v___x_1088_);
v___y_1074_ = v___x_1078_;
v_severity_1075_ = v_severity_1083_;
goto v___jp_1073_;
}
}
else
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_b_990_);
return v___x_1104_;
}
v___jp_992_:
{
size_t v___x_994_; size_t v___x_995_; 
v___x_994_ = ((size_t)1ULL);
v___x_995_ = lean_usize_add(v_i_988_, v___x_994_);
v_i_988_ = v___x_995_;
v_b_990_ = v_a_993_;
goto _start;
}
v___jp_997_:
{
if (v___y_999_ == 0)
{
v_a_993_ = v___y_998_;
goto v___jp_992_;
}
else
{
uint8_t v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = 1;
v___x_1001_ = lean_io_exit(v___x_1000_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_dec_ref_known(v___x_1001_, 1);
v_a_993_ = v___y_998_;
goto v___jp_992_;
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec(v___y_998_);
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
v___jp_1010_:
{
if (v_isSilent_1014_ == 0)
{
if (v_json_984_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = l_Lean_Message_toString(v___y_1013_, v_includeEndPos_985_);
v___x_1016_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_1015_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_dec_ref_known(v___x_1016_, 1);
v___y_998_ = v___y_1011_;
v___y_999_ = v___y_1012_;
goto v___jp_997_;
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v___y_1011_);
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = l_Lean_Message_toJson(v___y_1013_);
v___x_1026_ = l_Lean_Json_compress(v___x_1025_);
v___x_1027_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_1026_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_dec_ref_known(v___x_1027_, 1);
v___y_998_ = v___y_1011_;
v___y_999_ = v___y_1012_;
goto v___jp_997_;
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v___y_1011_);
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1013_);
v___y_998_ = v___y_1011_;
v___y_999_ = v___y_1012_;
goto v___jp_997_;
}
}
v___jp_1036_:
{
uint8_t v_isSilent_1040_; 
v_isSilent_1040_ = lean_ctor_get_uint8(v___y_1037_, sizeof(void*)*5 + 2);
v___y_1011_ = v___y_1038_;
v___y_1012_ = v___y_1039_;
v___y_1013_ = v___y_1037_;
v_isSilent_1014_ = v_isSilent_1040_;
goto v___jp_1010_;
}
v___jp_1042_:
{
lean_object* v_numErrors_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v_numErrors_1045_ = lean_nat_add(v_b_990_, v___y_1044_);
lean_dec(v_b_990_);
v___x_1046_ = l_Lean_Language_maxErrors;
v___x_1047_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_983_, v___x_1046_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_nat_dec_eq(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_nat_dec_lt(v___x_1047_, v_numErrors_1045_);
if (v___x_1050_ == 0)
{
lean_dec(v___x_1047_);
v___y_1037_ = v___y_1043_;
v___y_1038_ = v_numErrors_1045_;
v___y_1039_ = v___x_1050_;
goto v___jp_1036_;
}
else
{
lean_object* v_fileName_1051_; lean_object* v_pos_1052_; lean_object* v_endPos_1053_; uint8_t v_keepFullRange_1054_; uint8_t v_isSilent_1055_; lean_object* v_caption_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1071_; 
v_fileName_1051_ = lean_ctor_get(v___y_1043_, 0);
v_pos_1052_ = lean_ctor_get(v___y_1043_, 1);
v_endPos_1053_ = lean_ctor_get(v___y_1043_, 2);
v_keepFullRange_1054_ = lean_ctor_get_uint8(v___y_1043_, sizeof(void*)*5);
v_isSilent_1055_ = lean_ctor_get_uint8(v___y_1043_, sizeof(void*)*5 + 2);
v_caption_1056_ = lean_ctor_get(v___y_1043_, 3);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___y_1043_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v___y_1043_, 4);
lean_dec(v_unused_1072_);
v___x_1058_ = v___y_1043_;
v_isShared_1059_ = v_isSharedCheck_1071_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_caption_1056_);
lean_inc(v_endPos_1053_);
lean_inc(v_pos_1052_);
lean_inc(v_fileName_1051_);
lean_dec(v___y_1043_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1071_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1060_ = 2;
v___x_1061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0));
v___x_1062_ = l_Nat_reprFast(v___x_1047_);
v___x_1063_ = lean_string_append(v___x_1061_, v___x_1062_);
lean_dec_ref(v___x_1062_);
v___x_1064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1));
v___x_1065_ = lean_string_append(v___x_1063_, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
v___x_1067_ = l_Lean_MessageData_ofFormat(v___x_1066_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 4, v___x_1067_);
v___x_1069_ = v___x_1058_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_fileName_1051_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_pos_1052_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_endPos_1053_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v_caption_1056_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v___x_1067_);
lean_ctor_set_uint8(v_reuseFailAlloc_1070_, sizeof(void*)*5, v_keepFullRange_1054_);
lean_ctor_set_uint8(v_reuseFailAlloc_1070_, sizeof(void*)*5 + 2, v_isSilent_1055_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*5 + 1, v___x_1060_);
v___y_1011_ = v_numErrors_1045_;
v___y_1012_ = v___x_1050_;
v___y_1013_ = v___x_1069_;
v_isSilent_1014_ = v_isSilent_1055_;
goto v___jp_1010_;
}
}
}
}
else
{
lean_dec(v___x_1047_);
v___y_1037_ = v___y_1043_;
v___y_1038_ = v_numErrors_1045_;
v___y_1039_ = v___x_1041_;
goto v___jp_1036_;
}
}
v___jp_1073_:
{
if (v_severity_1075_ == 2)
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_unsigned_to_nat(1u);
v___y_1043_ = v___y_1074_;
v___y_1044_ = v___x_1076_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_unsigned_to_nat(0u);
v___y_1043_ = v___y_1074_;
v___y_1044_ = v___x_1077_;
goto v___jp_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___boxed(lean_object* v_opts_1105_, lean_object* v_json_1106_, lean_object* v_includeEndPos_1107_, lean_object* v_severityOverrides_1108_, lean_object* v_as_1109_, lean_object* v_i_1110_, lean_object* v_stop_1111_, lean_object* v_b_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v_json_boxed_1114_; uint8_t v_includeEndPos_boxed_1115_; size_t v_i_boxed_1116_; size_t v_stop_boxed_1117_; lean_object* v_res_1118_; 
v_json_boxed_1114_ = lean_unbox(v_json_1106_);
v_includeEndPos_boxed_1115_ = lean_unbox(v_includeEndPos_1107_);
v_i_boxed_1116_ = lean_unbox_usize(v_i_1110_);
lean_dec(v_i_1110_);
v_stop_boxed_1117_ = lean_unbox_usize(v_stop_1111_);
lean_dec(v_stop_1111_);
v_res_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1105_, v_json_boxed_1114_, v_includeEndPos_boxed_1115_, v_severityOverrides_1108_, v_as_1109_, v_i_boxed_1116_, v_stop_boxed_1117_, v_b_1112_);
lean_dec_ref(v_as_1109_);
lean_dec(v_severityOverrides_1108_);
lean_dec_ref(v_opts_1105_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(lean_object* v_opts_1119_, uint8_t v_json_1120_, uint8_t v_includeEndPos_1121_, lean_object* v_severityOverrides_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 0)
{
lean_object* v_cs_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1139_; 
v_cs_1126_ = lean_ctor_get(v_x_1123_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_x_1123_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1128_ = v_x_1123_;
v_isShared_1129_ = v_isSharedCheck_1139_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_cs_1126_);
lean_dec(v_x_1123_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1139_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_array_get_size(v_cs_1126_);
v___x_1132_ = lean_nat_dec_lt(v___x_1130_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1134_; 
lean_dec_ref(v_cs_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v_x_1124_);
v___x_1134_ = v___x_1128_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_x_1124_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
else
{
size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
lean_del_object(v___x_1128_);
v___x_1136_ = ((size_t)0ULL);
v___x_1137_ = lean_usize_of_nat(v___x_1131_);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1119_, v_json_1120_, v_includeEndPos_1121_, v_severityOverrides_1122_, v_cs_1126_, v___x_1136_, v___x_1137_, v_x_1124_);
lean_dec_ref(v_cs_1126_);
return v___x_1138_;
}
}
}
else
{
lean_object* v_vs_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1153_; 
v_vs_1140_ = lean_ctor_get(v_x_1123_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_x_1123_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1142_ = v_x_1123_;
v_isShared_1143_ = v_isSharedCheck_1153_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_vs_1140_);
lean_dec(v_x_1123_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1153_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = lean_array_get_size(v_vs_1140_);
v___x_1146_ = lean_nat_dec_lt(v___x_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1148_; 
lean_dec_ref(v_vs_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set_tag(v___x_1142_, 0);
lean_ctor_set(v___x_1142_, 0, v_x_1124_);
v___x_1148_ = v___x_1142_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_x_1124_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
size_t v___x_1150_; size_t v___x_1151_; lean_object* v___x_1152_; 
lean_del_object(v___x_1142_);
v___x_1150_ = ((size_t)0ULL);
v___x_1151_ = lean_usize_of_nat(v___x_1145_);
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1119_, v_json_1120_, v_includeEndPos_1121_, v_severityOverrides_1122_, v_vs_1140_, v___x_1150_, v___x_1151_, v_x_1124_);
lean_dec_ref(v_vs_1140_);
return v___x_1152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(lean_object* v_opts_1154_, uint8_t v_json_1155_, uint8_t v_includeEndPos_1156_, lean_object* v_severityOverrides_1157_, lean_object* v_as_1158_, size_t v_i_1159_, size_t v_stop_1160_, lean_object* v_b_1161_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_eq(v_i_1159_, v_stop_1160_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_array_uget_borrowed(v_as_1158_, v_i_1159_);
lean_inc(v___x_1164_);
v___x_1165_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1154_, v_json_1155_, v_includeEndPos_1156_, v_severityOverrides_1157_, v___x_1164_, v_b_1161_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; size_t v___x_1167_; size_t v___x_1168_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = ((size_t)1ULL);
v___x_1168_ = lean_usize_add(v_i_1159_, v___x_1167_);
v_i_1159_ = v___x_1168_;
v_b_1161_ = v_a_1166_;
goto _start;
}
else
{
return v___x_1165_;
}
}
else
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_b_1161_);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5___boxed(lean_object* v_opts_1171_, lean_object* v_json_1172_, lean_object* v_includeEndPos_1173_, lean_object* v_severityOverrides_1174_, lean_object* v_as_1175_, lean_object* v_i_1176_, lean_object* v_stop_1177_, lean_object* v_b_1178_, lean_object* v___y_1179_){
_start:
{
uint8_t v_json_boxed_1180_; uint8_t v_includeEndPos_boxed_1181_; size_t v_i_boxed_1182_; size_t v_stop_boxed_1183_; lean_object* v_res_1184_; 
v_json_boxed_1180_ = lean_unbox(v_json_1172_);
v_includeEndPos_boxed_1181_ = lean_unbox(v_includeEndPos_1173_);
v_i_boxed_1182_ = lean_unbox_usize(v_i_1176_);
lean_dec(v_i_1176_);
v_stop_boxed_1183_ = lean_unbox_usize(v_stop_1177_);
lean_dec(v_stop_1177_);
v_res_1184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1171_, v_json_boxed_1180_, v_includeEndPos_boxed_1181_, v_severityOverrides_1174_, v_as_1175_, v_i_boxed_1182_, v_stop_boxed_1183_, v_b_1178_);
lean_dec_ref(v_as_1175_);
lean_dec(v_severityOverrides_1174_);
lean_dec_ref(v_opts_1171_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6___boxed(lean_object* v_opts_1185_, lean_object* v_json_1186_, lean_object* v_includeEndPos_1187_, lean_object* v_severityOverrides_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v_json_boxed_1192_; uint8_t v_includeEndPos_boxed_1193_; lean_object* v_res_1194_; 
v_json_boxed_1192_ = lean_unbox(v_json_1186_);
v_includeEndPos_boxed_1193_ = lean_unbox(v_includeEndPos_1187_);
v_res_1194_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1185_, v_json_boxed_1192_, v_includeEndPos_boxed_1193_, v_severityOverrides_1188_, v_x_1189_, v_x_1190_);
lean_dec(v_severityOverrides_1188_);
lean_dec_ref(v_opts_1185_);
return v_res_1194_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(lean_object* v_opts_1196_, uint8_t v_json_1197_, uint8_t v_includeEndPos_1198_, lean_object* v_severityOverrides_1199_, lean_object* v_x_1200_, size_t v_x_1201_, size_t v_x_1202_, lean_object* v_x_1203_){
_start:
{
if (lean_obj_tag(v_x_1200_) == 0)
{
lean_object* v_cs_1205_; lean_object* v___x_1206_; size_t v___x_1207_; lean_object* v_j_1208_; lean_object* v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; lean_object* v___x_1216_; 
v_cs_1205_ = lean_ctor_get(v_x_1200_, 0);
lean_inc_ref(v_cs_1205_);
lean_dec_ref_known(v_x_1200_, 1);
v___x_1206_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0);
v___x_1207_ = lean_usize_shift_right(v_x_1201_, v_x_1202_);
v_j_1208_ = lean_usize_to_nat(v___x_1207_);
v___x_1209_ = lean_array_get_borrowed(v___x_1206_, v_cs_1205_, v_j_1208_);
v___x_1210_ = ((size_t)1ULL);
v___x_1211_ = lean_usize_shift_left(v___x_1210_, v_x_1202_);
v___x_1212_ = lean_usize_sub(v___x_1211_, v___x_1210_);
v___x_1213_ = lean_usize_land(v_x_1201_, v___x_1212_);
v___x_1214_ = ((size_t)5ULL);
v___x_1215_ = lean_usize_sub(v_x_1202_, v___x_1214_);
lean_inc(v___x_1209_);
v___x_1216_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1196_, v_json_1197_, v_includeEndPos_1198_, v_severityOverrides_1199_, v___x_1209_, v___x_1213_, v___x_1215_, v_x_1203_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v___x_1218_ = lean_unsigned_to_nat(1u);
v___x_1219_ = lean_nat_add(v_j_1208_, v___x_1218_);
lean_dec(v_j_1208_);
v___x_1220_ = lean_array_get_size(v_cs_1205_);
v___x_1221_ = lean_nat_dec_lt(v___x_1219_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_dec(v___x_1219_);
lean_dec_ref(v_cs_1205_);
return v___x_1216_;
}
else
{
size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1222_ = lean_usize_of_nat(v___x_1219_);
lean_dec(v___x_1219_);
v___x_1223_ = lean_usize_of_nat(v___x_1220_);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1196_, v_json_1197_, v_includeEndPos_1198_, v_severityOverrides_1199_, v_cs_1205_, v___x_1222_, v___x_1223_, v_a_1217_);
lean_dec_ref(v_cs_1205_);
return v___x_1224_;
}
}
else
{
lean_dec(v_j_1208_);
lean_dec_ref(v_cs_1205_);
return v___x_1216_;
}
}
else
{
lean_object* v_vs_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1238_; 
v_vs_1225_ = lean_ctor_get(v_x_1200_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_x_1200_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1227_ = v_x_1200_;
v_isShared_1228_ = v_isSharedCheck_1238_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_vs_1225_);
lean_dec(v_x_1200_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1238_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1229_ = lean_usize_to_nat(v_x_1201_);
v___x_1230_ = lean_array_get_size(v_vs_1225_);
v___x_1231_ = lean_nat_dec_lt(v___x_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1233_; 
lean_dec(v___x_1229_);
lean_dec_ref(v_vs_1225_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set_tag(v___x_1227_, 0);
lean_ctor_set(v___x_1227_, 0, v_x_1203_);
v___x_1233_ = v___x_1227_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_x_1203_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
else
{
size_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; 
lean_del_object(v___x_1227_);
v___x_1235_ = lean_usize_of_nat(v___x_1229_);
lean_dec(v___x_1229_);
v___x_1236_ = lean_usize_of_nat(v___x_1230_);
v___x_1237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1196_, v_json_1197_, v_includeEndPos_1198_, v_severityOverrides_1199_, v_vs_1225_, v___x_1235_, v___x_1236_, v_x_1203_);
lean_dec_ref(v_vs_1225_);
return v___x_1237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___boxed(lean_object* v_opts_1239_, lean_object* v_json_1240_, lean_object* v_includeEndPos_1241_, lean_object* v_severityOverrides_1242_, lean_object* v_x_1243_, lean_object* v_x_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_, lean_object* v___y_1247_){
_start:
{
uint8_t v_json_boxed_1248_; uint8_t v_includeEndPos_boxed_1249_; size_t v_x_2240__boxed_1250_; size_t v_x_2241__boxed_1251_; lean_object* v_res_1252_; 
v_json_boxed_1248_ = lean_unbox(v_json_1240_);
v_includeEndPos_boxed_1249_ = lean_unbox(v_includeEndPos_1241_);
v_x_2240__boxed_1250_ = lean_unbox_usize(v_x_1244_);
lean_dec(v_x_1244_);
v_x_2241__boxed_1251_ = lean_unbox_usize(v_x_1245_);
lean_dec(v_x_1245_);
v_res_1252_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1239_, v_json_boxed_1248_, v_includeEndPos_boxed_1249_, v_severityOverrides_1242_, v_x_1243_, v_x_2240__boxed_1250_, v_x_2241__boxed_1251_, v_x_1246_);
lean_dec(v_severityOverrides_1242_);
lean_dec_ref(v_opts_1239_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(lean_object* v_opts_1253_, uint8_t v_json_1254_, uint8_t v_includeEndPos_1255_, lean_object* v_severityOverrides_1256_, lean_object* v_t_1257_, lean_object* v_init_1258_, lean_object* v_start_1259_){
_start:
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_nat_dec_eq(v_start_1259_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v_root_1263_; lean_object* v_tail_1264_; size_t v_shift_1265_; lean_object* v_tailOff_1266_; uint8_t v___x_1267_; 
v_root_1263_ = lean_ctor_get(v_t_1257_, 0);
lean_inc_ref(v_root_1263_);
v_tail_1264_ = lean_ctor_get(v_t_1257_, 1);
lean_inc_ref(v_tail_1264_);
v_shift_1265_ = lean_ctor_get_usize(v_t_1257_, 4);
v_tailOff_1266_ = lean_ctor_get(v_t_1257_, 3);
lean_inc(v_tailOff_1266_);
lean_dec_ref(v_t_1257_);
v___x_1267_ = lean_nat_dec_le(v_tailOff_1266_, v_start_1259_);
if (v___x_1267_ == 0)
{
size_t v___x_1268_; lean_object* v___x_1269_; 
lean_dec(v_tailOff_1266_);
v___x_1268_ = lean_usize_of_nat(v_start_1259_);
v___x_1269_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1253_, v_json_1254_, v_includeEndPos_1255_, v_severityOverrides_1256_, v_root_1263_, v___x_1268_, v_shift_1265_, v_init_1258_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v___x_1271_ = lean_array_get_size(v_tail_1264_);
v___x_1272_ = lean_nat_dec_lt(v___x_1261_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec_ref(v_tail_1264_);
return v___x_1269_;
}
else
{
size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = lean_usize_of_nat(v___x_1271_);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1253_, v_json_1254_, v_includeEndPos_1255_, v_severityOverrides_1256_, v_tail_1264_, v___x_1273_, v___x_1274_, v_a_1270_);
lean_dec_ref(v_tail_1264_);
return v___x_1275_;
}
}
else
{
lean_dec_ref(v_tail_1264_);
return v___x_1269_;
}
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
lean_dec_ref(v_root_1263_);
v___x_1276_ = lean_nat_sub(v_start_1259_, v_tailOff_1266_);
lean_dec(v_tailOff_1266_);
v___x_1277_ = lean_array_get_size(v_tail_1264_);
v___x_1278_ = lean_nat_dec_lt(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_dec(v___x_1276_);
lean_dec_ref(v_tail_1264_);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v_init_1258_);
return v___x_1279_;
}
else
{
size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = lean_usize_of_nat(v___x_1276_);
lean_dec(v___x_1276_);
v___x_1281_ = lean_usize_of_nat(v___x_1277_);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1253_, v_json_1254_, v_includeEndPos_1255_, v_severityOverrides_1256_, v_tail_1264_, v___x_1280_, v___x_1281_, v_init_1258_);
lean_dec_ref(v_tail_1264_);
return v___x_1282_;
}
}
}
else
{
lean_object* v_root_1283_; lean_object* v_tail_1284_; lean_object* v___x_1285_; 
v_root_1283_ = lean_ctor_get(v_t_1257_, 0);
lean_inc_ref(v_root_1283_);
v_tail_1284_ = lean_ctor_get(v_t_1257_, 1);
lean_inc_ref(v_tail_1284_);
lean_dec_ref(v_t_1257_);
v___x_1285_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1253_, v_json_1254_, v_includeEndPos_1255_, v_severityOverrides_1256_, v_root_1283_, v_init_1258_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v___x_1287_ = lean_array_get_size(v_tail_1284_);
v___x_1288_ = lean_nat_dec_lt(v___x_1261_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_dec_ref(v_tail_1284_);
return v___x_1285_;
}
else
{
size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; 
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = lean_usize_of_nat(v___x_1287_);
v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1253_, v_json_1254_, v_includeEndPos_1255_, v_severityOverrides_1256_, v_tail_1284_, v___x_1289_, v___x_1290_, v_a_1286_);
lean_dec_ref(v_tail_1284_);
return v___x_1291_;
}
}
else
{
lean_dec_ref(v_tail_1284_);
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4___boxed(lean_object* v_opts_1292_, lean_object* v_json_1293_, lean_object* v_includeEndPos_1294_, lean_object* v_severityOverrides_1295_, lean_object* v_t_1296_, lean_object* v_init_1297_, lean_object* v_start_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v_json_boxed_1300_; uint8_t v_includeEndPos_boxed_1301_; lean_object* v_res_1302_; 
v_json_boxed_1300_ = lean_unbox(v_json_1293_);
v_includeEndPos_boxed_1301_ = lean_unbox(v_includeEndPos_1294_);
v_res_1302_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1292_, v_json_boxed_1300_, v_includeEndPos_boxed_1301_, v_severityOverrides_1295_, v_t_1296_, v_init_1297_, v_start_1298_);
lean_dec(v_start_1298_);
lean_dec(v_severityOverrides_1295_);
lean_dec_ref(v_opts_1292_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(lean_object* v_msgLog_1303_, lean_object* v_opts_1304_, uint8_t v_json_1305_, lean_object* v_severityOverrides_1306_, lean_object* v_numErrors_1307_){
_start:
{
lean_object* v_unreported_1309_; lean_object* v___x_1310_; uint8_t v_includeEndPos_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_unreported_1309_ = lean_ctor_get(v_msgLog_1303_, 1);
lean_inc_ref(v_unreported_1309_);
lean_dec_ref(v_msgLog_1303_);
v___x_1310_ = l_Lean_Language_printMessageEndPos;
v_includeEndPos_1311_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_1304_, v___x_1310_);
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1304_, v_json_1305_, v_includeEndPos_1311_, v_severityOverrides_1306_, v_unreported_1309_, v_numErrors_1307_, v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___boxed(lean_object* v_msgLog_1314_, lean_object* v_opts_1315_, lean_object* v_json_1316_, lean_object* v_severityOverrides_1317_, lean_object* v_numErrors_1318_, lean_object* v_a_1319_){
_start:
{
uint8_t v_json_boxed_1320_; lean_object* v_res_1321_; 
v_json_boxed_1320_ = lean_unbox(v_json_1316_);
v_res_1321_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1314_, v_opts_1315_, v_json_boxed_1320_, v_severityOverrides_1317_, v_numErrors_1318_);
lean_dec(v_severityOverrides_1317_);
lean_dec_ref(v_opts_1315_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object* v_opts_1322_, uint8_t v_json_1323_, lean_object* v_severityOverrides_1324_, lean_object* v_s_1325_, lean_object* v_init_1326_){
_start:
{
lean_object* v_element_1328_; lean_object* v_diagnostics_1329_; lean_object* v_children_1330_; lean_object* v_msgLog_1331_; lean_object* v___x_1332_; 
v_element_1328_ = lean_ctor_get(v_s_1325_, 0);
v_diagnostics_1329_ = lean_ctor_get(v_element_1328_, 1);
lean_inc_ref(v_diagnostics_1329_);
v_children_1330_ = lean_ctor_get(v_s_1325_, 1);
lean_inc_ref(v_children_1330_);
lean_dec_ref(v_s_1325_);
v_msgLog_1331_ = lean_ctor_get(v_diagnostics_1329_, 0);
lean_inc_ref(v_msgLog_1331_);
lean_dec_ref(v_diagnostics_1329_);
v___x_1332_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1331_, v_opts_1322_, v_json_1323_, v_severityOverrides_1324_, v_init_1326_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_array_get_size(v_children_1330_);
v___x_1336_ = lean_nat_dec_lt(v___x_1334_, v___x_1335_);
if (v___x_1336_ == 0)
{
lean_dec_ref(v_children_1330_);
return v___x_1332_;
}
else
{
size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; 
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1337_ = ((size_t)0ULL);
v___x_1338_ = lean_usize_of_nat(v___x_1335_);
v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1322_, v_json_1323_, v_severityOverrides_1324_, v_children_1330_, v___x_1337_, v___x_1338_, v_a_1333_);
lean_dec_ref(v_children_1330_);
return v___x_1339_;
}
}
else
{
lean_dec_ref(v_children_1330_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object* v_opts_1340_, uint8_t v_json_1341_, lean_object* v_severityOverrides_1342_, lean_object* v_as_1343_, size_t v_i_1344_, size_t v_stop_1345_, lean_object* v_b_1346_){
_start:
{
uint8_t v___x_1348_; 
v___x_1348_ = lean_usize_dec_eq(v_i_1344_, v_stop_1345_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = lean_array_uget_borrowed(v_as_1343_, v_i_1344_);
lean_inc(v___x_1349_);
v___x_1350_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1349_);
v___x_1351_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1340_, v_json_1341_, v_severityOverrides_1342_, v___x_1350_, v_b_1346_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; size_t v___x_1353_; size_t v___x_1354_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = ((size_t)1ULL);
v___x_1354_ = lean_usize_add(v_i_1344_, v___x_1353_);
v_i_1344_ = v___x_1354_;
v_b_1346_ = v_a_1352_;
goto _start;
}
else
{
return v___x_1351_;
}
}
else
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_b_1346_);
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object* v_opts_1357_, lean_object* v_json_1358_, lean_object* v_severityOverrides_1359_, lean_object* v_as_1360_, lean_object* v_i_1361_, lean_object* v_stop_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_){
_start:
{
uint8_t v_json_boxed_1365_; size_t v_i_boxed_1366_; size_t v_stop_boxed_1367_; lean_object* v_res_1368_; 
v_json_boxed_1365_ = lean_unbox(v_json_1358_);
v_i_boxed_1366_ = lean_unbox_usize(v_i_1361_);
lean_dec(v_i_1361_);
v_stop_boxed_1367_ = lean_unbox_usize(v_stop_1362_);
lean_dec(v_stop_1362_);
v_res_1368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1357_, v_json_boxed_1365_, v_severityOverrides_1359_, v_as_1360_, v_i_boxed_1366_, v_stop_boxed_1367_, v_b_1363_);
lean_dec_ref(v_as_1360_);
lean_dec(v_severityOverrides_1359_);
lean_dec_ref(v_opts_1357_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object* v_opts_1369_, lean_object* v_json_1370_, lean_object* v_severityOverrides_1371_, lean_object* v_s_1372_, lean_object* v_init_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v_json_boxed_1375_; lean_object* v_res_1376_; 
v_json_boxed_1375_ = lean_unbox(v_json_1370_);
v_res_1376_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1369_, v_json_boxed_1375_, v_severityOverrides_1371_, v_s_1372_, v_init_1373_);
lean_dec(v_severityOverrides_1371_);
lean_dec_ref(v_opts_1369_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object* v_s_1377_, lean_object* v_opts_1378_, uint8_t v_json_1379_, lean_object* v_severityOverrides_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1378_, v_json_1379_, v_severityOverrides_1380_, v_s_1377_, v___x_1382_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1393_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1388_ = lean_nat_dec_lt(v___x_1382_, v_a_1384_);
lean_dec(v_a_1384_);
v___x_1389_ = lean_box(v___x_1388_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1389_);
v___x_1391_ = v___x_1386_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
v_a_1394_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1383_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1383_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object* v_s_1402_, lean_object* v_opts_1403_, lean_object* v_json_1404_, lean_object* v_severityOverrides_1405_, lean_object* v_a_1406_){
_start:
{
uint8_t v_json_boxed_1407_; lean_object* v_res_1408_; 
v_json_boxed_1407_ = lean_unbox(v_json_1404_);
v_res_1408_ = l_Lean_Language_SnapshotTree_runAndReport(v_s_1402_, v_opts_1403_, v_json_boxed_1407_, v_severityOverrides_1405_);
lean_dec(v_severityOverrides_1405_);
lean_dec_ref(v_opts_1403_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(lean_object* v_s_1409_, lean_object* v_init_1410_){
_start:
{
lean_object* v_element_1411_; lean_object* v_children_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v_element_1411_ = lean_ctor_get(v_s_1409_, 0);
lean_inc_ref(v_element_1411_);
v_children_1412_ = lean_ctor_get(v_s_1409_, 1);
lean_inc_ref(v_children_1412_);
lean_dec_ref(v_s_1409_);
v___x_1413_ = lean_array_push(v_init_1410_, v_element_1411_);
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = lean_array_get_size(v_children_1412_);
v___x_1416_ = lean_nat_dec_lt(v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_dec_ref(v_children_1412_);
return v___x_1413_;
}
else
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = lean_usize_of_nat(v___x_1415_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_1412_, v___x_1417_, v___x_1418_, v___x_1413_);
lean_dec_ref(v_children_1412_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object* v_as_1420_, size_t v_i_1421_, size_t v_stop_1422_, lean_object* v_b_1423_){
_start:
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_usize_dec_eq(v_i_1421_, v_stop_1422_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; 
v___x_1425_ = lean_array_uget_borrowed(v_as_1420_, v_i_1421_);
lean_inc(v___x_1425_);
v___x_1426_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1425_);
v___x_1427_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v___x_1426_, v_b_1423_);
v___x_1428_ = ((size_t)1ULL);
v___x_1429_ = lean_usize_add(v_i_1421_, v___x_1428_);
v_i_1421_ = v___x_1429_;
v_b_1423_ = v___x_1427_;
goto _start;
}
else
{
return v_b_1423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object* v_as_1431_, lean_object* v_i_1432_, lean_object* v_stop_1433_, lean_object* v_b_1434_){
_start:
{
size_t v_i_boxed_1435_; size_t v_stop_boxed_1436_; lean_object* v_res_1437_; 
v_i_boxed_1435_ = lean_unbox_usize(v_i_1432_);
lean_dec(v_i_1432_);
v_stop_boxed_1436_ = lean_unbox_usize(v_stop_1433_);
lean_dec(v_stop_1433_);
v_res_1437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_as_1431_, v_i_boxed_1435_, v_stop_boxed_1436_, v_b_1434_);
lean_dec_ref(v_as_1431_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object* v_s_1440_){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = ((lean_object*)(l_Lean_Language_SnapshotTree_getAll___closed__0));
v___x_1442_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v_s_1440_, v___x_1441_);
return v___x_1442_;
}
}
static lean_object* _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0(void){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_task_pure(v___x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed(lean_object* v_tail_1445_, lean_object* v_t_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(v_tail_1445_, v_t_1446_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(lean_object* v_a_1449_){
_start:
{
if (lean_obj_tag(v_a_1449_) == 0)
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_obj_once(&l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0, &l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0_once, _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0);
return v___x_1451_;
}
else
{
lean_object* v_head_1452_; lean_object* v_tail_1453_; lean_object* v_task_1454_; lean_object* v___f_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; 
v_head_1452_ = lean_ctor_get(v_a_1449_, 0);
lean_inc(v_head_1452_);
v_tail_1453_ = lean_ctor_get(v_a_1449_, 1);
lean_inc(v_tail_1453_);
lean_dec_ref_known(v_a_1449_, 2);
v_task_1454_ = lean_ctor_get(v_head_1452_, 3);
lean_inc_ref(v_task_1454_);
lean_dec(v_head_1452_);
v___f_1455_ = lean_alloc_closure((void*)(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1455_, 0, v_tail_1453_);
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = 1;
v___x_1458_ = lean_io_bind_task(v_task_1454_, v___f_1455_, v___x_1456_, v___x_1457_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object* v_tail_1459_, lean_object* v_t_1460_){
_start:
{
lean_object* v_children_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_children_1462_ = lean_ctor_get(v_t_1460_, 1);
lean_inc_ref(v_children_1462_);
lean_dec_ref(v_t_1460_);
v___x_1463_ = lean_array_to_list(v_children_1462_);
v___x_1464_ = l_List_appendTR___redArg(v___x_1463_, v_tail_1459_);
v___x_1465_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___boxed(lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v_a_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object* v_x_1469_){
_start:
{
lean_object* v_children_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_children_1471_ = lean_ctor_get(v_x_1469_, 1);
lean_inc_ref(v_children_1471_);
lean_dec_ref(v_x_1469_);
v___x_1472_ = lean_array_to_list(v_children_1471_);
v___x_1473_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll___boxed(lean_object* v_x_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_Language_SnapshotTree_waitAll(v_x_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object* v_00_u03b1_1477_, lean_object* v_act_1478_, lean_object* v_ctx_1479_){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_apply_2(v_act_1478_, v_ctx_1479_, lean_box(0));
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_act_1484_, lean_object* v_ctx_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(v_00_u03b1_1483_, v_act_1484_, v_ctx_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object* v_msgLog_1490_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_st_mk_ref(v___x_1492_);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_msgLog_1490_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog___boxed(lean_object* v_msgLog_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1496_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object* v_msg_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_fileMap_1506_; lean_object* v_source_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_fileMap_1506_ = lean_ctor_get(v_a_1504_, 2);
v_source_1507_ = lean_ctor_get(v_fileMap_1506_, 0);
v___x_1508_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__0));
v___x_1509_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__1));
v___x_1510_ = lean_string_utf8_byte_size(v_source_1507_);
lean_inc_ref(v_fileMap_1506_);
v___x_1511_ = l_Lean_FileMap_toPosition(v_fileMap_1506_, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
v___x_1513_ = 0;
v___x_1514_ = 2;
v___x_1515_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot___closed__0));
v___x_1516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_msg_1503_);
v___x_1517_ = l_Lean_MessageData_ofFormat(v___x_1516_);
v___x_1518_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1518_, 0, v___x_1508_);
lean_ctor_set(v___x_1518_, 1, v___x_1509_);
lean_ctor_set(v___x_1518_, 2, v___x_1512_);
lean_ctor_set(v___x_1518_, 3, v___x_1515_);
lean_ctor_set(v___x_1518_, 4, v___x_1517_);
lean_ctor_set_uint8(v___x_1518_, sizeof(void*)*5, v___x_1513_);
lean_ctor_set_uint8(v___x_1518_, sizeof(void*)*5 + 1, v___x_1514_);
lean_ctor_set_uint8(v___x_1518_, sizeof(void*)*5 + 2, v___x_1513_);
v___x_1519_ = l_Lean_MessageLog_empty;
v___x_1520_ = l_Lean_MessageLog_add(v___x_1518_, v___x_1519_);
v___x_1521_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError___boxed(lean_object* v_msg_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Language_diagnosticsOfHeaderError(v_msg_1522_, v_a_1523_);
lean_dec_ref(v_a_1523_);
return v_res_1525_;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2(void){
_start:
{
uint8_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = 1;
v___x_1532_ = ((lean_object*)(l_Lean_Language_withHeaderExceptions___redArg___closed__1));
v___x_1533_ = l_Lean_Name_toString(v___x_1532_, v___x_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object* v_ex_1534_, lean_object* v_act_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v___x_1538_; 
lean_inc_ref(v_a_1536_);
v___x_1538_ = lean_apply_2(v_act_1535_, v_a_1536_, lean_box(0));
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; 
lean_dec(v_ex_1534_);
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
return v_a_1539_;
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_a_1540_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1541_ = lean_io_error_to_string(v_a_1540_);
v___x_1542_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_1541_, v_a_1536_);
v___x_1543_ = lean_obj_once(&l_Lean_Language_withHeaderExceptions___redArg___closed__2, &l_Lean_Language_withHeaderExceptions___redArg___closed__2_once, _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2);
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_1546_ = 0;
v___x_1547_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1547_, 0, v___x_1543_);
lean_ctor_set(v___x_1547_, 1, v___x_1542_);
lean_ctor_set(v___x_1547_, 2, v___x_1544_);
lean_ctor_set(v___x_1547_, 3, v___x_1545_);
lean_ctor_set_uint8(v___x_1547_, sizeof(void*)*4, v___x_1546_);
v___x_1548_ = lean_apply_1(v_ex_1534_, v___x_1547_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg___boxed(lean_object* v_ex_1549_, lean_object* v_act_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1549_, v_act_1550_, v_a_1551_);
lean_dec_ref(v_a_1551_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object* v_00_u03b1_1554_, lean_object* v_ex_1555_, lean_object* v_act_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1555_, v_act_1556_, v_a_1557_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___boxed(lean_object* v_00_u03b1_1560_, lean_object* v_ex_1561_, lean_object* v_act_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Language_withHeaderExceptions(v_00_u03b1_1560_, v_ex_1561_, v_act_1562_, v_a_1563_);
lean_dec_ref(v_a_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object* v_val_1566_, lean_object* v_process_1567_, lean_object* v_ictx_1568_){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1570_ = lean_st_ref_get(v_val_1566_);
v___x_1571_ = lean_apply_3(v_process_1567_, v___x_1570_, v_ictx_1568_, lean_box(0));
lean_inc(v___x_1571_);
v___x_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
v___x_1573_ = lean_st_ref_swap(v_val_1566_, v___x_1572_);
lean_dec(v___x_1573_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object* v_val_1574_, lean_object* v_process_1575_, lean_object* v_ictx_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(v_val_1574_, v_process_1575_, v_ictx_1576_);
lean_dec(v_val_1574_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object* v_process_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___f_1583_; 
v___x_1581_ = lean_box(0);
v___x_1582_ = lean_st_mk_ref(v___x_1581_);
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1583_, 0, v___x_1582_);
lean_closure_set(v___f_1583_, 1, v_process_1579_);
return v___f_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___boxed(lean_object* v_process_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object* v_InitSnap_1587_, lean_object* v_process_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___boxed(lean_object* v_InitSnap_1591_, lean_object* v_process_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Language_mkIncrementalProcessor(v_InitSnap_1591_, v_process_1592_);
return v_res_1594_;
}
}
lean_object* runtime_initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Trace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Language_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Basic(builtin);
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
lean_object* initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
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
res = initialize_Lean_Elab_InfoTree_Basic(builtin);
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
