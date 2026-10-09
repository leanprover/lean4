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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
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
lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object* v_stx_x3f_222_, lean_object* v_cancelTk_x3f_223_, lean_object* v_reportingRange_224_, lean_object* v_act_225_){
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
LEAN_EXPORT void l_Lean_Language_SnapshotTask_ofIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_x3f_222_ = stack[0].m_obj;
lean_object* v_cancelTk_x3f_223_ = stack[1].m_obj;
lean_object* v_reportingRange_224_ = stack[2].m_obj;
lean_object* v_act_225_ = stack[3].m_obj;
lean_object* v_res_230_;
v_res_230_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v_stx_x3f_222_, v_cancelTk_x3f_223_, v_reportingRange_224_, v_act_225_);
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg___boxed(lean_object* v_stx_x3f_231_, lean_object* v_cancelTk_x3f_232_, lean_object* v_reportingRange_233_, lean_object* v_act_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v_stx_x3f_231_, v_cancelTk_x3f_232_, v_reportingRange_233_, v_act_234_);
return v_res_236_;
}
}
lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object* v_00_u03b1_237_, lean_object* v_stx_x3f_238_, lean_object* v_cancelTk_x3f_239_, lean_object* v_reportingRange_240_, lean_object* v_act_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v_stx_x3f_238_, v_cancelTk_x3f_239_, v_reportingRange_240_, v_act_241_);
return v___x_243_;
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTask_ofIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_x3f_238_ = stack[1].m_obj;
lean_object* v_cancelTk_x3f_239_ = stack[2].m_obj;
lean_object* v_reportingRange_240_ = stack[3].m_obj;
lean_object* v_act_241_ = stack[4].m_obj;
lean_object* v_res_244_;
v_res_244_ = l_Lean_Language_SnapshotTask_ofIO(lean_box(0), v_stx_x3f_238_, v_cancelTk_x3f_239_, v_reportingRange_240_, v_act_241_);
stack->m_obj
 = v_res_244_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___boxed(lean_object* v_00_u03b1_245_, lean_object* v_stx_x3f_246_, lean_object* v_cancelTk_x3f_247_, lean_object* v_reportingRange_248_, lean_object* v_act_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Language_SnapshotTask_ofIO(v_00_u03b1_245_, v_stx_x3f_246_, v_cancelTk_x3f_247_, v_reportingRange_248_, v_act_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object* v_stx_x3f_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = lean_box(2);
v___x_255_ = lean_box(0);
v___x_256_ = lean_task_pure(v_a_253_);
v___x_257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_257_, 0, v_stx_x3f_252_);
lean_ctor_set(v___x_257_, 1, v___x_254_);
lean_ctor_set(v___x_257_, 2, v___x_255_);
lean_ctor_set(v___x_257_, 3, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished(lean_object* v_00_u03b1_258_, lean_object* v_stx_x3f_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Language_SnapshotTask_finished___redArg(v_stx_x3f_259_, v_a_260_);
return v___x_261_;
}
}
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object* v_t_262_, lean_object* v_f_263_, lean_object* v_stx_x3f_264_, lean_object* v_reportingRange_265_, uint8_t v_sync_266_){
_start:
{
lean_object* v_cancelTk_x3f_267_; lean_object* v_task_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_277_; 
v_cancelTk_x3f_267_ = lean_ctor_get(v_t_262_, 2);
v_task_268_ = lean_ctor_get(v_t_262_, 3);
v_isSharedCheck_277_ = !lean_is_exclusive(v_t_262_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; lean_object* v_unused_279_; 
v_unused_278_ = lean_ctor_get(v_t_262_, 1);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_t_262_, 0);
lean_dec(v_unused_279_);
v___x_270_ = v_t_262_;
v_isShared_271_ = v_isSharedCheck_277_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_task_268_);
lean_inc(v_cancelTk_x3f_267_);
lean_dec(v_t_262_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_277_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_task_map(v_f_263_, v_task_268_, v___x_272_, v_sync_266_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 3, v___x_273_);
lean_ctor_set(v___x_270_, 1, v_reportingRange_265_);
lean_ctor_set(v___x_270_, 0, v_stx_x3f_264_);
v___x_275_ = v___x_270_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_stx_x3f_264_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_reportingRange_265_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v_cancelTk_x3f_267_);
lean_ctor_set(v_reuseFailAlloc_276_, 3, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTask_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_262_ = stack[0].m_obj;
lean_object* v_f_263_ = stack[1].m_obj;
lean_object* v_stx_x3f_264_ = stack[2].m_obj;
lean_object* v_reportingRange_265_ = stack[3].m_obj;
uint8_t v_sync_266_ = stack[4].m_num;
lean_object* v_res_280_;
v_res_280_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_262_, v_f_263_, v_stx_x3f_264_, v_reportingRange_265_, v_sync_266_);
stack->m_obj
 = v_res_280_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg___boxed(lean_object* v_t_281_, lean_object* v_f_282_, lean_object* v_stx_x3f_283_, lean_object* v_reportingRange_284_, lean_object* v_sync_285_){
_start:
{
uint8_t v_sync_boxed_286_; lean_object* v_res_287_; 
v_sync_boxed_286_ = lean_unbox(v_sync_285_);
v_res_287_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_281_, v_f_282_, v_stx_x3f_283_, v_reportingRange_284_, v_sync_boxed_286_);
return v_res_287_;
}
}
lean_object* l_Lean_Language_SnapshotTask_map(lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_, lean_object* v_t_290_, lean_object* v_f_291_, lean_object* v_stx_x3f_292_, lean_object* v_reportingRange_293_, uint8_t v_sync_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_290_, v_f_291_, v_stx_x3f_292_, v_reportingRange_293_, v_sync_294_);
return v___x_295_;
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTask_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_290_ = stack[2].m_obj;
lean_object* v_f_291_ = stack[3].m_obj;
lean_object* v_stx_x3f_292_ = stack[4].m_obj;
lean_object* v_reportingRange_293_ = stack[5].m_obj;
uint8_t v_sync_294_ = stack[6].m_num;
lean_object* v_res_296_;
v_res_296_ = l_Lean_Language_SnapshotTask_map(lean_box(0), lean_box(0), v_t_290_, v_f_291_, v_stx_x3f_292_, v_reportingRange_293_, v_sync_294_);
stack->m_obj
 = v_res_296_;
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
lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(lean_object* v_act_306_, lean_object* v_a_307_){
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
LEAN_EXPORT void l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_306_ = stack[0].m_obj;
lean_object* v_a_307_ = stack[1].m_obj;
lean_object* v_res_311_;
v_res_311_ = l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(v_act_306_, v_a_307_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed(lean_object* v_act_312_, lean_object* v_a_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(v_act_312_, v_a_313_);
return v_res_315_;
}
}
lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object* v_t_316_, lean_object* v_act_317_, lean_object* v_stx_x3f_318_, lean_object* v_reportingRange_319_, lean_object* v_cancelTk_x3f_320_, uint8_t v_sync_321_){
_start:
{
lean_object* v_task_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_333_; 
v_task_323_ = lean_ctor_get(v_t_316_, 3);
v_isSharedCheck_333_ = !lean_is_exclusive(v_t_316_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; lean_object* v_unused_335_; lean_object* v_unused_336_; 
v_unused_334_ = lean_ctor_get(v_t_316_, 2);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_t_316_, 1);
lean_dec(v_unused_335_);
v_unused_336_ = lean_ctor_get(v_t_316_, 0);
lean_dec(v_unused_336_);
v___x_325_ = v_t_316_;
v_isShared_326_ = v_isSharedCheck_333_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_task_323_);
lean_dec(v_t_316_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_333_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___f_327_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_327_, 0, v_act_317_);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_io_bind_task(v_task_323_, v___f_327_, v___x_328_, v_sync_321_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 3, v___x_329_);
lean_ctor_set(v___x_325_, 2, v_cancelTk_x3f_320_);
lean_ctor_set(v___x_325_, 1, v_reportingRange_319_);
lean_ctor_set(v___x_325_, 0, v_stx_x3f_318_);
v___x_331_ = v___x_325_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_stx_x3f_318_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_reportingRange_319_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_cancelTk_x3f_320_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTask_bindIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_316_ = stack[0].m_obj;
lean_object* v_act_317_ = stack[1].m_obj;
lean_object* v_stx_x3f_318_ = stack[2].m_obj;
lean_object* v_reportingRange_319_ = stack[3].m_obj;
lean_object* v_cancelTk_x3f_320_ = stack[4].m_obj;
uint8_t v_sync_321_ = stack[5].m_num;
lean_object* v_res_337_;
v_res_337_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_t_316_, v_act_317_, v_stx_x3f_318_, v_reportingRange_319_, v_cancelTk_x3f_320_, v_sync_321_);
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___boxed(lean_object* v_t_338_, lean_object* v_act_339_, lean_object* v_stx_x3f_340_, lean_object* v_reportingRange_341_, lean_object* v_cancelTk_x3f_342_, lean_object* v_sync_343_, lean_object* v_a_344_){
_start:
{
uint8_t v_sync_boxed_345_; lean_object* v_res_346_; 
v_sync_boxed_345_ = lean_unbox(v_sync_343_);
v_res_346_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_t_338_, v_act_339_, v_stx_x3f_340_, v_reportingRange_341_, v_cancelTk_x3f_342_, v_sync_boxed_345_);
return v_res_346_;
}
}
lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object* v_00_u03b1_347_, lean_object* v_00_u03b2_348_, lean_object* v_t_349_, lean_object* v_act_350_, lean_object* v_stx_x3f_351_, lean_object* v_reportingRange_352_, lean_object* v_cancelTk_x3f_353_, uint8_t v_sync_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_t_349_, v_act_350_, v_stx_x3f_351_, v_reportingRange_352_, v_cancelTk_x3f_353_, v_sync_354_);
return v___x_356_;
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTask_bindIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_349_ = stack[2].m_obj;
lean_object* v_act_350_ = stack[3].m_obj;
lean_object* v_stx_x3f_351_ = stack[4].m_obj;
lean_object* v_reportingRange_352_ = stack[5].m_obj;
lean_object* v_cancelTk_x3f_353_ = stack[6].m_obj;
uint8_t v_sync_354_ = stack[7].m_num;
lean_object* v_res_357_;
v_res_357_ = l_Lean_Language_SnapshotTask_bindIO(lean_box(0), lean_box(0), v_t_349_, v_act_350_, v_stx_x3f_351_, v_reportingRange_352_, v_cancelTk_x3f_353_, v_sync_354_);
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___boxed(lean_object* v_00_u03b1_358_, lean_object* v_00_u03b2_359_, lean_object* v_t_360_, lean_object* v_act_361_, lean_object* v_stx_x3f_362_, lean_object* v_reportingRange_363_, lean_object* v_cancelTk_x3f_364_, lean_object* v_sync_365_, lean_object* v_a_366_){
_start:
{
uint8_t v_sync_boxed_367_; lean_object* v_res_368_; 
v_sync_boxed_367_ = lean_unbox(v_sync_365_);
v_res_368_ = l_Lean_Language_SnapshotTask_bindIO(v_00_u03b1_358_, v_00_u03b2_359_, v_t_360_, v_act_361_, v_stx_x3f_362_, v_reportingRange_363_, v_cancelTk_x3f_364_, v_sync_boxed_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object* v_t_369_){
_start:
{
lean_object* v_task_370_; lean_object* v___x_371_; 
v_task_370_ = lean_ctor_get(v_t_369_, 3);
lean_inc_ref(v_task_370_);
lean_dec_ref(v_t_369_);
v___x_371_ = lean_task_get_own(v_task_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object* v_00_u03b1_372_, lean_object* v_t_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Language_SnapshotTask_get___redArg(v_t_373_);
return v___x_374_;
}
}
lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object* v_t_375_){
_start:
{
lean_object* v_task_377_; uint8_t v___x_378_; 
v_task_377_ = lean_ctor_get(v_t_375_, 3);
lean_inc_ref(v_task_377_);
lean_dec_ref(v_t_375_);
v___x_378_ = lean_io_get_task_state(v_task_377_);
if (v___x_378_ == 2)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_task_get_own(v_task_377_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; 
lean_dec_ref(v_task_377_);
v___x_381_ = lean_box(0);
return v___x_381_;
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTask_get_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_375_ = stack[0].m_obj;
lean_object* v_res_382_;
v_res_382_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_375_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg___boxed(lean_object* v_t_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_383_);
return v_res_385_;
}
}
lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object* v_00_u03b1_386_, lean_object* v_t_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_387_);
return v___x_389_;
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTask_get_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_387_ = stack[1].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lean_Language_SnapshotTask_get_x3f(lean_box(0), v_t_387_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___boxed(lean_object* v_00_u03b1_391_, lean_object* v_t_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Language_SnapshotTask_get_x3f(v_00_u03b1_391_, v_t_392_);
return v_res_394_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshotTree_default___closed__0));
v___x_398_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_397_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default(void){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshotTree_default___closed__1, &l_Lean_Language_instInhabitedSnapshotTree_default___closed__1_once, _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree(void){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_401_;
}
}
uint8_t l_Lean_Language_SnapshotTreeTransform_isIdentity(lean_object* v_trans_415_){
_start:
{
lean_object* v_startPos_416_; lean_object* v_stopPos_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_startPos_416_ = lean_ctor_get(v_trans_415_, 1);
v_stopPos_417_ = lean_ctor_get(v_trans_415_, 2);
v___x_418_ = lean_nat_sub(v_stopPos_417_, v_startPos_416_);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_nat_dec_eq(v___x_418_, v___x_419_);
lean_dec(v___x_418_);
return v___x_420_;
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTreeTransform_isIdentity_0interp(lean_interpreter_value* stack)
{
lean_object* v_trans_415_ = stack[0].m_obj;
uint8_t v_res_421_;
v_res_421_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_trans_415_);
stack->m_num = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_isIdentity___boxed(lean_object* v_trans_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_trans_422_);
lean_dec_ref(v_trans_422_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformSyntax(lean_object* v_trans_425_, lean_object* v_stx_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Syntax_addTrailing(v_stx_426_, v_trans_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformInfoTree(lean_object* v_trans_428_, lean_object* v_t_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Elab_InfoTree_addTrailing(v_trans_428_, v_t_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformInfoTree_x3f(lean_object* v_trans_431_, lean_object* v_t_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Elab_InfoTree_addTrailing_x3f(v_trans_431_, v_t_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_compose(lean_object* v_outer_434_, lean_object* v_inner_435_){
_start:
{
lean_object* v_str_436_; lean_object* v_startPos_437_; lean_object* v_stopPos_438_; lean_object* v_startPos_439_; lean_object* v_stopPos_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
v_str_436_ = lean_ctor_get(v_inner_435_, 0);
v_startPos_437_ = lean_ctor_get(v_inner_435_, 1);
v_stopPos_438_ = lean_ctor_get(v_inner_435_, 2);
v_startPos_439_ = lean_ctor_get(v_outer_434_, 1);
v_stopPos_440_ = lean_ctor_get(v_outer_434_, 2);
v_isSharedCheck_448_ = !lean_is_exclusive(v_outer_434_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v_outer_434_, 0);
lean_dec(v_unused_449_);
v___x_442_ = v_outer_434_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_stopPos_440_);
lean_inc(v_startPos_439_);
lean_dec(v_outer_434_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
uint8_t v_decide_444_; 
v_decide_444_ = lean_nat_dec_eq(v_stopPos_438_, v_startPos_439_);
lean_dec(v_startPos_439_);
if (v_decide_444_ == 0)
{
lean_del_object(v___x_442_);
lean_dec(v_stopPos_440_);
lean_inc_ref(v_inner_435_);
return v_inner_435_;
}
else
{
lean_object* v___x_446_; 
lean_inc(v_startPos_437_);
lean_inc_ref(v_str_436_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v_startPos_437_);
lean_ctor_set(v___x_442_, 0, v_str_436_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_str_436_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_startPos_437_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_stopPos_440_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_compose___boxed(lean_object* v_outer_450_, lean_object* v_inner_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Language_SnapshotTreeTransform_compose(v_outer_450_, v_inner_451_);
lean_dec_ref(v_inner_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_transform(lean_object* v_s_453_, lean_object* v_a_454_){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_a_454_);
if (v___x_455_ == 0)
{
lean_object* v_infoTree_x3f_456_; 
v_infoTree_x3f_456_ = lean_ctor_get(v_s_453_, 2);
if (lean_obj_tag(v_infoTree_x3f_456_) == 0)
{
return v_s_453_;
}
else
{
lean_object* v_desc_457_; lean_object* v_diagnostics_458_; lean_object* v_traces_459_; uint8_t v_isFatal_460_; lean_object* v_val_461_; lean_object* v___x_462_; 
v_desc_457_ = lean_ctor_get(v_s_453_, 0);
v_diagnostics_458_ = lean_ctor_get(v_s_453_, 1);
v_traces_459_ = lean_ctor_get(v_s_453_, 3);
v_isFatal_460_ = lean_ctor_get_uint8(v_s_453_, sizeof(void*)*4);
v_val_461_ = lean_ctor_get(v_infoTree_x3f_456_, 0);
lean_inc(v_val_461_);
lean_inc_ref(v_a_454_);
v___x_462_ = l_Lean_Elab_InfoTree_addTrailing_x3f(v_a_454_, v_val_461_);
if (lean_obj_tag(v___x_462_) == 0)
{
return v_s_453_;
}
else
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_inc_ref(v_traces_459_);
lean_inc_ref(v_diagnostics_458_);
lean_inc_ref(v_desc_457_);
v_isSharedCheck_469_ = !lean_is_exclusive(v_s_453_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; 
v_unused_470_ = lean_ctor_get(v_s_453_, 3);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_s_453_, 2);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_s_453_, 1);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_s_453_, 0);
lean_dec(v_unused_473_);
v___x_464_ = v_s_453_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_dec(v_s_453_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 2, v___x_462_);
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_desc_457_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_diagnostics_458_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_traces_459_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, sizeof(void*)*4, v_isFatal_460_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
else
{
return v_s_453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_transform___boxed(lean_object* v_s_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Language_Snapshot_transform(v_s_474_, v_a_475_);
lean_dec_ref(v_a_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0___boxed(lean_object* v_a_477_, lean_object* v_x_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0(v_a_477_, v_x_478_);
lean_dec_ref(v_a_477_);
return v_res_479_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(lean_object* v_a_480_, size_t v_sz_481_, size_t v_i_482_, lean_object* v_bs_483_){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = lean_usize_dec_lt(v_i_482_, v_sz_481_);
if (v___x_484_ == 0)
{
return v_bs_483_;
}
else
{
lean_object* v_v_485_; lean_object* v_stx_x3f_486_; lean_object* v_reportingRange_487_; lean_object* v___f_488_; lean_object* v___x_489_; lean_object* v_bs_x27_490_; lean_object* v___x_491_; size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v_v_485_ = lean_array_uget(v_bs_483_, v_i_482_);
v_stx_x3f_486_ = lean_ctor_get(v_v_485_, 0);
lean_inc(v_stx_x3f_486_);
v_reportingRange_487_ = lean_ctor_get(v_v_485_, 1);
lean_inc(v_reportingRange_487_);
lean_inc_ref(v_a_480_);
v___f_488_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_488_, 0, v_a_480_);
v___x_489_ = lean_unsigned_to_nat(0u);
v_bs_x27_490_ = lean_array_uset(v_bs_483_, v_i_482_, v___x_489_);
v___x_491_ = l_Lean_Language_SnapshotTask_map___redArg(v_v_485_, v___f_488_, v_stx_x3f_486_, v_reportingRange_487_, v___x_484_);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_482_, v___x_492_);
v___x_494_ = lean_array_uset(v_bs_x27_490_, v_i_482_, v___x_491_);
v_i_482_ = v___x_493_;
v_bs_483_ = v___x_494_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_480_ = stack[0].m_obj;
size_t v_sz_481_ = stack[1].m_num;
size_t v_i_482_ = stack[2].m_num;
lean_object* v_bs_483_ = stack[3].m_obj;
lean_object* v_res_496_;
v_res_496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(v_a_480_, v_sz_481_, v_i_482_, v_bs_483_);
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_transform(lean_object* v_t_497_, lean_object* v_a_498_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_a_498_);
if (v___x_499_ == 0)
{
lean_object* v_element_500_; lean_object* v_children_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_512_; 
v_element_500_ = lean_ctor_get(v_t_497_, 0);
v_children_501_ = lean_ctor_get(v_t_497_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_t_497_);
if (v_isSharedCheck_512_ == 0)
{
v___x_503_ = v_t_497_;
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_children_501_);
lean_inc(v_element_500_);
lean_dec(v_t_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_505_ = l_Lean_Language_Snapshot_transform(v_element_500_, v_a_498_);
v_sz_506_ = lean_array_size(v_children_501_);
v___x_507_ = ((size_t)0ULL);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(v_a_498_, v_sz_506_, v___x_507_, v_children_501_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_508_);
lean_ctor_set(v___x_503_, 0, v___x_505_);
v___x_510_ = v___x_503_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
return v_t_497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0(lean_object* v_a_513_, lean_object* v_x_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Language_SnapshotTree_transform(v_x_514_, v_a_513_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object* v_t_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Language_SnapshotTree_transform(v_t_516_, v_a_517_);
lean_dec_ref(v_a_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___boxed(lean_object* v_a_519_, lean_object* v_sz_520_, lean_object* v_i_521_, lean_object* v_bs_522_){
_start:
{
size_t v_sz_boxed_523_; size_t v_i_boxed_524_; lean_object* v_res_525_; 
v_sz_boxed_523_ = lean_unbox_usize(v_sz_520_);
lean_dec(v_sz_520_);
v_i_boxed_524_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(v_a_519_, v_sz_boxed_523_, v_i_boxed_524_, v_bs_522_);
lean_dec_ref(v_a_519_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___redArg(lean_object* v_inst_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshotTreeTransform_default));
v___x_529_ = lean_apply_2(v_inst_526_, v_a_527_, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree(lean_object* v_00_u03b1_530_, lean_object* v_inst_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Language_toSnapshotTree___redArg(v_inst_531_, v_a_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedTransformedSnap___redArg(lean_object* v_inst_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshotTreeTransform_default));
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_inst_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedTransformedSnap(lean_object* v_00_u03b1_537_, lean_object* v_inst_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Language_instInhabitedTransformedSnap___redArg(v_inst_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0(lean_object* v_inst_540_, lean_object* v_s_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_raw_543_; lean_object* v_transform_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_raw_543_ = lean_ctor_get(v_s_541_, 0);
lean_inc(v_raw_543_);
v_transform_544_ = lean_ctor_get(v_s_541_, 1);
lean_inc_ref(v_transform_544_);
lean_dec_ref(v_s_541_);
lean_inc_ref(v___y_542_);
v___x_545_ = l_Lean_Language_SnapshotTreeTransform_compose(v___y_542_, v_transform_544_);
lean_dec_ref(v_transform_544_);
v___x_546_ = lean_apply_2(v_inst_540_, v_raw_543_, v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed(lean_object* v_inst_547_, lean_object* v_s_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0(v_inst_547_, v_s_548_, v___y_549_);
lean_dec_ref(v___y_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg(lean_object* v_inst_551_){
_start:
{
lean_object* v___f_552_; 
v___f_552_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_552_, 0, v_inst_551_);
return v___f_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap(lean_object* v_00_u03b1_553_, lean_object* v_inst_554_){
_start:
{
lean_object* v___f_555_; 
v___f_555_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_555_, 0, v_inst_554_);
return v___f_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_TransformedSnap_compose___redArg(lean_object* v_outer_556_, lean_object* v_s_557_){
_start:
{
lean_object* v_raw_558_; lean_object* v_transform_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_raw_558_ = lean_ctor_get(v_s_557_, 0);
v_transform_559_ = lean_ctor_get(v_s_557_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_s_557_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v_s_557_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_transform_559_);
lean_inc(v_raw_558_);
lean_dec(v_s_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = l_Lean_Language_SnapshotTreeTransform_compose(v_outer_556_, v_transform_559_);
lean_dec_ref(v_transform_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_raw_558_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_TransformedSnap_compose(lean_object* v_00_u03b1_568_, lean_object* v_outer_569_, lean_object* v_s_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Language_TransformedSnap_compose___redArg(v_outer_569_, v_s_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0(lean_object* v_f_572_, lean_object* v_a_573_, lean_object* v_x_574_){
_start:
{
lean_object* v___x_575_; 
lean_inc_ref(v_a_573_);
v___x_575_ = lean_apply_2(v_f_572_, v_x_574_, v_a_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0___boxed(lean_object* v_f_576_, lean_object* v_a_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0(v_f_576_, v_a_577_, v_x_578_);
lean_dec_ref(v_a_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object* v_t_580_, lean_object* v_f_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_stx_x3f_583_; lean_object* v_reportingRange_584_; lean_object* v___f_585_; uint8_t v___x_586_; lean_object* v___x_587_; 
v_stx_x3f_583_ = lean_ctor_get(v_t_580_, 0);
lean_inc(v_stx_x3f_583_);
v_reportingRange_584_ = lean_ctor_get(v_t_580_, 1);
lean_inc(v_reportingRange_584_);
lean_inc_ref(v_a_582_);
v___f_585_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_585_, 0, v_f_581_);
lean_closure_set(v___f_585_, 1, v_a_582_);
v___x_586_ = 1;
v___x_587_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_580_, v___f_585_, v_stx_x3f_583_, v_reportingRange_584_, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___boxed(lean_object* v_t_588_, lean_object* v_f_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_588_, v_f_589_, v_a_590_);
lean_dec_ref(v_a_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith(lean_object* v_00_u03b1_592_, lean_object* v_t_593_, lean_object* v_f_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_593_, v_f_594_, v_a_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___boxed(lean_object* v_00_u03b1_597_, lean_object* v_t_598_, lean_object* v_f_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Language_SnapshotTask_transformWith(v_00_u03b1_597_, v_t_598_, v_f_599_, v_a_600_);
lean_dec_ref(v_a_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___redArg(lean_object* v_inst_602_, lean_object* v_t_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_603_, v_inst_602_, v_a_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___redArg___boxed(lean_object* v_inst_606_, lean_object* v_t_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Language_SnapshotTask_transform___redArg(v_inst_606_, v_t_607_, v_a_608_);
lean_dec_ref(v_a_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform(lean_object* v_00_u03b1_610_, lean_object* v_inst_611_, lean_object* v_t_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_612_, v_inst_611_, v_a_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___boxed(lean_object* v_00_u03b1_615_, lean_object* v_inst_616_, lean_object* v_t_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Language_SnapshotTask_transform(v_00_u03b1_615_, v_inst_616_, v_t_617_, v_a_618_);
lean_dec_ref(v_a_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object* v_inst_622_, lean_object* v_x_623_, lean_object* v___y_624_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
lean_object* v___x_625_; 
lean_dec_ref(v_inst_622_);
v___x_625_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_625_;
}
else
{
lean_object* v_val_626_; lean_object* v___x_627_; 
v_val_626_ = lean_ctor_get(v_x_623_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v_x_623_, 1);
lean_inc_ref(v___y_624_);
v___x_627_ = lean_apply_2(v_inst_622_, v_val_626_, v___y_624_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed(lean_object* v_inst_628_, lean_object* v_x_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(v_inst_628_, v_x_629_, v___y_630_);
lean_dec_ref(v___y_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg(lean_object* v_inst_632_){
_start:
{
lean_object* v___f_633_; 
v___f_633_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_633_, 0, v_inst_632_);
return v___f_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object* v_00_u03b1_634_, lean_object* v_inst_635_){
_start:
{
lean_object* v___f_636_; 
v___f_636_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_636_, 0, v_inst_635_);
return v___f_636_;
}
}
lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(lean_object* v_inst_637_, lean_object* v___x_638_, lean_object* v___f_639_, lean_object* v_snap_640_){
_start:
{
lean_object* v___x_642_; lean_object* v_children_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_642_ = l_Lean_Language_toSnapshotTree___redArg(v_inst_637_, v_snap_640_);
v_children_643_ = lean_ctor_get(v___x_642_, 1);
lean_inc_ref(v_children_643_);
lean_dec_ref(v___x_642_);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_array_get_size(v_children_643_);
v___x_646_ = lean_box(0);
v___x_647_ = lean_nat_dec_lt(v___x_644_, v___x_645_);
if (v___x_647_ == 0)
{
lean_dec_ref(v_children_643_);
lean_dec_ref(v___f_639_);
lean_dec_ref(v___x_638_);
return v___x_646_;
}
else
{
uint8_t v___x_648_; 
v___x_648_ = lean_nat_dec_le(v___x_645_, v___x_645_);
if (v___x_648_ == 0)
{
if (v___x_647_ == 0)
{
lean_dec_ref(v_children_643_);
lean_dec_ref(v___f_639_);
lean_dec_ref(v___x_638_);
return v___x_646_;
}
else
{
size_t v___x_649_; size_t v___x_650_; lean_object* v___x_205__overap_651_; lean_object* v___x_652_; 
v___x_649_ = ((size_t)0ULL);
v___x_650_ = lean_usize_of_nat(v___x_645_);
v___x_205__overap_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_638_, v___f_639_, v_children_643_, v___x_649_, v___x_650_, v___x_646_);
v___x_652_ = lean_apply_1(v___x_205__overap_651_, lean_box(0));
return v___x_652_;
}
}
else
{
size_t v___x_653_; size_t v___x_654_; lean_object* v___x_208__overap_655_; lean_object* v___x_656_; 
v___x_653_ = ((size_t)0ULL);
v___x_654_ = lean_usize_of_nat(v___x_645_);
v___x_208__overap_655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_638_, v___f_639_, v_children_643_, v___x_653_, v___x_654_, v___x_646_);
v___x_656_ = lean_apply_1(v___x_208__overap_655_, lean_box(0));
return v___x_656_;
}
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_637_ = stack[0].m_obj;
lean_object* v___x_638_ = stack[1].m_obj;
lean_object* v___f_639_ = stack[2].m_obj;
lean_object* v_snap_640_ = stack[3].m_obj;
lean_object* v_res_657_;
v_res_657_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(v_inst_637_, v___x_638_, v___f_639_, v_snap_640_);
stack->m_obj
 = v_res_657_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed(lean_object* v_inst_658_, lean_object* v___x_659_, lean_object* v___f_660_, lean_object* v_snap_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(v_inst_658_, v___x_659_, v___f_660_, v_snap_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(lean_object* v___f_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(v___f_664_, v_x_665_, v___y_666_);
return v_res_668_;
}
}
lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object* v_inst_669_, lean_object* v_t_670_){
_start:
{
lean_object* v___x_672_; lean_object* v_cancelTk_x3f_673_; lean_object* v_task_674_; lean_object* v___f_675_; lean_object* v___f_676_; lean_object* v___f_677_; 
v___x_672_ = l_instMonadBaseIO;
v_cancelTk_x3f_673_ = lean_ctor_get(v_t_670_, 2);
lean_inc(v_cancelTk_x3f_673_);
v_task_674_ = lean_ctor_get(v_t_670_, 3);
lean_inc_ref(v_task_674_);
lean_dec_ref(v_t_670_);
v___f_675_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0));
v___f_676_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_676_, 0, v___f_675_);
v___f_677_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_677_, 0, v_inst_669_);
lean_closure_set(v___f_677_, 1, v___x_672_);
lean_closure_set(v___f_677_, 2, v___f_676_);
if (lean_obj_tag(v_cancelTk_x3f_673_) == 1)
{
lean_object* v_val_682_; lean_object* v___x_683_; 
v_val_682_ = lean_ctor_get(v_cancelTk_x3f_673_, 0);
lean_inc(v_val_682_);
lean_dec_ref_known(v_cancelTk_x3f_673_, 1);
v___x_683_ = l_IO_CancelToken_set(v_val_682_);
lean_dec(v_val_682_);
goto v___jp_678_;
}
else
{
lean_dec(v_cancelTk_x3f_673_);
goto v___jp_678_;
}
v___jp_678_:
{
lean_object* v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = 1;
v___x_681_ = l_BaseIO_chainTask___redArg(v_task_674_, v___f_677_, v___x_679_, v___x_680_);
return v___x_681_;
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTask_cancelRec___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_669_ = stack[0].m_obj;
lean_object* v_t_670_ = stack[1].m_obj;
lean_object* v_res_684_;
v_res_684_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_669_, v_t_670_);
stack->m_obj
 = v_res_684_;
}
lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object* v___f_685_, lean_object* v_x_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_685_, v___y_687_);
return v___x_689_;
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_685_ = stack[0].m_obj;
lean_object* v_x_686_ = stack[1].m_obj;
lean_object* v___y_687_ = stack[2].m_obj;
lean_object* v_res_690_;
v_res_690_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(v___f_685_, v_x_686_, v___y_687_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___boxed(lean_object* v_inst_691_, lean_object* v_t_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_691_, v_t_692_);
return v_res_694_;
}
}
lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object* v_00_u03b1_695_, lean_object* v_inst_696_, lean_object* v_t_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_696_, v_t_697_);
return v___x_699_;
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTask_cancelRec_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_696_ = stack[1].m_obj;
lean_object* v_t_697_ = stack[2].m_obj;
lean_object* v_res_700_;
v_res_700_ = l_Lean_Language_SnapshotTask_cancelRec(lean_box(0), v_inst_696_, v_t_697_);
stack->m_obj
 = v_res_700_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___boxed(lean_object* v_00_u03b1_701_, lean_object* v_inst_702_, lean_object* v_t_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Language_SnapshotTask_cancelRec(v_00_u03b1_701_, v_inst_702_, v_t_703_);
return v_res_705_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotLeaf(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = lean_unsigned_to_nat(32u);
v___x_714_ = lean_mk_empty_array_with_capacity(v___x_713_);
lean_dec_ref(v___x_714_);
v___x_715_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object* v_s_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = l_Lean_Language_Snapshot_transform(v_s_718_, v___y_719_);
v___x_721_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0));
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___boxed(lean_object* v_s_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(v_s_723_, v___y_724_);
lean_dec_ref(v___y_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object* v_s_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_toSnapshotTreeM_730_; lean_object* v___x_731_; 
v_toSnapshotTreeM_730_ = lean_ctor_get(v_s_728_, 1);
lean_inc_ref(v_toSnapshotTreeM_730_);
lean_dec_ref(v_s_728_);
lean_inc_ref(v___y_729_);
v___x_731_ = lean_apply_1(v_toSnapshotTreeM_730_, v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object* v_s_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(v_s_732_, v___y_733_);
lean_dec_ref(v___y_733_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_val_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_inc(v_val_739_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_inst_737_);
lean_ctor_set(v___x_740_, 1, v_val_739_);
v___x_741_ = lean_apply_1(v_inst_738_, v_val_739_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object* v_00_u03b1_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_val_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v_inst_744_, v_inst_745_, v_val_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object* v_inst_748_, lean_object* v_snap_749_){
_start:
{
lean_object* v_val_750_; lean_object* v___x_751_; 
v_val_750_ = lean_ctor_get(v_snap_749_, 0);
v___x_751_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_750_, v_inst_748_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object* v_inst_752_, lean_object* v_snap_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_752_, v_snap_753_);
lean_dec_ref(v_snap_753_);
lean_dec(v_inst_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object* v_00_u03b1_755_, lean_object* v_inst_756_, lean_object* v_snap_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_756_, v_snap_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object* v_00_u03b1_759_, lean_object* v_inst_760_, lean_object* v_snap_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f(v_00_u03b1_759_, v_inst_760_, v_snap_761_);
lean_dec_ref(v_snap_761_);
lean_dec(v_inst_760_);
return v_res_762_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2(void){
_start:
{
uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = 1;
v___x_769_ = ((lean_object*)(l_Lean_Language_instInhabitedDynamicSnapshot___closed__1));
v___x_770_ = l_Lean_Name_toString(v___x_769_, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3(void){
_start:
{
uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_771_ = 0;
v___x_772_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_773_ = lean_box(0);
v___x_774_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_775_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__2, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__2_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2);
v___x_776_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_774_);
lean_ctor_set(v___x_776_, 2, v___x_773_);
lean_ctor_set(v___x_776_, 3, v___x_772_);
lean_ctor_set_uint8(v___x_776_, sizeof(void*)*4, v___x_771_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4(void){
_start:
{
lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_777_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__3, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3);
v___f_778_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0));
v___x_779_ = ((lean_object*)(l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_));
v___x_780_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v___x_779_, v___f_778_, v___x_777_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot(void){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__4, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object* v_toApplicative_782_, lean_object* v_children_783_, lean_object* v_inst_784_, lean_object* v___f_785_, lean_object* v_____r_786_){
_start:
{
lean_object* v_toPure_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_toPure_787_ = lean_ctor_get(v_toApplicative_782_, 1);
lean_inc(v_toPure_787_);
lean_dec_ref(v_toApplicative_782_);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = lean_array_get_size(v_children_783_);
v___x_790_ = lean_box(0);
v___x_791_ = lean_nat_dec_lt(v___x_788_, v___x_789_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
lean_dec(v___f_785_);
lean_dec_ref(v_inst_784_);
lean_dec_ref(v_children_783_);
v___x_792_ = lean_apply_2(v_toPure_787_, lean_box(0), v___x_790_);
return v___x_792_;
}
else
{
uint8_t v___x_793_; 
v___x_793_ = lean_nat_dec_le(v___x_789_, v___x_789_);
if (v___x_793_ == 0)
{
if (v___x_791_ == 0)
{
lean_object* v___x_794_; 
lean_dec(v___f_785_);
lean_dec_ref(v_inst_784_);
lean_dec_ref(v_children_783_);
v___x_794_ = lean_apply_2(v_toPure_787_, lean_box(0), v___x_790_);
return v___x_794_;
}
else
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
lean_dec(v_toPure_787_);
v___x_795_ = ((size_t)0ULL);
v___x_796_ = lean_usize_of_nat(v___x_789_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_784_, v___f_785_, v_children_783_, v___x_795_, v___x_796_, v___x_790_);
return v___x_797_;
}
}
else
{
size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
lean_dec(v_toPure_787_);
v___x_798_ = ((size_t)0ULL);
v___x_799_ = lean_usize_of_nat(v___x_789_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_784_, v___f_785_, v_children_783_, v___x_798_, v___x_799_, v___x_790_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object* v_inst_801_, lean_object* v_s_802_, lean_object* v_f_803_){
_start:
{
lean_object* v_toApplicative_804_; lean_object* v_toBind_805_; lean_object* v_element_806_; lean_object* v_children_807_; lean_object* v___f_808_; lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_toApplicative_804_ = lean_ctor_get(v_inst_801_, 0);
lean_inc_ref(v_toApplicative_804_);
v_toBind_805_ = lean_ctor_get(v_inst_801_, 1);
lean_inc(v_toBind_805_);
v_element_806_ = lean_ctor_get(v_s_802_, 0);
lean_inc_ref(v_element_806_);
v_children_807_ = lean_ctor_get(v_s_802_, 1);
lean_inc_ref(v_children_807_);
lean_dec_ref(v_s_802_);
lean_inc(v_f_803_);
lean_inc_ref(v_inst_801_);
v___f_808_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_808_, 0, v_inst_801_);
lean_closure_set(v___f_808_, 1, v_f_803_);
v___f_809_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_809_, 0, v_toApplicative_804_);
lean_closure_set(v___f_809_, 1, v_children_807_);
lean_closure_set(v___f_809_, 2, v_inst_801_);
lean_closure_set(v___f_809_, 3, v___f_808_);
v___x_810_ = lean_apply_1(v_f_803_, v_element_806_);
v___x_811_ = lean_apply_4(v_toBind_805_, lean_box(0), lean_box(0), v___x_810_, v___f_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object* v_inst_812_, lean_object* v_f_813_, lean_object* v_x_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = l_Lean_Language_SnapshotTask_get___redArg(v___y_815_);
v___x_817_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_812_, v___x_816_, v_f_813_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object* v_m_818_, lean_object* v_inst_819_, lean_object* v_s_820_, lean_object* v_f_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_819_, v_s_820_, v_f_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object* v_toApplicative_823_, lean_object* v_children_824_, lean_object* v_inst_825_, lean_object* v___f_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_toPure_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_toPure_828_ = lean_ctor_get(v_toApplicative_823_, 1);
lean_inc(v_toPure_828_);
lean_dec_ref(v_toApplicative_823_);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_array_get_size(v_children_824_);
v___x_831_ = lean_nat_dec_lt(v___x_829_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec(v___f_826_);
lean_dec_ref(v_inst_825_);
lean_dec_ref(v_children_824_);
v___x_832_ = lean_apply_2(v_toPure_828_, lean_box(0), v_a_827_);
return v___x_832_;
}
else
{
uint8_t v___x_833_; 
v___x_833_ = lean_nat_dec_le(v___x_830_, v___x_830_);
if (v___x_833_ == 0)
{
if (v___x_831_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v___f_826_);
lean_dec_ref(v_inst_825_);
lean_dec_ref(v_children_824_);
v___x_834_ = lean_apply_2(v_toPure_828_, lean_box(0), v_a_827_);
return v___x_834_;
}
else
{
size_t v___x_835_; size_t v___x_836_; lean_object* v___x_837_; 
lean_dec(v_toPure_828_);
v___x_835_ = ((size_t)0ULL);
v___x_836_ = lean_usize_of_nat(v___x_830_);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_825_, v___f_826_, v_children_824_, v___x_835_, v___x_836_, v_a_827_);
return v___x_837_;
}
}
else
{
size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; 
lean_dec(v_toPure_828_);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = lean_usize_of_nat(v___x_830_);
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_825_, v___f_826_, v_children_824_, v___x_838_, v___x_839_, v_a_827_);
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object* v_inst_841_, lean_object* v_s_842_, lean_object* v_f_843_, lean_object* v_init_844_){
_start:
{
lean_object* v_toApplicative_845_; lean_object* v_toBind_846_; lean_object* v_element_847_; lean_object* v_children_848_; lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_toApplicative_845_ = lean_ctor_get(v_inst_841_, 0);
lean_inc_ref(v_toApplicative_845_);
v_toBind_846_ = lean_ctor_get(v_inst_841_, 1);
lean_inc(v_toBind_846_);
v_element_847_ = lean_ctor_get(v_s_842_, 0);
lean_inc_ref(v_element_847_);
v_children_848_ = lean_ctor_get(v_s_842_, 1);
lean_inc_ref(v_children_848_);
lean_dec_ref(v_s_842_);
lean_inc(v_f_843_);
lean_inc_ref(v_inst_841_);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_849_, 0, v_inst_841_);
lean_closure_set(v___f_849_, 1, v_f_843_);
v___f_850_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_850_, 0, v_toApplicative_845_);
lean_closure_set(v___f_850_, 1, v_children_848_);
lean_closure_set(v___f_850_, 2, v_inst_841_);
lean_closure_set(v___f_850_, 3, v___f_849_);
v___x_851_ = lean_apply_2(v_f_843_, v_init_844_, v_element_847_);
v___x_852_ = lean_apply_4(v_toBind_846_, lean_box(0), lean_box(0), v___x_851_, v___f_850_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object* v_inst_853_, lean_object* v_f_854_, lean_object* v_a_855_, lean_object* v_snap_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = l_Lean_Language_SnapshotTask_get___redArg(v_snap_856_);
v___x_858_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_853_, v___x_857_, v_f_854_, v_a_855_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object* v_m_859_, lean_object* v_00_u03b1_860_, lean_object* v_inst_861_, lean_object* v_s_862_, lean_object* v_f_863_, lean_object* v_init_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_861_, v_s_862_, v_f_863_, v_init_864_);
return v___x_865_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(lean_object* v_name_866_, lean_object* v_decl_867_, lean_object* v_ref_868_){
_start:
{
lean_object* v_defValue_870_; lean_object* v_descr_871_; lean_object* v_deprecation_x3f_872_; lean_object* v___x_873_; uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_defValue_870_ = lean_ctor_get(v_decl_867_, 0);
v_descr_871_ = lean_ctor_get(v_decl_867_, 1);
v_deprecation_x3f_872_ = lean_ctor_get(v_decl_867_, 2);
v___x_873_ = lean_alloc_ctor(1, 0, 1);
v___x_874_ = lean_unbox(v_defValue_870_);
lean_ctor_set_uint8(v___x_873_, 0, v___x_874_);
lean_inc(v_deprecation_x3f_872_);
lean_inc_ref(v_descr_871_);
lean_inc_n(v_name_866_, 2);
v___x_875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_875_, 0, v_name_866_);
lean_ctor_set(v___x_875_, 1, v_ref_868_);
lean_ctor_set(v___x_875_, 2, v___x_873_);
lean_ctor_set(v___x_875_, 3, v_descr_871_);
lean_ctor_set(v___x_875_, 4, v_deprecation_x3f_872_);
v___x_876_ = lean_register_option(v_name_866_, v___x_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_884_; 
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v___x_876_, 0);
lean_dec(v_unused_885_);
v___x_878_ = v___x_876_;
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
else
{
lean_dec(v___x_876_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
lean_inc(v_defValue_870_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_name_866_);
lean_ctor_set(v___x_880_, 1, v_defValue_870_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_880_);
v___x_882_ = v___x_878_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_name_866_);
v_a_886_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_876_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_876_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_866_ = stack[0].m_obj;
lean_object* v_decl_867_ = stack[1].m_obj;
lean_object* v_ref_868_ = stack[2].m_obj;
lean_object* v_res_894_;
v_res_894_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v_name_866_, v_decl_867_, v_ref_868_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_895_, lean_object* v_decl_896_, lean_object* v_ref_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v_name_895_, v_decl_896_, v_ref_897_);
lean_dec_ref(v_decl_896_);
return v_res_899_;
}
}
lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_914_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_915_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_916_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_917_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v___x_914_, v___x_915_, v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT void l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_918_;
v_res_918_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
stack->m_obj
 = v_res_918_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4____boxed(lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
return v_res_920_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(lean_object* v_name_921_, lean_object* v_decl_922_, lean_object* v_ref_923_){
_start:
{
lean_object* v_defValue_925_; lean_object* v_descr_926_; lean_object* v_deprecation_x3f_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_defValue_925_ = lean_ctor_get(v_decl_922_, 0);
v_descr_926_ = lean_ctor_get(v_decl_922_, 1);
v_deprecation_x3f_927_ = lean_ctor_get(v_decl_922_, 2);
lean_inc(v_defValue_925_);
v___x_928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_928_, 0, v_defValue_925_);
lean_inc(v_deprecation_x3f_927_);
lean_inc_ref(v_descr_926_);
lean_inc_n(v_name_921_, 2);
v___x_929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_929_, 0, v_name_921_);
lean_ctor_set(v___x_929_, 1, v_ref_923_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
lean_ctor_set(v___x_929_, 3, v_descr_926_);
lean_ctor_set(v___x_929_, 4, v_deprecation_x3f_927_);
v___x_930_ = lean_register_option(v_name_921_, v___x_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_938_; 
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v___x_930_, 0);
lean_dec(v_unused_939_);
v___x_932_ = v___x_930_;
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
else
{
lean_dec(v___x_930_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
lean_inc(v_defValue_925_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_name_921_);
lean_ctor_set(v___x_934_, 1, v_defValue_925_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_934_);
v___x_936_ = v___x_932_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_name_921_);
v_a_940_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_930_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_930_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_921_ = stack[0].m_obj;
lean_object* v_decl_922_ = stack[1].m_obj;
lean_object* v_ref_923_ = stack[2].m_obj;
lean_object* v_res_948_;
v_res_948_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v_name_921_, v_decl_922_, v_ref_923_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_949_, lean_object* v_decl_950_, lean_object* v_ref_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v_name_949_, v_decl_950_, v_ref_951_);
lean_dec_ref(v_decl_950_);
return v_res_953_;
}
}
lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_967_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_968_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_969_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_970_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v___x_967_, v___x_968_, v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT void l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_971_;
v_res_971_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
stack->m_obj
 = v_res_971_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4____boxed(lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
return v_res_973_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(lean_object* v_opts_974_, lean_object* v_opt_975_){
_start:
{
lean_object* v_name_976_; lean_object* v_defValue_977_; lean_object* v_map_978_; lean_object* v___x_979_; 
v_name_976_ = lean_ctor_get(v_opt_975_, 0);
v_defValue_977_ = lean_ctor_get(v_opt_975_, 1);
v_map_978_ = lean_ctor_get(v_opts_974_, 0);
v___x_979_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_978_, v_name_976_);
if (lean_obj_tag(v___x_979_) == 0)
{
uint8_t v___x_980_; 
v___x_980_ = lean_unbox(v_defValue_977_);
return v___x_980_;
}
else
{
lean_object* v_val_981_; 
v_val_981_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_val_981_);
lean_dec_ref_known(v___x_979_, 1);
if (lean_obj_tag(v_val_981_) == 1)
{
uint8_t v_v_982_; 
v_v_982_ = lean_ctor_get_uint8(v_val_981_, 0);
lean_dec_ref_known(v_val_981_, 0);
return v_v_982_;
}
else
{
uint8_t v___x_983_; 
lean_dec(v_val_981_);
v___x_983_ = lean_unbox(v_defValue_977_);
return v___x_983_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_974_ = stack[0].m_obj;
lean_object* v_opt_975_ = stack[1].m_obj;
uint8_t v_res_984_;
v_res_984_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_974_, v_opt_975_);
stack->m_num = v_res_984_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0___boxed(lean_object* v_opts_985_, lean_object* v_opt_986_){
_start:
{
uint8_t v_res_987_; lean_object* v_r_988_; 
v_res_987_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_985_, v_opt_986_);
lean_dec_ref(v_opt_986_);
lean_dec_ref(v_opts_985_);
v_r_988_ = lean_box(v_res_987_);
return v_r_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(lean_object* v_opts_989_, lean_object* v_opt_990_){
_start:
{
lean_object* v_name_991_; lean_object* v_defValue_992_; lean_object* v_map_993_; lean_object* v___x_994_; 
v_name_991_ = lean_ctor_get(v_opt_990_, 0);
v_defValue_992_ = lean_ctor_get(v_opt_990_, 1);
v_map_993_ = lean_ctor_get(v_opts_989_, 0);
v___x_994_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_993_, v_name_991_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_inc(v_defValue_992_);
return v_defValue_992_;
}
else
{
lean_object* v_val_995_; 
v_val_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v___x_994_, 1);
if (lean_obj_tag(v_val_995_) == 3)
{
lean_object* v_v_996_; 
v_v_996_ = lean_ctor_get(v_val_995_, 0);
lean_inc(v_v_996_);
lean_dec_ref_known(v_val_995_, 1);
return v_v_996_;
}
else
{
lean_dec(v_val_995_);
lean_inc(v_defValue_992_);
return v_defValue_992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1___boxed(lean_object* v_opts_997_, lean_object* v_opt_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_997_, v_opt_998_);
lean_dec_ref(v_opt_998_);
lean_dec_ref(v_opts_997_);
return v_res_999_;
}
}
lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(lean_object* v_s_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v_putStr_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_get_stdout();
v_putStr_1003_ = lean_ctor_get(v___x_1002_, 4);
lean_inc_ref(v_putStr_1003_);
lean_dec_ref(v___x_1002_);
v___x_1004_ = lean_apply_2(v_putStr_1003_, v_s_1000_, lean_box(0));
return v___x_1004_;
}
}
LEAN_EXPORT void l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1000_ = stack[0].m_obj;
lean_object* v_res_1005_;
v_res_1005_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v_s_1000_);
stack->m_obj
 = v_res_1005_;
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2___boxed(lean_object* v_s_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v_s_1006_);
return v_res_1008_;
}
}
lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object* v_s_1009_){
_start:
{
uint32_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = 10;
v___x_1012_ = lean_string_push(v_s_1009_, v___x_1011_);
v___x_1013_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT void l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1009_ = stack[0].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v_s_1009_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3___boxed(lean_object* v_s_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v_s_1015_);
return v_res_1017_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(lean_object* v_opts_1020_, uint8_t v_json_1021_, uint8_t v_includeEndPos_1022_, lean_object* v_severityOverrides_1023_, lean_object* v_as_1024_, size_t v_i_1025_, size_t v_stop_1026_, lean_object* v_b_1027_){
_start:
{
lean_object* v_a_1030_; lean_object* v___y_1035_; uint8_t v___y_1036_; uint8_t v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; uint8_t v_isSilent_1051_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; uint8_t v___y_1077_; uint8_t v___x_1101_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1112_; uint8_t v_severity_1113_; 
v___x_1101_ = lean_usize_dec_eq(v_i_1025_, v_stop_1026_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1116_; lean_object* v_fileName_1117_; lean_object* v_pos_1118_; lean_object* v_endPos_1119_; uint8_t v_keepFullRange_1120_; uint8_t v_isSilent_1121_; lean_object* v_caption_1122_; lean_object* v_data_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1116_ = lean_array_uget(v_as_1024_, v_i_1025_);
v_fileName_1117_ = lean_ctor_get(v___x_1116_, 0);
v_pos_1118_ = lean_ctor_get(v___x_1116_, 1);
v_endPos_1119_ = lean_ctor_get(v___x_1116_, 2);
v_keepFullRange_1120_ = lean_ctor_get_uint8(v___x_1116_, sizeof(void*)*5);
v_isSilent_1121_ = lean_ctor_get_uint8(v___x_1116_, sizeof(void*)*5 + 2);
v_caption_1122_ = lean_ctor_get(v___x_1116_, 3);
v_data_1123_ = lean_ctor_get(v___x_1116_, 4);
v___x_1124_ = l_Lean_MessageData_kind(v_data_1123_);
v___x_1125_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_severityOverrides_1023_, v___x_1124_);
lean_dec(v___x_1124_);
if (lean_obj_tag(v___x_1125_) == 1)
{
lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1135_; 
lean_inc(v_data_1123_);
lean_inc_ref(v_caption_1122_);
lean_inc(v_endPos_1119_);
lean_inc_ref(v_pos_1118_);
lean_inc_ref(v_fileName_1117_);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; lean_object* v_unused_1137_; lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; 
v_unused_1136_ = lean_ctor_get(v___x_1116_, 4);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v___x_1116_, 3);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v___x_1116_, 2);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v___x_1116_, 1);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v___x_1116_, 0);
lean_dec(v_unused_1140_);
v___x_1127_ = v___x_1116_;
v_isShared_1128_ = v_isSharedCheck_1135_;
goto v_resetjp_1126_;
}
else
{
lean_dec(v___x_1116_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1135_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_val_1129_; lean_object* v___x_1131_; 
v_val_1129_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_val_1129_);
lean_dec_ref_known(v___x_1125_, 1);
if (v_isShared_1128_ == 0)
{
v___x_1131_ = v___x_1127_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_fileName_1117_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_pos_1118_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_endPos_1119_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_caption_1122_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v_data_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*5, v_keepFullRange_1120_);
v___x_1131_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
uint8_t v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_unbox(v_val_1129_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*5 + 1, v___x_1132_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*5 + 2, v_isSilent_1121_);
v___x_1133_ = lean_unbox(v_val_1129_);
lean_dec(v_val_1129_);
v___y_1112_ = v___x_1131_;
v_severity_1113_ = v___x_1133_;
goto v___jp_1111_;
}
}
}
else
{
uint8_t v_severity_1141_; 
lean_dec(v___x_1125_);
v_severity_1141_ = lean_ctor_get_uint8(v___x_1116_, sizeof(void*)*5 + 1);
v___y_1112_ = v___x_1116_;
v_severity_1113_ = v_severity_1141_;
goto v___jp_1111_;
}
}
else
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_b_1027_);
return v___x_1142_;
}
v___jp_1029_:
{
size_t v___x_1031_; size_t v___x_1032_; 
v___x_1031_ = ((size_t)1ULL);
v___x_1032_ = lean_usize_add(v_i_1025_, v___x_1031_);
v_i_1025_ = v___x_1032_;
v_b_1027_ = v_a_1030_;
goto _start;
}
v___jp_1034_:
{
if (v___y_1036_ == 0)
{
v_a_1030_ = v___y_1035_;
goto v___jp_1029_;
}
else
{
uint8_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = 1;
v___x_1038_ = lean_io_exit(v___x_1037_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_dec_ref_known(v___x_1038_, 1);
v_a_1030_ = v___y_1035_;
goto v___jp_1029_;
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v___y_1035_);
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
v___jp_1047_:
{
if (v_isSilent_1051_ == 0)
{
if (v_json_1021_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = l_Lean_Message_toString(v___y_1050_, v_includeEndPos_1022_);
v___x_1053_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_1052_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_dec_ref_known(v___x_1053_, 1);
v___y_1035_ = v___y_1049_;
v___y_1036_ = v___y_1048_;
goto v___jp_1034_;
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec(v___y_1049_);
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = l_Lean_Message_toJson(v___y_1050_);
v___x_1063_ = l_Lean_Json_compress(v___x_1062_);
v___x_1064_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_dec_ref_known(v___x_1064_, 1);
v___y_1035_ = v___y_1049_;
v___y_1036_ = v___y_1048_;
goto v___jp_1034_;
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v___y_1049_);
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1050_);
v___y_1035_ = v___y_1049_;
v___y_1036_ = v___y_1048_;
goto v___jp_1034_;
}
}
v___jp_1073_:
{
if (v___y_1077_ == 0)
{
uint8_t v_isSilent_1078_; 
lean_dec(v___y_1076_);
v_isSilent_1078_ = lean_ctor_get_uint8(v___y_1074_, sizeof(void*)*5 + 2);
v___y_1048_ = v___y_1077_;
v___y_1049_ = v___y_1075_;
v___y_1050_ = v___y_1074_;
v_isSilent_1051_ = v_isSilent_1078_;
goto v___jp_1047_;
}
else
{
lean_object* v_fileName_1079_; lean_object* v_pos_1080_; lean_object* v_endPos_1081_; uint8_t v_keepFullRange_1082_; uint8_t v_isSilent_1083_; lean_object* v_caption_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1099_; 
v_fileName_1079_ = lean_ctor_get(v___y_1074_, 0);
v_pos_1080_ = lean_ctor_get(v___y_1074_, 1);
v_endPos_1081_ = lean_ctor_get(v___y_1074_, 2);
v_keepFullRange_1082_ = lean_ctor_get_uint8(v___y_1074_, sizeof(void*)*5);
v_isSilent_1083_ = lean_ctor_get_uint8(v___y_1074_, sizeof(void*)*5 + 2);
v_caption_1084_ = lean_ctor_get(v___y_1074_, 3);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___y_1074_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v___y_1074_, 4);
lean_dec(v_unused_1100_);
v___x_1086_ = v___y_1074_;
v_isShared_1087_ = v_isSharedCheck_1099_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_caption_1084_);
lean_inc(v_endPos_1081_);
lean_inc(v_pos_1080_);
lean_inc(v_fileName_1079_);
lean_dec(v___y_1074_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1099_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1088_ = 2;
v___x_1089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0));
v___x_1090_ = l_Nat_reprFast(v___y_1076_);
v___x_1091_ = lean_string_append(v___x_1089_, v___x_1090_);
lean_dec_ref(v___x_1090_);
v___x_1092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1));
v___x_1093_ = lean_string_append(v___x_1091_, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
v___x_1095_ = l_Lean_MessageData_ofFormat(v___x_1094_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 4, v___x_1095_);
v___x_1097_ = v___x_1086_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_fileName_1079_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_pos_1080_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_endPos_1081_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_caption_1084_);
lean_ctor_set(v_reuseFailAlloc_1098_, 4, v___x_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*5, v_keepFullRange_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*5 + 2, v_isSilent_1083_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*5 + 1, v___x_1088_);
v___y_1048_ = v___y_1077_;
v___y_1049_ = v___y_1075_;
v___y_1050_ = v___x_1097_;
v_isSilent_1051_ = v_isSilent_1083_;
goto v___jp_1047_;
}
}
}
}
v___jp_1102_:
{
lean_object* v_numErrors_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v_numErrors_1105_ = lean_nat_add(v_b_1027_, v___y_1104_);
lean_dec(v_b_1027_);
v___x_1106_ = l_Lean_Language_maxErrors;
v___x_1107_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_1020_, v___x_1106_);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_nat_dec_eq(v___x_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_nat_dec_lt(v___x_1107_, v_numErrors_1105_);
v___y_1074_ = v___y_1103_;
v___y_1075_ = v_numErrors_1105_;
v___y_1076_ = v___x_1107_;
v___y_1077_ = v___x_1110_;
goto v___jp_1073_;
}
else
{
v___y_1074_ = v___y_1103_;
v___y_1075_ = v_numErrors_1105_;
v___y_1076_ = v___x_1107_;
v___y_1077_ = v___x_1101_;
goto v___jp_1073_;
}
}
v___jp_1111_:
{
if (v_severity_1113_ == 2)
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_unsigned_to_nat(1u);
v___y_1103_ = v___y_1112_;
v___y_1104_ = v___x_1114_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_unsigned_to_nat(0u);
v___y_1103_ = v___y_1112_;
v___y_1104_ = v___x_1115_;
goto v___jp_1102_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1020_ = stack[0].m_obj;
uint8_t v_json_1021_ = stack[1].m_num;
uint8_t v_includeEndPos_1022_ = stack[2].m_num;
lean_object* v_severityOverrides_1023_ = stack[3].m_obj;
lean_object* v_as_1024_ = stack[4].m_obj;
size_t v_i_1025_ = stack[5].m_num;
size_t v_stop_1026_ = stack[6].m_num;
lean_object* v_b_1027_ = stack[7].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1020_, v_json_1021_, v_includeEndPos_1022_, v_severityOverrides_1023_, v_as_1024_, v_i_1025_, v_stop_1026_, v_b_1027_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___boxed(lean_object* v_opts_1144_, lean_object* v_json_1145_, lean_object* v_includeEndPos_1146_, lean_object* v_severityOverrides_1147_, lean_object* v_as_1148_, lean_object* v_i_1149_, lean_object* v_stop_1150_, lean_object* v_b_1151_, lean_object* v___y_1152_){
_start:
{
uint8_t v_json_boxed_1153_; uint8_t v_includeEndPos_boxed_1154_; size_t v_i_boxed_1155_; size_t v_stop_boxed_1156_; lean_object* v_res_1157_; 
v_json_boxed_1153_ = lean_unbox(v_json_1145_);
v_includeEndPos_boxed_1154_ = lean_unbox(v_includeEndPos_1146_);
v_i_boxed_1155_ = lean_unbox_usize(v_i_1149_);
lean_dec(v_i_1149_);
v_stop_boxed_1156_ = lean_unbox_usize(v_stop_1150_);
lean_dec(v_stop_1150_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1144_, v_json_boxed_1153_, v_includeEndPos_boxed_1154_, v_severityOverrides_1147_, v_as_1148_, v_i_boxed_1155_, v_stop_boxed_1156_, v_b_1151_);
lean_dec_ref(v_as_1148_);
lean_dec(v_severityOverrides_1147_);
lean_dec_ref(v_opts_1144_);
return v_res_1157_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(lean_object* v_opts_1158_, uint8_t v_json_1159_, uint8_t v_includeEndPos_1160_, lean_object* v_severityOverrides_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_){
_start:
{
if (lean_obj_tag(v_x_1162_) == 0)
{
lean_object* v_cs_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1178_; 
v_cs_1165_ = lean_ctor_get(v_x_1162_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1167_ = v_x_1162_;
v_isShared_1168_ = v_isSharedCheck_1178_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_cs_1165_);
lean_dec(v_x_1162_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1178_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = lean_unsigned_to_nat(0u);
v___x_1170_ = lean_array_get_size(v_cs_1165_);
v___x_1171_ = lean_nat_dec_lt(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1173_; 
lean_dec_ref(v_cs_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v_x_1163_);
v___x_1173_ = v___x_1167_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_x_1163_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
else
{
size_t v___x_1175_; size_t v___x_1176_; lean_object* v___x_1177_; 
lean_del_object(v___x_1167_);
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = lean_usize_of_nat(v___x_1170_);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1158_, v_json_1159_, v_includeEndPos_1160_, v_severityOverrides_1161_, v_cs_1165_, v___x_1175_, v___x_1176_, v_x_1163_);
lean_dec_ref(v_cs_1165_);
return v___x_1177_;
}
}
}
else
{
lean_object* v_vs_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1192_; 
v_vs_1179_ = lean_ctor_get(v_x_1162_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1181_ = v_x_1162_;
v_isShared_1182_ = v_isSharedCheck_1192_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_vs_1179_);
lean_dec(v_x_1162_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1192_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = lean_array_get_size(v_vs_1179_);
v___x_1185_ = lean_nat_dec_lt(v___x_1183_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1187_; 
lean_dec_ref(v_vs_1179_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set_tag(v___x_1181_, 0);
lean_ctor_set(v___x_1181_, 0, v_x_1163_);
v___x_1187_ = v___x_1181_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_x_1163_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
else
{
size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
lean_del_object(v___x_1181_);
v___x_1189_ = ((size_t)0ULL);
v___x_1190_ = lean_usize_of_nat(v___x_1184_);
v___x_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1158_, v_json_1159_, v_includeEndPos_1160_, v_severityOverrides_1161_, v_vs_1179_, v___x_1189_, v___x_1190_, v_x_1163_);
lean_dec_ref(v_vs_1179_);
return v___x_1191_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1158_ = stack[0].m_obj;
uint8_t v_json_1159_ = stack[1].m_num;
uint8_t v_includeEndPos_1160_ = stack[2].m_num;
lean_object* v_severityOverrides_1161_ = stack[3].m_obj;
lean_object* v_x_1162_ = stack[4].m_obj;
lean_object* v_x_1163_ = stack[5].m_obj;
lean_object* v_res_1193_;
v_res_1193_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1158_, v_json_1159_, v_includeEndPos_1160_, v_severityOverrides_1161_, v_x_1162_, v_x_1163_);
stack->m_obj
 = v_res_1193_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(lean_object* v_opts_1194_, uint8_t v_json_1195_, uint8_t v_includeEndPos_1196_, lean_object* v_severityOverrides_1197_, lean_object* v_as_1198_, size_t v_i_1199_, size_t v_stop_1200_, lean_object* v_b_1201_){
_start:
{
uint8_t v___x_1203_; 
v___x_1203_ = lean_usize_dec_eq(v_i_1199_, v_stop_1200_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_array_uget_borrowed(v_as_1198_, v_i_1199_);
lean_inc(v___x_1204_);
v___x_1205_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1194_, v_json_1195_, v_includeEndPos_1196_, v_severityOverrides_1197_, v___x_1204_, v_b_1201_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; size_t v___x_1207_; size_t v___x_1208_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1205_, 1);
v___x_1207_ = ((size_t)1ULL);
v___x_1208_ = lean_usize_add(v_i_1199_, v___x_1207_);
v_i_1199_ = v___x_1208_;
v_b_1201_ = v_a_1206_;
goto _start;
}
else
{
return v___x_1205_;
}
}
else
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_b_1201_);
return v___x_1210_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1194_ = stack[0].m_obj;
uint8_t v_json_1195_ = stack[1].m_num;
uint8_t v_includeEndPos_1196_ = stack[2].m_num;
lean_object* v_severityOverrides_1197_ = stack[3].m_obj;
lean_object* v_as_1198_ = stack[4].m_obj;
size_t v_i_1199_ = stack[5].m_num;
size_t v_stop_1200_ = stack[6].m_num;
lean_object* v_b_1201_ = stack[7].m_obj;
lean_object* v_res_1211_;
v_res_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1194_, v_json_1195_, v_includeEndPos_1196_, v_severityOverrides_1197_, v_as_1198_, v_i_1199_, v_stop_1200_, v_b_1201_);
stack->m_obj
 = v_res_1211_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5___boxed(lean_object* v_opts_1212_, lean_object* v_json_1213_, lean_object* v_includeEndPos_1214_, lean_object* v_severityOverrides_1215_, lean_object* v_as_1216_, lean_object* v_i_1217_, lean_object* v_stop_1218_, lean_object* v_b_1219_, lean_object* v___y_1220_){
_start:
{
uint8_t v_json_boxed_1221_; uint8_t v_includeEndPos_boxed_1222_; size_t v_i_boxed_1223_; size_t v_stop_boxed_1224_; lean_object* v_res_1225_; 
v_json_boxed_1221_ = lean_unbox(v_json_1213_);
v_includeEndPos_boxed_1222_ = lean_unbox(v_includeEndPos_1214_);
v_i_boxed_1223_ = lean_unbox_usize(v_i_1217_);
lean_dec(v_i_1217_);
v_stop_boxed_1224_ = lean_unbox_usize(v_stop_1218_);
lean_dec(v_stop_1218_);
v_res_1225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1212_, v_json_boxed_1221_, v_includeEndPos_boxed_1222_, v_severityOverrides_1215_, v_as_1216_, v_i_boxed_1223_, v_stop_boxed_1224_, v_b_1219_);
lean_dec_ref(v_as_1216_);
lean_dec(v_severityOverrides_1215_);
lean_dec_ref(v_opts_1212_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6___boxed(lean_object* v_opts_1226_, lean_object* v_json_1227_, lean_object* v_includeEndPos_1228_, lean_object* v_severityOverrides_1229_, lean_object* v_x_1230_, lean_object* v_x_1231_, lean_object* v___y_1232_){
_start:
{
uint8_t v_json_boxed_1233_; uint8_t v_includeEndPos_boxed_1234_; lean_object* v_res_1235_; 
v_json_boxed_1233_ = lean_unbox(v_json_1227_);
v_includeEndPos_boxed_1234_ = lean_unbox(v_includeEndPos_1228_);
v_res_1235_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1226_, v_json_boxed_1233_, v_includeEndPos_boxed_1234_, v_severityOverrides_1229_, v_x_1230_, v_x_1231_);
lean_dec(v_severityOverrides_1229_);
lean_dec_ref(v_opts_1226_);
return v_res_1235_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1236_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(lean_object* v_opts_1237_, uint8_t v_json_1238_, uint8_t v_includeEndPos_1239_, lean_object* v_severityOverrides_1240_, lean_object* v_x_1241_, size_t v_x_1242_, size_t v_x_1243_, lean_object* v_x_1244_){
_start:
{
if (lean_obj_tag(v_x_1241_) == 0)
{
lean_object* v_cs_1246_; lean_object* v___x_1247_; size_t v___x_1248_; lean_object* v_j_1249_; lean_object* v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; 
v_cs_1246_ = lean_ctor_get(v_x_1241_, 0);
lean_inc_ref(v_cs_1246_);
lean_dec_ref_known(v_x_1241_, 1);
v___x_1247_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0);
v___x_1248_ = lean_usize_shift_right(v_x_1242_, v_x_1243_);
v_j_1249_ = lean_usize_to_nat(v___x_1248_);
v___x_1250_ = lean_array_get_borrowed(v___x_1247_, v_cs_1246_, v_j_1249_);
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = lean_usize_shift_left(v___x_1251_, v_x_1243_);
v___x_1253_ = lean_usize_sub(v___x_1252_, v___x_1251_);
v___x_1254_ = lean_usize_land(v_x_1242_, v___x_1253_);
v___x_1255_ = ((size_t)5ULL);
v___x_1256_ = lean_usize_sub(v_x_1243_, v___x_1255_);
lean_inc(v___x_1250_);
v___x_1257_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1237_, v_json_1238_, v_includeEndPos_1239_, v_severityOverrides_1240_, v___x_1250_, v___x_1254_, v___x_1256_, v_x_1244_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_add(v_j_1249_, v___x_1259_);
lean_dec(v_j_1249_);
v___x_1261_ = lean_array_get_size(v_cs_1246_);
v___x_1262_ = lean_nat_dec_lt(v___x_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_dec(v___x_1260_);
lean_dec_ref(v_cs_1246_);
return v___x_1257_;
}
else
{
size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; 
lean_inc(v_a_1258_);
lean_dec_ref_known(v___x_1257_, 1);
v___x_1263_ = lean_usize_of_nat(v___x_1260_);
lean_dec(v___x_1260_);
v___x_1264_ = lean_usize_of_nat(v___x_1261_);
v___x_1265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1237_, v_json_1238_, v_includeEndPos_1239_, v_severityOverrides_1240_, v_cs_1246_, v___x_1263_, v___x_1264_, v_a_1258_);
lean_dec_ref(v_cs_1246_);
return v___x_1265_;
}
}
else
{
lean_dec(v_j_1249_);
lean_dec_ref(v_cs_1246_);
return v___x_1257_;
}
}
else
{
lean_object* v_vs_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1279_; 
v_vs_1266_ = lean_ctor_get(v_x_1241_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_x_1241_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1268_ = v_x_1241_;
v_isShared_1269_ = v_isSharedCheck_1279_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_vs_1266_);
lean_dec(v_x_1241_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1279_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1270_ = lean_usize_to_nat(v_x_1242_);
v___x_1271_ = lean_array_get_size(v_vs_1266_);
v___x_1272_ = lean_nat_dec_lt(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1274_; 
lean_dec(v___x_1270_);
lean_dec_ref(v_vs_1266_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 0);
lean_ctor_set(v___x_1268_, 0, v_x_1244_);
v___x_1274_ = v___x_1268_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_x_1244_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
else
{
size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
lean_del_object(v___x_1268_);
v___x_1276_ = lean_usize_of_nat(v___x_1270_);
lean_dec(v___x_1270_);
v___x_1277_ = lean_usize_of_nat(v___x_1271_);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1237_, v_json_1238_, v_includeEndPos_1239_, v_severityOverrides_1240_, v_vs_1266_, v___x_1276_, v___x_1277_, v_x_1244_);
lean_dec_ref(v_vs_1266_);
return v___x_1278_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1237_ = stack[0].m_obj;
uint8_t v_json_1238_ = stack[1].m_num;
uint8_t v_includeEndPos_1239_ = stack[2].m_num;
lean_object* v_severityOverrides_1240_ = stack[3].m_obj;
lean_object* v_x_1241_ = stack[4].m_obj;
size_t v_x_1242_ = stack[5].m_num;
size_t v_x_1243_ = stack[6].m_num;
lean_object* v_x_1244_ = stack[7].m_obj;
lean_object* v_res_1280_;
v_res_1280_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1237_, v_json_1238_, v_includeEndPos_1239_, v_severityOverrides_1240_, v_x_1241_, v_x_1242_, v_x_1243_, v_x_1244_);
stack->m_obj
 = v_res_1280_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___boxed(lean_object* v_opts_1281_, lean_object* v_json_1282_, lean_object* v_includeEndPos_1283_, lean_object* v_severityOverrides_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v_json_boxed_1290_; uint8_t v_includeEndPos_boxed_1291_; size_t v_x_2389__boxed_1292_; size_t v_x_2390__boxed_1293_; lean_object* v_res_1294_; 
v_json_boxed_1290_ = lean_unbox(v_json_1282_);
v_includeEndPos_boxed_1291_ = lean_unbox(v_includeEndPos_1283_);
v_x_2389__boxed_1292_ = lean_unbox_usize(v_x_1286_);
lean_dec(v_x_1286_);
v_x_2390__boxed_1293_ = lean_unbox_usize(v_x_1287_);
lean_dec(v_x_1287_);
v_res_1294_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1281_, v_json_boxed_1290_, v_includeEndPos_boxed_1291_, v_severityOverrides_1284_, v_x_1285_, v_x_2389__boxed_1292_, v_x_2390__boxed_1293_, v_x_1288_);
lean_dec(v_severityOverrides_1284_);
lean_dec_ref(v_opts_1281_);
return v_res_1294_;
}
}
lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(lean_object* v_opts_1295_, uint8_t v_json_1296_, uint8_t v_includeEndPos_1297_, lean_object* v_severityOverrides_1298_, lean_object* v_t_1299_, lean_object* v_init_1300_, lean_object* v_start_1301_){
_start:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = lean_nat_dec_eq(v_start_1301_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v_root_1305_; lean_object* v_tail_1306_; size_t v_shift_1307_; lean_object* v_tailOff_1308_; uint8_t v___x_1309_; 
v_root_1305_ = lean_ctor_get(v_t_1299_, 0);
lean_inc_ref(v_root_1305_);
v_tail_1306_ = lean_ctor_get(v_t_1299_, 1);
lean_inc_ref(v_tail_1306_);
v_shift_1307_ = lean_ctor_get_usize(v_t_1299_, 4);
v_tailOff_1308_ = lean_ctor_get(v_t_1299_, 3);
lean_inc(v_tailOff_1308_);
lean_dec_ref(v_t_1299_);
v___x_1309_ = lean_nat_dec_le(v_tailOff_1308_, v_start_1301_);
if (v___x_1309_ == 0)
{
size_t v___x_1310_; lean_object* v___x_1311_; 
lean_dec(v_tailOff_1308_);
v___x_1310_ = lean_usize_of_nat(v_start_1301_);
v___x_1311_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1295_, v_json_1296_, v_includeEndPos_1297_, v_severityOverrides_1298_, v_root_1305_, v___x_1310_, v_shift_1307_, v_init_1300_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v___x_1313_ = lean_array_get_size(v_tail_1306_);
v___x_1314_ = lean_nat_dec_lt(v___x_1303_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_dec_ref(v_tail_1306_);
return v___x_1311_;
}
else
{
size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = lean_usize_of_nat(v___x_1313_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1295_, v_json_1296_, v_includeEndPos_1297_, v_severityOverrides_1298_, v_tail_1306_, v___x_1315_, v___x_1316_, v_a_1312_);
lean_dec_ref(v_tail_1306_);
return v___x_1317_;
}
}
else
{
lean_dec_ref(v_tail_1306_);
return v___x_1311_;
}
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
lean_dec_ref(v_root_1305_);
v___x_1318_ = lean_nat_sub(v_start_1301_, v_tailOff_1308_);
lean_dec(v_tailOff_1308_);
v___x_1319_ = lean_array_get_size(v_tail_1306_);
v___x_1320_ = lean_nat_dec_lt(v___x_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
lean_dec(v___x_1318_);
lean_dec_ref(v_tail_1306_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_init_1300_);
return v___x_1321_;
}
else
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = lean_usize_of_nat(v___x_1318_);
lean_dec(v___x_1318_);
v___x_1323_ = lean_usize_of_nat(v___x_1319_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1295_, v_json_1296_, v_includeEndPos_1297_, v_severityOverrides_1298_, v_tail_1306_, v___x_1322_, v___x_1323_, v_init_1300_);
lean_dec_ref(v_tail_1306_);
return v___x_1324_;
}
}
}
else
{
lean_object* v_root_1325_; lean_object* v_tail_1326_; lean_object* v___x_1327_; 
v_root_1325_ = lean_ctor_get(v_t_1299_, 0);
lean_inc_ref(v_root_1325_);
v_tail_1326_ = lean_ctor_get(v_t_1299_, 1);
lean_inc_ref(v_tail_1326_);
lean_dec_ref(v_t_1299_);
v___x_1327_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1295_, v_json_1296_, v_includeEndPos_1297_, v_severityOverrides_1298_, v_root_1325_, v_init_1300_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v___x_1329_ = lean_array_get_size(v_tail_1326_);
v___x_1330_ = lean_nat_dec_lt(v___x_1303_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_dec_ref(v_tail_1326_);
return v___x_1327_;
}
else
{
size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1331_ = ((size_t)0ULL);
v___x_1332_ = lean_usize_of_nat(v___x_1329_);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1295_, v_json_1296_, v_includeEndPos_1297_, v_severityOverrides_1298_, v_tail_1326_, v___x_1331_, v___x_1332_, v_a_1328_);
lean_dec_ref(v_tail_1326_);
return v___x_1333_;
}
}
else
{
lean_dec_ref(v_tail_1326_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1295_ = stack[0].m_obj;
uint8_t v_json_1296_ = stack[1].m_num;
uint8_t v_includeEndPos_1297_ = stack[2].m_num;
lean_object* v_severityOverrides_1298_ = stack[3].m_obj;
lean_object* v_t_1299_ = stack[4].m_obj;
lean_object* v_init_1300_ = stack[5].m_obj;
lean_object* v_start_1301_ = stack[6].m_obj;
lean_object* v_res_1334_;
v_res_1334_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1295_, v_json_1296_, v_includeEndPos_1297_, v_severityOverrides_1298_, v_t_1299_, v_init_1300_, v_start_1301_);
stack->m_obj
 = v_res_1334_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4___boxed(lean_object* v_opts_1335_, lean_object* v_json_1336_, lean_object* v_includeEndPos_1337_, lean_object* v_severityOverrides_1338_, lean_object* v_t_1339_, lean_object* v_init_1340_, lean_object* v_start_1341_, lean_object* v___y_1342_){
_start:
{
uint8_t v_json_boxed_1343_; uint8_t v_includeEndPos_boxed_1344_; lean_object* v_res_1345_; 
v_json_boxed_1343_ = lean_unbox(v_json_1336_);
v_includeEndPos_boxed_1344_ = lean_unbox(v_includeEndPos_1337_);
v_res_1345_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1335_, v_json_boxed_1343_, v_includeEndPos_boxed_1344_, v_severityOverrides_1338_, v_t_1339_, v_init_1340_, v_start_1341_);
lean_dec(v_start_1341_);
lean_dec(v_severityOverrides_1338_);
lean_dec_ref(v_opts_1335_);
return v_res_1345_;
}
}
lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(lean_object* v_msgLog_1346_, lean_object* v_opts_1347_, uint8_t v_json_1348_, lean_object* v_severityOverrides_1349_, lean_object* v_numErrors_1350_){
_start:
{
lean_object* v_unreported_1352_; lean_object* v___x_1353_; uint8_t v_includeEndPos_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_unreported_1352_ = lean_ctor_get(v_msgLog_1346_, 1);
lean_inc_ref(v_unreported_1352_);
lean_dec_ref(v_msgLog_1346_);
v___x_1353_ = l_Lean_Language_printMessageEndPos;
v_includeEndPos_1354_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_1347_, v___x_1353_);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1347_, v_json_1348_, v_includeEndPos_1354_, v_severityOverrides_1349_, v_unreported_1352_, v_numErrors_1350_, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT void l___private_Lean_Language_Basic_0__Lean_Language_reportMessages_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgLog_1346_ = stack[0].m_obj;
lean_object* v_opts_1347_ = stack[1].m_obj;
uint8_t v_json_1348_ = stack[2].m_num;
lean_object* v_severityOverrides_1349_ = stack[3].m_obj;
lean_object* v_numErrors_1350_ = stack[4].m_obj;
lean_object* v_res_1357_;
v_res_1357_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1346_, v_opts_1347_, v_json_1348_, v_severityOverrides_1349_, v_numErrors_1350_);
stack->m_obj
 = v_res_1357_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___boxed(lean_object* v_msgLog_1358_, lean_object* v_opts_1359_, lean_object* v_json_1360_, lean_object* v_severityOverrides_1361_, lean_object* v_numErrors_1362_, lean_object* v_a_1363_){
_start:
{
uint8_t v_json_boxed_1364_; lean_object* v_res_1365_; 
v_json_boxed_1364_ = lean_unbox(v_json_1360_);
v_res_1365_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1358_, v_opts_1359_, v_json_boxed_1364_, v_severityOverrides_1361_, v_numErrors_1362_);
lean_dec(v_severityOverrides_1361_);
lean_dec_ref(v_opts_1359_);
return v_res_1365_;
}
}
lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object* v_opts_1366_, uint8_t v_json_1367_, lean_object* v_severityOverrides_1368_, lean_object* v_s_1369_, lean_object* v_init_1370_){
_start:
{
lean_object* v_element_1372_; lean_object* v_diagnostics_1373_; lean_object* v_children_1374_; lean_object* v_msgLog_1375_; lean_object* v___x_1376_; 
v_element_1372_ = lean_ctor_get(v_s_1369_, 0);
v_diagnostics_1373_ = lean_ctor_get(v_element_1372_, 1);
lean_inc_ref(v_diagnostics_1373_);
v_children_1374_ = lean_ctor_get(v_s_1369_, 1);
lean_inc_ref(v_children_1374_);
lean_dec_ref(v_s_1369_);
v_msgLog_1375_ = lean_ctor_get(v_diagnostics_1373_, 0);
lean_inc_ref(v_msgLog_1375_);
lean_dec_ref(v_diagnostics_1373_);
v___x_1376_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1375_, v_opts_1366_, v_json_1367_, v_severityOverrides_1368_, v_init_1370_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = lean_array_get_size(v_children_1374_);
v___x_1380_ = lean_nat_dec_lt(v___x_1378_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_dec_ref(v_children_1374_);
return v___x_1376_;
}
else
{
size_t v___x_1381_; size_t v___x_1382_; lean_object* v___x_1383_; 
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1381_ = ((size_t)0ULL);
v___x_1382_ = lean_usize_of_nat(v___x_1379_);
v___x_1383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1366_, v_json_1367_, v_severityOverrides_1368_, v_children_1374_, v___x_1381_, v___x_1382_, v_a_1377_);
lean_dec_ref(v_children_1374_);
return v___x_1383_;
}
}
else
{
lean_dec_ref(v_children_1374_);
return v___x_1376_;
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1366_ = stack[0].m_obj;
uint8_t v_json_1367_ = stack[1].m_num;
lean_object* v_severityOverrides_1368_ = stack[2].m_obj;
lean_object* v_s_1369_ = stack[3].m_obj;
lean_object* v_init_1370_ = stack[4].m_obj;
lean_object* v_res_1384_;
v_res_1384_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1366_, v_json_1367_, v_severityOverrides_1368_, v_s_1369_, v_init_1370_);
stack->m_obj
 = v_res_1384_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object* v_opts_1385_, uint8_t v_json_1386_, lean_object* v_severityOverrides_1387_, lean_object* v_as_1388_, size_t v_i_1389_, size_t v_stop_1390_, lean_object* v_b_1391_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_usize_dec_eq(v_i_1389_, v_stop_1390_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = lean_array_uget_borrowed(v_as_1388_, v_i_1389_);
lean_inc(v___x_1394_);
v___x_1395_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1394_);
v___x_1396_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1385_, v_json_1386_, v_severityOverrides_1387_, v___x_1395_, v_b_1391_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; size_t v___x_1398_; size_t v___x_1399_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_add(v_i_1389_, v___x_1398_);
v_i_1389_ = v___x_1399_;
v_b_1391_ = v_a_1397_;
goto _start;
}
else
{
return v___x_1396_;
}
}
else
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_b_1391_);
return v___x_1401_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1385_ = stack[0].m_obj;
uint8_t v_json_1386_ = stack[1].m_num;
lean_object* v_severityOverrides_1387_ = stack[2].m_obj;
lean_object* v_as_1388_ = stack[3].m_obj;
size_t v_i_1389_ = stack[4].m_num;
size_t v_stop_1390_ = stack[5].m_num;
lean_object* v_b_1391_ = stack[6].m_obj;
lean_object* v_res_1402_;
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1385_, v_json_1386_, v_severityOverrides_1387_, v_as_1388_, v_i_1389_, v_stop_1390_, v_b_1391_);
stack->m_obj
 = v_res_1402_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object* v_opts_1403_, lean_object* v_json_1404_, lean_object* v_severityOverrides_1405_, lean_object* v_as_1406_, lean_object* v_i_1407_, lean_object* v_stop_1408_, lean_object* v_b_1409_, lean_object* v___y_1410_){
_start:
{
uint8_t v_json_boxed_1411_; size_t v_i_boxed_1412_; size_t v_stop_boxed_1413_; lean_object* v_res_1414_; 
v_json_boxed_1411_ = lean_unbox(v_json_1404_);
v_i_boxed_1412_ = lean_unbox_usize(v_i_1407_);
lean_dec(v_i_1407_);
v_stop_boxed_1413_ = lean_unbox_usize(v_stop_1408_);
lean_dec(v_stop_1408_);
v_res_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1403_, v_json_boxed_1411_, v_severityOverrides_1405_, v_as_1406_, v_i_boxed_1412_, v_stop_boxed_1413_, v_b_1409_);
lean_dec_ref(v_as_1406_);
lean_dec(v_severityOverrides_1405_);
lean_dec_ref(v_opts_1403_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object* v_opts_1415_, lean_object* v_json_1416_, lean_object* v_severityOverrides_1417_, lean_object* v_s_1418_, lean_object* v_init_1419_, lean_object* v___y_1420_){
_start:
{
uint8_t v_json_boxed_1421_; lean_object* v_res_1422_; 
v_json_boxed_1421_ = lean_unbox(v_json_1416_);
v_res_1422_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1415_, v_json_boxed_1421_, v_severityOverrides_1417_, v_s_1418_, v_init_1419_);
lean_dec(v_severityOverrides_1417_);
lean_dec_ref(v_opts_1415_);
return v_res_1422_;
}
}
lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object* v_s_1423_, lean_object* v_opts_1424_, uint8_t v_json_1425_, lean_object* v_severityOverrides_1426_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1424_, v_json_1425_, v_severityOverrides_1426_, v_s_1423_, v___x_1428_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1439_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1434_ = lean_nat_dec_lt(v___x_1428_, v_a_1430_);
lean_dec(v_a_1430_);
v___x_1435_ = lean_box(v___x_1434_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1435_);
v___x_1437_ = v___x_1432_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
v_a_1440_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1429_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1429_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTree_runAndReport_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1423_ = stack[0].m_obj;
lean_object* v_opts_1424_ = stack[1].m_obj;
uint8_t v_json_1425_ = stack[2].m_num;
lean_object* v_severityOverrides_1426_ = stack[3].m_obj;
lean_object* v_res_1448_;
v_res_1448_ = l_Lean_Language_SnapshotTree_runAndReport(v_s_1423_, v_opts_1424_, v_json_1425_, v_severityOverrides_1426_);
stack->m_obj
 = v_res_1448_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object* v_s_1449_, lean_object* v_opts_1450_, lean_object* v_json_1451_, lean_object* v_severityOverrides_1452_, lean_object* v_a_1453_){
_start:
{
uint8_t v_json_boxed_1454_; lean_object* v_res_1455_; 
v_json_boxed_1454_ = lean_unbox(v_json_1451_);
v_res_1455_ = l_Lean_Language_SnapshotTree_runAndReport(v_s_1449_, v_opts_1450_, v_json_boxed_1454_, v_severityOverrides_1452_);
lean_dec(v_severityOverrides_1452_);
lean_dec_ref(v_opts_1450_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(lean_object* v_s_1456_, lean_object* v_init_1457_){
_start:
{
lean_object* v_element_1458_; lean_object* v_children_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_element_1458_ = lean_ctor_get(v_s_1456_, 0);
lean_inc_ref(v_element_1458_);
v_children_1459_ = lean_ctor_get(v_s_1456_, 1);
lean_inc_ref(v_children_1459_);
lean_dec_ref(v_s_1456_);
v___x_1460_ = lean_array_push(v_init_1457_, v_element_1458_);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_array_get_size(v_children_1459_);
v___x_1463_ = lean_nat_dec_lt(v___x_1461_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_dec_ref(v_children_1459_);
return v___x_1460_;
}
else
{
size_t v___x_1464_; size_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = ((size_t)0ULL);
v___x_1465_ = lean_usize_of_nat(v___x_1462_);
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_1459_, v___x_1464_, v___x_1465_, v___x_1460_);
lean_dec_ref(v_children_1459_);
return v___x_1466_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object* v_as_1467_, size_t v_i_1468_, size_t v_stop_1469_, lean_object* v_b_1470_){
_start:
{
uint8_t v___x_1471_; 
v___x_1471_ = lean_usize_dec_eq(v_i_1468_, v_stop_1469_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; 
v___x_1472_ = lean_array_uget_borrowed(v_as_1467_, v_i_1468_);
lean_inc(v___x_1472_);
v___x_1473_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1472_);
v___x_1474_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v___x_1473_, v_b_1470_);
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_add(v_i_1468_, v___x_1475_);
v_i_1468_ = v___x_1476_;
v_b_1470_ = v___x_1474_;
goto _start;
}
else
{
return v_b_1470_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1467_ = stack[0].m_obj;
size_t v_i_1468_ = stack[1].m_num;
size_t v_stop_1469_ = stack[2].m_num;
lean_object* v_b_1470_ = stack[3].m_obj;
lean_object* v_res_1478_;
v_res_1478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_as_1467_, v_i_1468_, v_stop_1469_, v_b_1470_);
stack->m_obj
 = v_res_1478_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object* v_as_1479_, lean_object* v_i_1480_, lean_object* v_stop_1481_, lean_object* v_b_1482_){
_start:
{
size_t v_i_boxed_1483_; size_t v_stop_boxed_1484_; lean_object* v_res_1485_; 
v_i_boxed_1483_ = lean_unbox_usize(v_i_1480_);
lean_dec(v_i_1480_);
v_stop_boxed_1484_ = lean_unbox_usize(v_stop_1481_);
lean_dec(v_stop_1481_);
v_res_1485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_as_1479_, v_i_boxed_1483_, v_stop_boxed_1484_, v_b_1482_);
lean_dec_ref(v_as_1479_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object* v_s_1488_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = ((lean_object*)(l_Lean_Language_SnapshotTree_getAll___closed__0));
v___x_1490_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v_s_1488_, v___x_1489_);
return v___x_1490_;
}
}
static lean_object* _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_box(0);
v___x_1492_ = lean_task_pure(v___x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed(lean_object* v_tail_1493_, lean_object* v_t_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(v_tail_1493_, v_t_1494_);
return v_res_1496_;
}
}
lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(lean_object* v_a_1497_){
_start:
{
if (lean_obj_tag(v_a_1497_) == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_obj_once(&l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0, &l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0_once, _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0);
return v___x_1499_;
}
else
{
lean_object* v_head_1500_; lean_object* v_tail_1501_; lean_object* v_task_1502_; lean_object* v___f_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; lean_object* v___x_1506_; 
v_head_1500_ = lean_ctor_get(v_a_1497_, 0);
lean_inc(v_head_1500_);
v_tail_1501_ = lean_ctor_get(v_a_1497_, 1);
lean_inc(v_tail_1501_);
lean_dec_ref_known(v_a_1497_, 2);
v_task_1502_ = lean_ctor_get(v_head_1500_, 3);
lean_inc_ref(v_task_1502_);
lean_dec(v_head_1500_);
v___f_1503_ = lean_alloc_closure((void*)(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1503_, 0, v_tail_1501_);
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = 1;
v___x_1506_ = lean_io_bind_task(v_task_1502_, v___f_1503_, v___x_1504_, v___x_1505_);
return v___x_1506_;
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1497_ = stack[0].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v_a_1497_);
stack->m_obj
 = v_res_1507_;
}
lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object* v_tail_1508_, lean_object* v_t_1509_){
_start:
{
lean_object* v_children_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_children_1511_ = lean_ctor_get(v_t_1509_, 1);
lean_inc_ref(v_children_1511_);
lean_dec_ref(v_t_1509_);
v___x_1512_ = lean_array_to_list(v_children_1511_);
v___x_1513_ = l_List_appendTR___redArg(v___x_1512_, v_tail_1508_);
v___x_1514_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT void l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_1508_ = stack[0].m_obj;
lean_object* v_t_1509_ = stack[1].m_obj;
lean_object* v_res_1515_;
v_res_1515_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(v_tail_1508_, v_t_1509_);
stack->m_obj
 = v_res_1515_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___boxed(lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v_a_1516_);
return v_res_1518_;
}
}
lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object* v_x_1519_){
_start:
{
lean_object* v_children_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_children_1521_ = lean_ctor_get(v_x_1519_, 1);
lean_inc_ref(v_children_1521_);
lean_dec_ref(v_x_1519_);
v___x_1522_ = lean_array_to_list(v_children_1521_);
v___x_1523_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTree_waitAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1519_ = stack[0].m_obj;
lean_object* v_res_1524_;
v_res_1524_ = l_Lean_Language_SnapshotTree_waitAll(v_x_1519_);
stack->m_obj
 = v_res_1524_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll___boxed(lean_object* v_x_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_Language_SnapshotTree_waitAll(v_x_1525_);
return v_res_1527_;
}
}
lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object* v_00_u03b1_1528_, lean_object* v_act_1529_, lean_object* v_ctx_1530_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_apply_2(v_act_1529_, v_ctx_1530_, lean_box(0));
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT void l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_1529_ = stack[1].m_obj;
lean_object* v_ctx_1530_ = stack[2].m_obj;
lean_object* v_res_1534_;
v_res_1534_ = l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_box(0), v_act_1529_, v_ctx_1530_);
stack->m_obj
 = v_res_1534_;
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0___boxed(lean_object* v_00_u03b1_1535_, lean_object* v_act_1536_, lean_object* v_ctx_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(v_00_u03b1_1535_, v_act_1536_, v_ctx_1537_);
return v_res_1539_;
}
}
lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object* v_msgLog_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_st_mk_ref(v___x_1544_);
v___x_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_msgLog_1542_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT void l_Lean_Language_Snapshot_Diagnostics_ofMessageLog_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgLog_1542_ = stack[0].m_obj;
lean_object* v_res_1548_;
v_res_1548_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1542_);
stack->m_obj
 = v_res_1548_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog___boxed(lean_object* v_msgLog_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1549_);
return v_res_1551_;
}
}
lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object* v_msg_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_fileMap_1559_; lean_object* v_source_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_fileMap_1559_ = lean_ctor_get(v_a_1557_, 2);
v_source_1560_ = lean_ctor_get(v_fileMap_1559_, 0);
v___x_1561_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__0));
v___x_1562_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__1));
v___x_1563_ = lean_string_utf8_byte_size(v_source_1560_);
lean_inc_ref(v_fileMap_1559_);
v___x_1564_ = l_Lean_FileMap_toPosition(v_fileMap_1559_, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
v___x_1566_ = 0;
v___x_1567_ = 2;
v___x_1568_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot___closed__0));
v___x_1569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_msg_1556_);
v___x_1570_ = l_Lean_MessageData_ofFormat(v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1571_, 0, v___x_1561_);
lean_ctor_set(v___x_1571_, 1, v___x_1562_);
lean_ctor_set(v___x_1571_, 2, v___x_1565_);
lean_ctor_set(v___x_1571_, 3, v___x_1568_);
lean_ctor_set(v___x_1571_, 4, v___x_1570_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*5, v___x_1566_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*5 + 1, v___x_1567_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*5 + 2, v___x_1566_);
v___x_1572_ = l_Lean_MessageLog_empty;
v___x_1573_ = l_Lean_MessageLog_add(v___x_1571_, v___x_1572_);
v___x_1574_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT void l_Lean_Language_diagnosticsOfHeaderError_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1556_ = stack[0].m_obj;
lean_object* v_a_1557_ = stack[1].m_obj;
lean_object* v_res_1575_;
v_res_1575_ = l_Lean_Language_diagnosticsOfHeaderError(v_msg_1556_, v_a_1557_);
stack->m_obj
 = v_res_1575_;
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError___boxed(lean_object* v_msg_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Language_diagnosticsOfHeaderError(v_msg_1576_, v_a_1577_);
lean_dec_ref(v_a_1577_);
return v_res_1579_;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2(void){
_start:
{
uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = 1;
v___x_1586_ = ((lean_object*)(l_Lean_Language_withHeaderExceptions___redArg___closed__1));
v___x_1587_ = l_Lean_Name_toString(v___x_1586_, v___x_1585_);
return v___x_1587_;
}
}
lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object* v_ex_1588_, lean_object* v_act_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v___x_1592_; 
lean_inc_ref(v_a_1590_);
v___x_1592_ = lean_apply_2(v_act_1589_, v_a_1590_, lean_box(0));
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; 
lean_dec(v_ex_1588_);
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
return v_a_1593_;
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_a_1594_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1595_ = lean_io_error_to_string(v_a_1594_);
v___x_1596_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_1595_, v_a_1590_);
v___x_1597_ = lean_obj_once(&l_Lean_Language_withHeaderExceptions___redArg___closed__2, &l_Lean_Language_withHeaderExceptions___redArg___closed__2_once, _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2);
v___x_1598_ = lean_box(0);
v___x_1599_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_1600_ = 0;
v___x_1601_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1601_, 0, v___x_1597_);
lean_ctor_set(v___x_1601_, 1, v___x_1596_);
lean_ctor_set(v___x_1601_, 2, v___x_1598_);
lean_ctor_set(v___x_1601_, 3, v___x_1599_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*4, v___x_1600_);
v___x_1602_ = lean_apply_1(v_ex_1588_, v___x_1601_);
return v___x_1602_;
}
}
}
LEAN_EXPORT void l_Lean_Language_withHeaderExceptions___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_1588_ = stack[0].m_obj;
lean_object* v_act_1589_ = stack[1].m_obj;
lean_object* v_a_1590_ = stack[2].m_obj;
lean_object* v_res_1603_;
v_res_1603_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1588_, v_act_1589_, v_a_1590_);
stack->m_obj
 = v_res_1603_;
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg___boxed(lean_object* v_ex_1604_, lean_object* v_act_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1604_, v_act_1605_, v_a_1606_);
lean_dec_ref(v_a_1606_);
return v_res_1608_;
}
}
lean_object* l_Lean_Language_withHeaderExceptions(lean_object* v_00_u03b1_1609_, lean_object* v_ex_1610_, lean_object* v_act_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1610_, v_act_1611_, v_a_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT void l_Lean_Language_withHeaderExceptions_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_1610_ = stack[1].m_obj;
lean_object* v_act_1611_ = stack[2].m_obj;
lean_object* v_a_1612_ = stack[3].m_obj;
lean_object* v_res_1615_;
v_res_1615_ = l_Lean_Language_withHeaderExceptions(lean_box(0), v_ex_1610_, v_act_1611_, v_a_1612_);
stack->m_obj
 = v_res_1615_;
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___boxed(lean_object* v_00_u03b1_1616_, lean_object* v_ex_1617_, lean_object* v_act_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Language_withHeaderExceptions(v_00_u03b1_1616_, v_ex_1617_, v_act_1618_, v_a_1619_);
lean_dec_ref(v_a_1619_);
return v_res_1621_;
}
}
lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object* v_val_1622_, lean_object* v_process_1623_, lean_object* v_ictx_1624_){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1626_ = lean_st_ref_get(v_val_1622_);
v___x_1627_ = lean_apply_3(v_process_1623_, v___x_1626_, v_ictx_1624_, lean_box(0));
lean_inc(v___x_1627_);
v___x_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
v___x_1629_ = lean_st_ref_swap(v_val_1622_, v___x_1628_);
lean_dec(v___x_1629_);
return v___x_1627_;
}
}
LEAN_EXPORT void l_Lean_Language_mkIncrementalProcessor___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1622_ = stack[0].m_obj;
lean_object* v_process_1623_ = stack[1].m_obj;
lean_object* v_ictx_1624_ = stack[2].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(v_val_1622_, v_process_1623_, v_ictx_1624_);
stack->m_obj
 = v_res_1630_;
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object* v_val_1631_, lean_object* v_process_1632_, lean_object* v_ictx_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(v_val_1631_, v_process_1632_, v_ictx_1633_);
lean_dec(v_val_1631_);
return v_res_1635_;
}
}
lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object* v_process_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___f_1640_; 
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_st_mk_ref(v___x_1638_);
v___f_1640_ = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1640_, 0, v___x_1639_);
lean_closure_set(v___f_1640_, 1, v_process_1636_);
return v___f_1640_;
}
}
LEAN_EXPORT void l_Lean_Language_mkIncrementalProcessor___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_process_1636_ = stack[0].m_obj;
lean_object* v_res_1641_;
v_res_1641_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1636_);
stack->m_obj
 = v_res_1641_;
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___boxed(lean_object* v_process_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1642_);
return v_res_1644_;
}
}
lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object* v_InitSnap_1645_, lean_object* v_process_1646_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1646_);
return v___x_1648_;
}
}
LEAN_EXPORT void l_Lean_Language_mkIncrementalProcessor_0interp(lean_interpreter_value* stack)
{
lean_object* v_process_1646_ = stack[1].m_obj;
lean_object* v_res_1649_;
v_res_1649_ = l_Lean_Language_mkIncrementalProcessor(lean_box(0), v_process_1646_);
stack->m_obj
 = v_res_1649_;
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___boxed(lean_object* v_InitSnap_1650_, lean_object* v_process_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Language_mkIncrementalProcessor(v_InitSnap_1650_, v_process_1651_);
return v_res_1653_;
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
