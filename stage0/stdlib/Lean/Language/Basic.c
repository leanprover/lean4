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
uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_le(v___x_634_, v___x_634_);
if (v___x_637_ == 0)
{
if (v___x_636_ == 0)
{
lean_dec_ref(v_children_632_);
lean_dec_ref(v___f_628_);
lean_dec_ref(v___x_627_);
return v___x_635_;
}
else
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_205__overap_640_; lean_object* v___x_641_; 
v___x_638_ = ((size_t)0ULL);
v___x_639_ = lean_usize_of_nat(v___x_634_);
v___x_205__overap_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_627_, v___f_628_, v_children_632_, v___x_638_, v___x_639_, v___x_635_);
v___x_641_ = lean_apply_1(v___x_205__overap_640_, lean_box(0));
return v___x_641_;
}
}
else
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_208__overap_644_; lean_object* v___x_645_; 
v___x_642_ = ((size_t)0ULL);
v___x_643_ = lean_usize_of_nat(v___x_634_);
v___x_208__overap_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_627_, v___f_628_, v_children_632_, v___x_642_, v___x_643_, v___x_635_);
v___x_645_ = lean_apply_1(v___x_208__overap_644_, lean_box(0));
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed(lean_object* v_inst_646_, lean_object* v___x_647_, lean_object* v___f_648_, lean_object* v_snap_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(v_inst_646_, v___x_647_, v___f_648_, v_snap_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(lean_object* v___f_652_, lean_object* v_x_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(v___f_652_, v_x_653_, v___y_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object* v_inst_657_, lean_object* v_t_658_){
_start:
{
lean_object* v___x_660_; lean_object* v_cancelTk_x3f_661_; lean_object* v_task_662_; lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___f_665_; 
v___x_660_ = l_instMonadBaseIO;
v_cancelTk_x3f_661_ = lean_ctor_get(v_t_658_, 2);
lean_inc(v_cancelTk_x3f_661_);
v_task_662_ = lean_ctor_get(v_t_658_, 3);
lean_inc_ref(v_task_662_);
lean_dec_ref(v_t_658_);
v___f_663_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0));
v___f_664_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_664_, 0, v___f_663_);
v___f_665_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_665_, 0, v_inst_657_);
lean_closure_set(v___f_665_, 1, v___x_660_);
lean_closure_set(v___f_665_, 2, v___f_664_);
if (lean_obj_tag(v_cancelTk_x3f_661_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_671_; 
v_val_670_ = lean_ctor_get(v_cancelTk_x3f_661_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v_cancelTk_x3f_661_, 1);
v___x_671_ = l_IO_CancelToken_set(v_val_670_);
lean_dec(v_val_670_);
goto v___jp_666_;
}
else
{
lean_dec(v_cancelTk_x3f_661_);
goto v___jp_666_;
}
v___jp_666_:
{
lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = 1;
v___x_669_ = l_BaseIO_chainTask___redArg(v_task_662_, v___f_665_, v___x_667_, v___x_668_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object* v___f_672_, lean_object* v_x_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_672_, v___y_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___boxed(lean_object* v_inst_677_, lean_object* v_t_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_677_, v_t_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object* v_00_u03b1_681_, lean_object* v_inst_682_, lean_object* v_t_683_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_682_, v_t_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___boxed(lean_object* v_00_u03b1_686_, lean_object* v_inst_687_, lean_object* v_t_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Language_SnapshotTask_cancelRec(v_00_u03b1_686_, v_inst_687_, v_t_688_);
return v_res_690_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotLeaf(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_unsigned_to_nat(32u);
v___x_699_ = lean_mk_empty_array_with_capacity(v___x_698_);
lean_dec_ref(v___x_699_);
v___x_700_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object* v_s_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = l_Lean_Language_Snapshot_transform(v_s_703_, v___y_704_);
v___x_706_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0));
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___boxed(lean_object* v_s_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(v_s_708_, v___y_709_);
lean_dec_ref(v___y_709_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object* v_s_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_toSnapshotTreeM_715_; lean_object* v___x_716_; 
v_toSnapshotTreeM_715_ = lean_ctor_get(v_s_713_, 1);
lean_inc_ref(v_toSnapshotTreeM_715_);
lean_dec_ref(v_s_713_);
lean_inc_ref(v___y_714_);
v___x_716_ = lean_apply_1(v_toSnapshotTreeM_715_, v___y_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object* v_s_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(v_s_717_, v___y_718_);
lean_dec_ref(v___y_718_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_val_724_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
lean_inc(v_val_724_);
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v_inst_722_);
lean_ctor_set(v___x_725_, 1, v_val_724_);
v___x_726_ = lean_apply_1(v_inst_723_, v_val_724_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object* v_00_u03b1_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_val_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v_inst_729_, v_inst_730_, v_val_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object* v_inst_733_, lean_object* v_snap_734_){
_start:
{
lean_object* v_val_735_; lean_object* v___x_736_; 
v_val_735_ = lean_ctor_get(v_snap_734_, 0);
v___x_736_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_735_, v_inst_733_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object* v_inst_737_, lean_object* v_snap_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_737_, v_snap_738_);
lean_dec_ref(v_snap_738_);
lean_dec(v_inst_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object* v_00_u03b1_740_, lean_object* v_inst_741_, lean_object* v_snap_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_741_, v_snap_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object* v_00_u03b1_744_, lean_object* v_inst_745_, lean_object* v_snap_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f(v_00_u03b1_744_, v_inst_745_, v_snap_746_);
lean_dec_ref(v_snap_746_);
lean_dec(v_inst_745_);
return v_res_747_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2(void){
_start:
{
uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = 1;
v___x_754_ = ((lean_object*)(l_Lean_Language_instInhabitedDynamicSnapshot___closed__1));
v___x_755_ = l_Lean_Name_toString(v___x_754_, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3(void){
_start:
{
uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_756_ = 0;
v___x_757_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_758_ = lean_box(0);
v___x_759_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_760_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__2, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__2_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2);
v___x_761_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___x_759_);
lean_ctor_set(v___x_761_, 2, v___x_758_);
lean_ctor_set(v___x_761_, 3, v___x_757_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*4, v___x_756_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4(void){
_start:
{
lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_762_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__3, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3);
v___f_763_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0));
v___x_764_ = ((lean_object*)(l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_));
v___x_765_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v___x_764_, v___f_763_, v___x_762_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot(void){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__4, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object* v_toApplicative_767_, lean_object* v_children_768_, lean_object* v_inst_769_, lean_object* v___f_770_, lean_object* v_____r_771_){
_start:
{
lean_object* v_toPure_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_toPure_772_ = lean_ctor_get(v_toApplicative_767_, 1);
lean_inc(v_toPure_772_);
lean_dec_ref(v_toApplicative_767_);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_array_get_size(v_children_768_);
v___x_775_ = lean_box(0);
v___x_776_ = lean_nat_dec_lt(v___x_773_, v___x_774_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
lean_dec(v___f_770_);
lean_dec_ref(v_inst_769_);
lean_dec_ref(v_children_768_);
v___x_777_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_775_);
return v___x_777_;
}
else
{
uint8_t v___x_778_; 
v___x_778_ = lean_nat_dec_le(v___x_774_, v___x_774_);
if (v___x_778_ == 0)
{
if (v___x_776_ == 0)
{
lean_object* v___x_779_; 
lean_dec(v___f_770_);
lean_dec_ref(v_inst_769_);
lean_dec_ref(v_children_768_);
v___x_779_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_775_);
return v___x_779_;
}
else
{
size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
lean_dec(v_toPure_772_);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_of_nat(v___x_774_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_769_, v___f_770_, v_children_768_, v___x_780_, v___x_781_, v___x_775_);
return v___x_782_;
}
}
else
{
size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
lean_dec(v_toPure_772_);
v___x_783_ = ((size_t)0ULL);
v___x_784_ = lean_usize_of_nat(v___x_774_);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_769_, v___f_770_, v_children_768_, v___x_783_, v___x_784_, v___x_775_);
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object* v_inst_786_, lean_object* v_s_787_, lean_object* v_f_788_){
_start:
{
lean_object* v_toApplicative_789_; lean_object* v_toBind_790_; lean_object* v_element_791_; lean_object* v_children_792_; lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_toApplicative_789_ = lean_ctor_get(v_inst_786_, 0);
lean_inc_ref(v_toApplicative_789_);
v_toBind_790_ = lean_ctor_get(v_inst_786_, 1);
lean_inc(v_toBind_790_);
v_element_791_ = lean_ctor_get(v_s_787_, 0);
lean_inc_ref(v_element_791_);
v_children_792_ = lean_ctor_get(v_s_787_, 1);
lean_inc_ref(v_children_792_);
lean_dec_ref(v_s_787_);
lean_inc(v_f_788_);
lean_inc_ref(v_inst_786_);
v___f_793_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_793_, 0, v_inst_786_);
lean_closure_set(v___f_793_, 1, v_f_788_);
v___f_794_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_794_, 0, v_toApplicative_789_);
lean_closure_set(v___f_794_, 1, v_children_792_);
lean_closure_set(v___f_794_, 2, v_inst_786_);
lean_closure_set(v___f_794_, 3, v___f_793_);
v___x_795_ = lean_apply_1(v_f_788_, v_element_791_);
v___x_796_ = lean_apply_4(v_toBind_790_, lean_box(0), lean_box(0), v___x_795_, v___f_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object* v_inst_797_, lean_object* v_f_798_, lean_object* v_x_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = l_Lean_Language_SnapshotTask_get___redArg(v___y_800_);
v___x_802_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_797_, v___x_801_, v_f_798_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object* v_m_803_, lean_object* v_inst_804_, lean_object* v_s_805_, lean_object* v_f_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_804_, v_s_805_, v_f_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object* v_toApplicative_808_, lean_object* v_children_809_, lean_object* v_inst_810_, lean_object* v___f_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_toPure_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_toPure_813_ = lean_ctor_get(v_toApplicative_808_, 1);
lean_inc(v_toPure_813_);
lean_dec_ref(v_toApplicative_808_);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_array_get_size(v_children_809_);
v___x_816_ = lean_nat_dec_lt(v___x_814_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_dec(v___f_811_);
lean_dec_ref(v_inst_810_);
lean_dec_ref(v_children_809_);
v___x_817_ = lean_apply_2(v_toPure_813_, lean_box(0), v_a_812_);
return v___x_817_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = lean_nat_dec_le(v___x_815_, v___x_815_);
if (v___x_818_ == 0)
{
if (v___x_816_ == 0)
{
lean_object* v___x_819_; 
lean_dec(v___f_811_);
lean_dec_ref(v_inst_810_);
lean_dec_ref(v_children_809_);
v___x_819_ = lean_apply_2(v_toPure_813_, lean_box(0), v_a_812_);
return v___x_819_;
}
else
{
size_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; 
lean_dec(v_toPure_813_);
v___x_820_ = ((size_t)0ULL);
v___x_821_ = lean_usize_of_nat(v___x_815_);
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_810_, v___f_811_, v_children_809_, v___x_820_, v___x_821_, v_a_812_);
return v___x_822_;
}
}
else
{
size_t v___x_823_; size_t v___x_824_; lean_object* v___x_825_; 
lean_dec(v_toPure_813_);
v___x_823_ = ((size_t)0ULL);
v___x_824_ = lean_usize_of_nat(v___x_815_);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_810_, v___f_811_, v_children_809_, v___x_823_, v___x_824_, v_a_812_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object* v_inst_826_, lean_object* v_s_827_, lean_object* v_f_828_, lean_object* v_init_829_){
_start:
{
lean_object* v_toApplicative_830_; lean_object* v_toBind_831_; lean_object* v_element_832_; lean_object* v_children_833_; lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_toApplicative_830_ = lean_ctor_get(v_inst_826_, 0);
lean_inc_ref(v_toApplicative_830_);
v_toBind_831_ = lean_ctor_get(v_inst_826_, 1);
lean_inc(v_toBind_831_);
v_element_832_ = lean_ctor_get(v_s_827_, 0);
lean_inc_ref(v_element_832_);
v_children_833_ = lean_ctor_get(v_s_827_, 1);
lean_inc_ref(v_children_833_);
lean_dec_ref(v_s_827_);
lean_inc(v_f_828_);
lean_inc_ref(v_inst_826_);
v___f_834_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_834_, 0, v_inst_826_);
lean_closure_set(v___f_834_, 1, v_f_828_);
v___f_835_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_835_, 0, v_toApplicative_830_);
lean_closure_set(v___f_835_, 1, v_children_833_);
lean_closure_set(v___f_835_, 2, v_inst_826_);
lean_closure_set(v___f_835_, 3, v___f_834_);
v___x_836_ = lean_apply_2(v_f_828_, v_init_829_, v_element_832_);
v___x_837_ = lean_apply_4(v_toBind_831_, lean_box(0), lean_box(0), v___x_836_, v___f_835_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object* v_inst_838_, lean_object* v_f_839_, lean_object* v_a_840_, lean_object* v_snap_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = l_Lean_Language_SnapshotTask_get___redArg(v_snap_841_);
v___x_843_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_838_, v___x_842_, v_f_839_, v_a_840_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object* v_m_844_, lean_object* v_00_u03b1_845_, lean_object* v_inst_846_, lean_object* v_s_847_, lean_object* v_f_848_, lean_object* v_init_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_846_, v_s_847_, v_f_848_, v_init_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(lean_object* v_name_851_, lean_object* v_decl_852_, lean_object* v_ref_853_){
_start:
{
lean_object* v_defValue_855_; lean_object* v_descr_856_; lean_object* v_deprecation_x3f_857_; lean_object* v___x_858_; uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_defValue_855_ = lean_ctor_get(v_decl_852_, 0);
v_descr_856_ = lean_ctor_get(v_decl_852_, 1);
v_deprecation_x3f_857_ = lean_ctor_get(v_decl_852_, 2);
v___x_858_ = lean_alloc_ctor(1, 0, 1);
v___x_859_ = lean_unbox(v_defValue_855_);
lean_ctor_set_uint8(v___x_858_, 0, v___x_859_);
lean_inc(v_deprecation_x3f_857_);
lean_inc_ref(v_descr_856_);
lean_inc_n(v_name_851_, 2);
v___x_860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_860_, 0, v_name_851_);
lean_ctor_set(v___x_860_, 1, v_ref_853_);
lean_ctor_set(v___x_860_, 2, v___x_858_);
lean_ctor_set(v___x_860_, 3, v_descr_856_);
lean_ctor_set(v___x_860_, 4, v_deprecation_x3f_857_);
v___x_861_ = lean_register_option(v_name_851_, v___x_860_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v___x_861_, 0);
lean_dec(v_unused_870_);
v___x_863_ = v___x_861_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_dec(v___x_861_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
lean_inc(v_defValue_855_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v_name_851_);
lean_ctor_set(v___x_865_, 1, v_defValue_855_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_name_851_);
v_a_871_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_861_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_861_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_879_, lean_object* v_decl_880_, lean_object* v_ref_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v_name_879_, v_decl_880_, v_ref_881_);
lean_dec_ref(v_decl_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_898_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_899_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_900_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_901_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v___x_898_, v___x_899_, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4____boxed(lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(lean_object* v_name_904_, lean_object* v_decl_905_, lean_object* v_ref_906_){
_start:
{
lean_object* v_defValue_908_; lean_object* v_descr_909_; lean_object* v_deprecation_x3f_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_defValue_908_ = lean_ctor_get(v_decl_905_, 0);
v_descr_909_ = lean_ctor_get(v_decl_905_, 1);
v_deprecation_x3f_910_ = lean_ctor_get(v_decl_905_, 2);
lean_inc(v_defValue_908_);
v___x_911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_911_, 0, v_defValue_908_);
lean_inc(v_deprecation_x3f_910_);
lean_inc_ref(v_descr_909_);
lean_inc_n(v_name_904_, 2);
v___x_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_912_, 0, v_name_904_);
lean_ctor_set(v___x_912_, 1, v_ref_906_);
lean_ctor_set(v___x_912_, 2, v___x_911_);
lean_ctor_set(v___x_912_, 3, v_descr_909_);
lean_ctor_set(v___x_912_, 4, v_deprecation_x3f_910_);
v___x_913_ = lean_register_option(v_name_904_, v___x_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_921_; 
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v___x_913_, 0);
lean_dec(v_unused_922_);
v___x_915_ = v___x_913_;
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
else
{
lean_dec(v___x_913_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
lean_inc(v_defValue_908_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_name_904_);
lean_ctor_set(v___x_917_, 1, v_defValue_908_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_917_);
v___x_919_ = v___x_915_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v_name_904_);
v_a_923_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_913_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_913_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_931_, lean_object* v_decl_932_, lean_object* v_ref_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v_name_931_, v_decl_932_, v_ref_933_);
lean_dec_ref(v_decl_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_949_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_950_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_951_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_952_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v___x_949_, v___x_950_, v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4____boxed(lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
return v_res_954_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(lean_object* v_opts_955_, lean_object* v_opt_956_){
_start:
{
lean_object* v_name_957_; lean_object* v_defValue_958_; lean_object* v_map_959_; lean_object* v___x_960_; 
v_name_957_ = lean_ctor_get(v_opt_956_, 0);
v_defValue_958_ = lean_ctor_get(v_opt_956_, 1);
v_map_959_ = lean_ctor_get(v_opts_955_, 0);
v___x_960_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_959_, v_name_957_);
if (lean_obj_tag(v___x_960_) == 0)
{
uint8_t v___x_961_; 
v___x_961_ = lean_unbox(v_defValue_958_);
return v___x_961_;
}
else
{
lean_object* v_val_962_; 
v_val_962_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_val_962_);
lean_dec_ref_known(v___x_960_, 1);
if (lean_obj_tag(v_val_962_) == 1)
{
uint8_t v_v_963_; 
v_v_963_ = lean_ctor_get_uint8(v_val_962_, 0);
lean_dec_ref_known(v_val_962_, 0);
return v_v_963_;
}
else
{
uint8_t v___x_964_; 
lean_dec(v_val_962_);
v___x_964_ = lean_unbox(v_defValue_958_);
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0___boxed(lean_object* v_opts_965_, lean_object* v_opt_966_){
_start:
{
uint8_t v_res_967_; lean_object* v_r_968_; 
v_res_967_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_965_, v_opt_966_);
lean_dec_ref(v_opt_966_);
lean_dec_ref(v_opts_965_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(lean_object* v_opts_969_, lean_object* v_opt_970_){
_start:
{
lean_object* v_name_971_; lean_object* v_defValue_972_; lean_object* v_map_973_; lean_object* v___x_974_; 
v_name_971_ = lean_ctor_get(v_opt_970_, 0);
v_defValue_972_ = lean_ctor_get(v_opt_970_, 1);
v_map_973_ = lean_ctor_get(v_opts_969_, 0);
v___x_974_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_973_, v_name_971_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_inc(v_defValue_972_);
return v_defValue_972_;
}
else
{
lean_object* v_val_975_; 
v_val_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_val_975_);
lean_dec_ref_known(v___x_974_, 1);
if (lean_obj_tag(v_val_975_) == 3)
{
lean_object* v_v_976_; 
v_v_976_ = lean_ctor_get(v_val_975_, 0);
lean_inc(v_v_976_);
lean_dec_ref_known(v_val_975_, 1);
return v_v_976_;
}
else
{
lean_dec(v_val_975_);
lean_inc(v_defValue_972_);
return v_defValue_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1___boxed(lean_object* v_opts_977_, lean_object* v_opt_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_977_, v_opt_978_);
lean_dec_ref(v_opt_978_);
lean_dec_ref(v_opts_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(lean_object* v_s_980_){
_start:
{
lean_object* v___x_982_; lean_object* v_putStr_983_; lean_object* v___x_984_; 
v___x_982_ = lean_get_stdout();
v_putStr_983_ = lean_ctor_get(v___x_982_, 4);
lean_inc_ref(v_putStr_983_);
lean_dec_ref(v___x_982_);
v___x_984_ = lean_apply_2(v_putStr_983_, v_s_980_, lean_box(0));
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2___boxed(lean_object* v_s_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v_s_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object* v_s_988_){
_start:
{
uint32_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = 10;
v___x_991_ = lean_string_push(v_s_988_, v___x_990_);
v___x_992_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3___boxed(lean_object* v_s_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v_s_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(lean_object* v_opts_998_, uint8_t v_json_999_, uint8_t v_includeEndPos_1000_, lean_object* v_severityOverrides_1001_, lean_object* v_as_1002_, size_t v_i_1003_, size_t v_stop_1004_, lean_object* v_b_1005_){
_start:
{
lean_object* v_a_1008_; lean_object* v___y_1013_; uint8_t v___y_1014_; uint8_t v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; uint8_t v_isSilent_1029_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; uint8_t v___y_1055_; uint8_t v___x_1079_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1090_; uint8_t v_severity_1091_; 
v___x_1079_ = lean_usize_dec_eq(v_i_1003_, v_stop_1004_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1094_; lean_object* v_fileName_1095_; lean_object* v_pos_1096_; lean_object* v_endPos_1097_; uint8_t v_keepFullRange_1098_; uint8_t v_isSilent_1099_; lean_object* v_caption_1100_; lean_object* v_data_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1094_ = lean_array_uget(v_as_1002_, v_i_1003_);
v_fileName_1095_ = lean_ctor_get(v___x_1094_, 0);
v_pos_1096_ = lean_ctor_get(v___x_1094_, 1);
v_endPos_1097_ = lean_ctor_get(v___x_1094_, 2);
v_keepFullRange_1098_ = lean_ctor_get_uint8(v___x_1094_, sizeof(void*)*5);
v_isSilent_1099_ = lean_ctor_get_uint8(v___x_1094_, sizeof(void*)*5 + 2);
v_caption_1100_ = lean_ctor_get(v___x_1094_, 3);
v_data_1101_ = lean_ctor_get(v___x_1094_, 4);
v___x_1102_ = l_Lean_MessageData_kind(v_data_1101_);
v___x_1103_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_severityOverrides_1001_, v___x_1102_);
lean_dec(v___x_1102_);
if (lean_obj_tag(v___x_1103_) == 1)
{
lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1113_; 
lean_inc(v_data_1101_);
lean_inc_ref(v_caption_1100_);
lean_inc(v_endPos_1097_);
lean_inc_ref(v_pos_1096_);
lean_inc_ref(v_fileName_1095_);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; lean_object* v_unused_1115_; lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; 
v_unused_1114_ = lean_ctor_get(v___x_1094_, 4);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v___x_1094_, 3);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v___x_1094_, 2);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v___x_1094_, 1);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v___x_1094_, 0);
lean_dec(v_unused_1118_);
v___x_1105_ = v___x_1094_;
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
else
{
lean_dec(v___x_1094_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v_val_1107_; lean_object* v___x_1109_; 
v_val_1107_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_val_1107_);
lean_dec_ref_known(v___x_1103_, 1);
if (v_isShared_1106_ == 0)
{
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_fileName_1095_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_pos_1096_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_endPos_1097_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_caption_1100_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_data_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*5, v_keepFullRange_1098_);
v___x_1109_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
uint8_t v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_unbox(v_val_1107_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*5 + 1, v___x_1110_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*5 + 2, v_isSilent_1099_);
v___x_1111_ = lean_unbox(v_val_1107_);
lean_dec(v_val_1107_);
v___y_1090_ = v___x_1109_;
v_severity_1091_ = v___x_1111_;
goto v___jp_1089_;
}
}
}
else
{
uint8_t v_severity_1119_; 
lean_dec(v___x_1103_);
v_severity_1119_ = lean_ctor_get_uint8(v___x_1094_, sizeof(void*)*5 + 1);
v___y_1090_ = v___x_1094_;
v_severity_1091_ = v_severity_1119_;
goto v___jp_1089_;
}
}
else
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_b_1005_);
return v___x_1120_;
}
v___jp_1007_:
{
size_t v___x_1009_; size_t v___x_1010_; 
v___x_1009_ = ((size_t)1ULL);
v___x_1010_ = lean_usize_add(v_i_1003_, v___x_1009_);
v_i_1003_ = v___x_1010_;
v_b_1005_ = v_a_1008_;
goto _start;
}
v___jp_1012_:
{
if (v___y_1014_ == 0)
{
v_a_1008_ = v___y_1013_;
goto v___jp_1007_;
}
else
{
uint8_t v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = 1;
v___x_1016_ = lean_io_exit(v___x_1015_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_dec_ref_known(v___x_1016_, 1);
v_a_1008_ = v___y_1013_;
goto v___jp_1007_;
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v___y_1013_);
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
}
v___jp_1025_:
{
if (v_isSilent_1029_ == 0)
{
if (v_json_999_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = l_Lean_Message_toString(v___y_1028_, v_includeEndPos_1000_);
v___x_1031_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_1030_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_dec_ref_known(v___x_1031_, 1);
v___y_1013_ = v___y_1027_;
v___y_1014_ = v___y_1026_;
goto v___jp_1012_;
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v___y_1027_);
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = l_Lean_Message_toJson(v___y_1028_);
v___x_1041_ = l_Lean_Json_compress(v___x_1040_);
v___x_1042_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_1041_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_dec_ref_known(v___x_1042_, 1);
v___y_1013_ = v___y_1027_;
v___y_1014_ = v___y_1026_;
goto v___jp_1012_;
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec(v___y_1027_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1028_);
v___y_1013_ = v___y_1027_;
v___y_1014_ = v___y_1026_;
goto v___jp_1012_;
}
}
v___jp_1051_:
{
if (v___y_1055_ == 0)
{
uint8_t v_isSilent_1056_; 
lean_dec(v___y_1054_);
v_isSilent_1056_ = lean_ctor_get_uint8(v___y_1052_, sizeof(void*)*5 + 2);
v___y_1026_ = v___y_1055_;
v___y_1027_ = v___y_1053_;
v___y_1028_ = v___y_1052_;
v_isSilent_1029_ = v_isSilent_1056_;
goto v___jp_1025_;
}
else
{
lean_object* v_fileName_1057_; lean_object* v_pos_1058_; lean_object* v_endPos_1059_; uint8_t v_keepFullRange_1060_; uint8_t v_isSilent_1061_; lean_object* v_caption_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1077_; 
v_fileName_1057_ = lean_ctor_get(v___y_1052_, 0);
v_pos_1058_ = lean_ctor_get(v___y_1052_, 1);
v_endPos_1059_ = lean_ctor_get(v___y_1052_, 2);
v_keepFullRange_1060_ = lean_ctor_get_uint8(v___y_1052_, sizeof(void*)*5);
v_isSilent_1061_ = lean_ctor_get_uint8(v___y_1052_, sizeof(void*)*5 + 2);
v_caption_1062_ = lean_ctor_get(v___y_1052_, 3);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___y_1052_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v___y_1052_, 4);
lean_dec(v_unused_1078_);
v___x_1064_ = v___y_1052_;
v_isShared_1065_ = v_isSharedCheck_1077_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_caption_1062_);
lean_inc(v_endPos_1059_);
lean_inc(v_pos_1058_);
lean_inc(v_fileName_1057_);
lean_dec(v___y_1052_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1077_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
uint8_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1066_ = 2;
v___x_1067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0));
v___x_1068_ = l_Nat_reprFast(v___y_1054_);
v___x_1069_ = lean_string_append(v___x_1067_, v___x_1068_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1));
v___x_1071_ = lean_string_append(v___x_1069_, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
v___x_1073_ = l_Lean_MessageData_ofFormat(v___x_1072_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 4, v___x_1073_);
v___x_1075_ = v___x_1064_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_fileName_1057_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_pos_1058_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_endPos_1059_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_caption_1062_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v___x_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1076_, sizeof(void*)*5, v_keepFullRange_1060_);
lean_ctor_set_uint8(v_reuseFailAlloc_1076_, sizeof(void*)*5 + 2, v_isSilent_1061_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*5 + 1, v___x_1066_);
v___y_1026_ = v___y_1055_;
v___y_1027_ = v___y_1053_;
v___y_1028_ = v___x_1075_;
v_isSilent_1029_ = v_isSilent_1061_;
goto v___jp_1025_;
}
}
}
}
v___jp_1080_:
{
lean_object* v_numErrors_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v_numErrors_1083_ = lean_nat_add(v_b_1005_, v___y_1082_);
lean_dec(v_b_1005_);
v___x_1084_ = l_Lean_Language_maxErrors;
v___x_1085_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_998_, v___x_1084_);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = lean_nat_dec_eq(v___x_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
uint8_t v___x_1088_; 
v___x_1088_ = lean_nat_dec_lt(v___x_1085_, v_numErrors_1083_);
v___y_1052_ = v___y_1081_;
v___y_1053_ = v_numErrors_1083_;
v___y_1054_ = v___x_1085_;
v___y_1055_ = v___x_1088_;
goto v___jp_1051_;
}
else
{
v___y_1052_ = v___y_1081_;
v___y_1053_ = v_numErrors_1083_;
v___y_1054_ = v___x_1085_;
v___y_1055_ = v___x_1079_;
goto v___jp_1051_;
}
}
v___jp_1089_:
{
if (v_severity_1091_ == 2)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_unsigned_to_nat(1u);
v___y_1081_ = v___y_1090_;
v___y_1082_ = v___x_1092_;
goto v___jp_1080_;
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_unsigned_to_nat(0u);
v___y_1081_ = v___y_1090_;
v___y_1082_ = v___x_1093_;
goto v___jp_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___boxed(lean_object* v_opts_1121_, lean_object* v_json_1122_, lean_object* v_includeEndPos_1123_, lean_object* v_severityOverrides_1124_, lean_object* v_as_1125_, lean_object* v_i_1126_, lean_object* v_stop_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v_json_boxed_1130_; uint8_t v_includeEndPos_boxed_1131_; size_t v_i_boxed_1132_; size_t v_stop_boxed_1133_; lean_object* v_res_1134_; 
v_json_boxed_1130_ = lean_unbox(v_json_1122_);
v_includeEndPos_boxed_1131_ = lean_unbox(v_includeEndPos_1123_);
v_i_boxed_1132_ = lean_unbox_usize(v_i_1126_);
lean_dec(v_i_1126_);
v_stop_boxed_1133_ = lean_unbox_usize(v_stop_1127_);
lean_dec(v_stop_1127_);
v_res_1134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1121_, v_json_boxed_1130_, v_includeEndPos_boxed_1131_, v_severityOverrides_1124_, v_as_1125_, v_i_boxed_1132_, v_stop_boxed_1133_, v_b_1128_);
lean_dec_ref(v_as_1125_);
lean_dec(v_severityOverrides_1124_);
lean_dec_ref(v_opts_1121_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(lean_object* v_opts_1135_, uint8_t v_json_1136_, uint8_t v_includeEndPos_1137_, lean_object* v_severityOverrides_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
if (lean_obj_tag(v_x_1139_) == 0)
{
lean_object* v_cs_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1155_; 
v_cs_1142_ = lean_ctor_get(v_x_1139_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1144_ = v_x_1139_;
v_isShared_1145_ = v_isSharedCheck_1155_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_cs_1142_);
lean_dec(v_x_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1155_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_array_get_size(v_cs_1142_);
v___x_1148_ = lean_nat_dec_lt(v___x_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1150_; 
lean_dec_ref(v_cs_1142_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v_x_1140_);
v___x_1150_ = v___x_1144_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_x_1140_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
lean_del_object(v___x_1144_);
v___x_1152_ = ((size_t)0ULL);
v___x_1153_ = lean_usize_of_nat(v___x_1147_);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1135_, v_json_1136_, v_includeEndPos_1137_, v_severityOverrides_1138_, v_cs_1142_, v___x_1152_, v___x_1153_, v_x_1140_);
lean_dec_ref(v_cs_1142_);
return v___x_1154_;
}
}
}
else
{
lean_object* v_vs_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1169_; 
v_vs_1156_ = lean_ctor_get(v_x_1139_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1158_ = v_x_1139_;
v_isShared_1159_ = v_isSharedCheck_1169_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_vs_1156_);
lean_dec(v_x_1139_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1169_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_array_get_size(v_vs_1156_);
v___x_1162_ = lean_nat_dec_lt(v___x_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1164_; 
lean_dec_ref(v_vs_1156_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set_tag(v___x_1158_, 0);
lean_ctor_set(v___x_1158_, 0, v_x_1140_);
v___x_1164_ = v___x_1158_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_x_1140_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
else
{
size_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
lean_del_object(v___x_1158_);
v___x_1166_ = ((size_t)0ULL);
v___x_1167_ = lean_usize_of_nat(v___x_1161_);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1135_, v_json_1136_, v_includeEndPos_1137_, v_severityOverrides_1138_, v_vs_1156_, v___x_1166_, v___x_1167_, v_x_1140_);
lean_dec_ref(v_vs_1156_);
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(lean_object* v_opts_1170_, uint8_t v_json_1171_, uint8_t v_includeEndPos_1172_, lean_object* v_severityOverrides_1173_, lean_object* v_as_1174_, size_t v_i_1175_, size_t v_stop_1176_, lean_object* v_b_1177_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_usize_dec_eq(v_i_1175_, v_stop_1176_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_array_uget_borrowed(v_as_1174_, v_i_1175_);
lean_inc(v___x_1180_);
v___x_1181_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1170_, v_json_1171_, v_includeEndPos_1172_, v_severityOverrides_1173_, v___x_1180_, v_b_1177_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; size_t v___x_1183_; size_t v___x_1184_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_add(v_i_1175_, v___x_1183_);
v_i_1175_ = v___x_1184_;
v_b_1177_ = v_a_1182_;
goto _start;
}
else
{
return v___x_1181_;
}
}
else
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_b_1177_);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5___boxed(lean_object* v_opts_1187_, lean_object* v_json_1188_, lean_object* v_includeEndPos_1189_, lean_object* v_severityOverrides_1190_, lean_object* v_as_1191_, lean_object* v_i_1192_, lean_object* v_stop_1193_, lean_object* v_b_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v_json_boxed_1196_; uint8_t v_includeEndPos_boxed_1197_; size_t v_i_boxed_1198_; size_t v_stop_boxed_1199_; lean_object* v_res_1200_; 
v_json_boxed_1196_ = lean_unbox(v_json_1188_);
v_includeEndPos_boxed_1197_ = lean_unbox(v_includeEndPos_1189_);
v_i_boxed_1198_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_stop_boxed_1199_ = lean_unbox_usize(v_stop_1193_);
lean_dec(v_stop_1193_);
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1187_, v_json_boxed_1196_, v_includeEndPos_boxed_1197_, v_severityOverrides_1190_, v_as_1191_, v_i_boxed_1198_, v_stop_boxed_1199_, v_b_1194_);
lean_dec_ref(v_as_1191_);
lean_dec(v_severityOverrides_1190_);
lean_dec_ref(v_opts_1187_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6___boxed(lean_object* v_opts_1201_, lean_object* v_json_1202_, lean_object* v_includeEndPos_1203_, lean_object* v_severityOverrides_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_, lean_object* v___y_1207_){
_start:
{
uint8_t v_json_boxed_1208_; uint8_t v_includeEndPos_boxed_1209_; lean_object* v_res_1210_; 
v_json_boxed_1208_ = lean_unbox(v_json_1202_);
v_includeEndPos_boxed_1209_ = lean_unbox(v_includeEndPos_1203_);
v_res_1210_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1201_, v_json_boxed_1208_, v_includeEndPos_boxed_1209_, v_severityOverrides_1204_, v_x_1205_, v_x_1206_);
lean_dec(v_severityOverrides_1204_);
lean_dec_ref(v_opts_1201_);
return v_res_1210_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(lean_object* v_opts_1212_, uint8_t v_json_1213_, uint8_t v_includeEndPos_1214_, lean_object* v_severityOverrides_1215_, lean_object* v_x_1216_, size_t v_x_1217_, size_t v_x_1218_, lean_object* v_x_1219_){
_start:
{
if (lean_obj_tag(v_x_1216_) == 0)
{
lean_object* v_cs_1221_; lean_object* v___x_1222_; size_t v___x_1223_; lean_object* v_j_1224_; lean_object* v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; lean_object* v___x_1232_; 
v_cs_1221_ = lean_ctor_get(v_x_1216_, 0);
lean_inc_ref(v_cs_1221_);
lean_dec_ref_known(v_x_1216_, 1);
v___x_1222_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0);
v___x_1223_ = lean_usize_shift_right(v_x_1217_, v_x_1218_);
v_j_1224_ = lean_usize_to_nat(v___x_1223_);
v___x_1225_ = lean_array_get_borrowed(v___x_1222_, v_cs_1221_, v_j_1224_);
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_shift_left(v___x_1226_, v_x_1218_);
v___x_1228_ = lean_usize_sub(v___x_1227_, v___x_1226_);
v___x_1229_ = lean_usize_land(v_x_1217_, v___x_1228_);
v___x_1230_ = ((size_t)5ULL);
v___x_1231_ = lean_usize_sub(v_x_1218_, v___x_1230_);
lean_inc(v___x_1225_);
v___x_1232_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1212_, v_json_1213_, v_includeEndPos_1214_, v_severityOverrides_1215_, v___x_1225_, v___x_1229_, v___x_1231_, v_x_1219_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v_j_1224_, v___x_1234_);
lean_dec(v_j_1224_);
v___x_1236_ = lean_array_get_size(v_cs_1221_);
v___x_1237_ = lean_nat_dec_lt(v___x_1235_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_dec(v___x_1235_);
lean_dec_ref(v_cs_1221_);
return v___x_1232_;
}
else
{
size_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1238_ = lean_usize_of_nat(v___x_1235_);
lean_dec(v___x_1235_);
v___x_1239_ = lean_usize_of_nat(v___x_1236_);
v___x_1240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1212_, v_json_1213_, v_includeEndPos_1214_, v_severityOverrides_1215_, v_cs_1221_, v___x_1238_, v___x_1239_, v_a_1233_);
lean_dec_ref(v_cs_1221_);
return v___x_1240_;
}
}
else
{
lean_dec(v_j_1224_);
lean_dec_ref(v_cs_1221_);
return v___x_1232_;
}
}
else
{
lean_object* v_vs_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1254_; 
v_vs_1241_ = lean_ctor_get(v_x_1216_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_x_1216_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1243_ = v_x_1216_;
v_isShared_1244_ = v_isSharedCheck_1254_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_vs_1241_);
lean_dec(v_x_1216_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1254_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1245_ = lean_usize_to_nat(v_x_1217_);
v___x_1246_ = lean_array_get_size(v_vs_1241_);
v___x_1247_ = lean_nat_dec_lt(v___x_1245_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1249_; 
lean_dec(v___x_1245_);
lean_dec_ref(v_vs_1241_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set_tag(v___x_1243_, 0);
lean_ctor_set(v___x_1243_, 0, v_x_1219_);
v___x_1249_ = v___x_1243_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_x_1219_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
else
{
size_t v___x_1251_; size_t v___x_1252_; lean_object* v___x_1253_; 
lean_del_object(v___x_1243_);
v___x_1251_ = lean_usize_of_nat(v___x_1245_);
lean_dec(v___x_1245_);
v___x_1252_ = lean_usize_of_nat(v___x_1246_);
v___x_1253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1212_, v_json_1213_, v_includeEndPos_1214_, v_severityOverrides_1215_, v_vs_1241_, v___x_1251_, v___x_1252_, v_x_1219_);
lean_dec_ref(v_vs_1241_);
return v___x_1253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___boxed(lean_object* v_opts_1255_, lean_object* v_json_1256_, lean_object* v_includeEndPos_1257_, lean_object* v_severityOverrides_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v_json_boxed_1264_; uint8_t v_includeEndPos_boxed_1265_; size_t v_x_2228__boxed_1266_; size_t v_x_2229__boxed_1267_; lean_object* v_res_1268_; 
v_json_boxed_1264_ = lean_unbox(v_json_1256_);
v_includeEndPos_boxed_1265_ = lean_unbox(v_includeEndPos_1257_);
v_x_2228__boxed_1266_ = lean_unbox_usize(v_x_1260_);
lean_dec(v_x_1260_);
v_x_2229__boxed_1267_ = lean_unbox_usize(v_x_1261_);
lean_dec(v_x_1261_);
v_res_1268_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1255_, v_json_boxed_1264_, v_includeEndPos_boxed_1265_, v_severityOverrides_1258_, v_x_1259_, v_x_2228__boxed_1266_, v_x_2229__boxed_1267_, v_x_1262_);
lean_dec(v_severityOverrides_1258_);
lean_dec_ref(v_opts_1255_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(lean_object* v_opts_1269_, uint8_t v_json_1270_, uint8_t v_includeEndPos_1271_, lean_object* v_severityOverrides_1272_, lean_object* v_t_1273_, lean_object* v_init_1274_, lean_object* v_start_1275_){
_start:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = lean_nat_dec_eq(v_start_1275_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v_root_1279_; lean_object* v_tail_1280_; size_t v_shift_1281_; lean_object* v_tailOff_1282_; uint8_t v___x_1283_; 
v_root_1279_ = lean_ctor_get(v_t_1273_, 0);
lean_inc_ref(v_root_1279_);
v_tail_1280_ = lean_ctor_get(v_t_1273_, 1);
lean_inc_ref(v_tail_1280_);
v_shift_1281_ = lean_ctor_get_usize(v_t_1273_, 4);
v_tailOff_1282_ = lean_ctor_get(v_t_1273_, 3);
lean_inc(v_tailOff_1282_);
lean_dec_ref(v_t_1273_);
v___x_1283_ = lean_nat_dec_le(v_tailOff_1282_, v_start_1275_);
if (v___x_1283_ == 0)
{
size_t v___x_1284_; lean_object* v___x_1285_; 
lean_dec(v_tailOff_1282_);
v___x_1284_ = lean_usize_of_nat(v_start_1275_);
v___x_1285_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1269_, v_json_1270_, v_includeEndPos_1271_, v_severityOverrides_1272_, v_root_1279_, v___x_1284_, v_shift_1281_, v_init_1274_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v___x_1287_ = lean_array_get_size(v_tail_1280_);
v___x_1288_ = lean_nat_dec_lt(v___x_1277_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_dec_ref(v_tail_1280_);
return v___x_1285_;
}
else
{
size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; 
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = lean_usize_of_nat(v___x_1287_);
v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1269_, v_json_1270_, v_includeEndPos_1271_, v_severityOverrides_1272_, v_tail_1280_, v___x_1289_, v___x_1290_, v_a_1286_);
lean_dec_ref(v_tail_1280_);
return v___x_1291_;
}
}
else
{
lean_dec_ref(v_tail_1280_);
return v___x_1285_;
}
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
lean_dec_ref(v_root_1279_);
v___x_1292_ = lean_nat_sub(v_start_1275_, v_tailOff_1282_);
lean_dec(v_tailOff_1282_);
v___x_1293_ = lean_array_get_size(v_tail_1280_);
v___x_1294_ = lean_nat_dec_lt(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; 
lean_dec(v___x_1292_);
lean_dec_ref(v_tail_1280_);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v_init_1274_);
return v___x_1295_;
}
else
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_usize_of_nat(v___x_1292_);
lean_dec(v___x_1292_);
v___x_1297_ = lean_usize_of_nat(v___x_1293_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1269_, v_json_1270_, v_includeEndPos_1271_, v_severityOverrides_1272_, v_tail_1280_, v___x_1296_, v___x_1297_, v_init_1274_);
lean_dec_ref(v_tail_1280_);
return v___x_1298_;
}
}
}
else
{
lean_object* v_root_1299_; lean_object* v_tail_1300_; lean_object* v___x_1301_; 
v_root_1299_ = lean_ctor_get(v_t_1273_, 0);
lean_inc_ref(v_root_1299_);
v_tail_1300_ = lean_ctor_get(v_t_1273_, 1);
lean_inc_ref(v_tail_1300_);
lean_dec_ref(v_t_1273_);
v___x_1301_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1269_, v_json_1270_, v_includeEndPos_1271_, v_severityOverrides_1272_, v_root_1299_, v_init_1274_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v___x_1303_ = lean_array_get_size(v_tail_1300_);
v___x_1304_ = lean_nat_dec_lt(v___x_1277_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_dec_ref(v_tail_1300_);
return v___x_1301_;
}
else
{
size_t v___x_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v___x_1305_ = ((size_t)0ULL);
v___x_1306_ = lean_usize_of_nat(v___x_1303_);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1269_, v_json_1270_, v_includeEndPos_1271_, v_severityOverrides_1272_, v_tail_1300_, v___x_1305_, v___x_1306_, v_a_1302_);
lean_dec_ref(v_tail_1300_);
return v___x_1307_;
}
}
else
{
lean_dec_ref(v_tail_1300_);
return v___x_1301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4___boxed(lean_object* v_opts_1308_, lean_object* v_json_1309_, lean_object* v_includeEndPos_1310_, lean_object* v_severityOverrides_1311_, lean_object* v_t_1312_, lean_object* v_init_1313_, lean_object* v_start_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v_json_boxed_1316_; uint8_t v_includeEndPos_boxed_1317_; lean_object* v_res_1318_; 
v_json_boxed_1316_ = lean_unbox(v_json_1309_);
v_includeEndPos_boxed_1317_ = lean_unbox(v_includeEndPos_1310_);
v_res_1318_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1308_, v_json_boxed_1316_, v_includeEndPos_boxed_1317_, v_severityOverrides_1311_, v_t_1312_, v_init_1313_, v_start_1314_);
lean_dec(v_start_1314_);
lean_dec(v_severityOverrides_1311_);
lean_dec_ref(v_opts_1308_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(lean_object* v_msgLog_1319_, lean_object* v_opts_1320_, uint8_t v_json_1321_, lean_object* v_severityOverrides_1322_, lean_object* v_numErrors_1323_){
_start:
{
lean_object* v_unreported_1325_; lean_object* v___x_1326_; uint8_t v_includeEndPos_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_unreported_1325_ = lean_ctor_get(v_msgLog_1319_, 1);
lean_inc_ref(v_unreported_1325_);
lean_dec_ref(v_msgLog_1319_);
v___x_1326_ = l_Lean_Language_printMessageEndPos;
v_includeEndPos_1327_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_1320_, v___x_1326_);
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1320_, v_json_1321_, v_includeEndPos_1327_, v_severityOverrides_1322_, v_unreported_1325_, v_numErrors_1323_, v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___boxed(lean_object* v_msgLog_1330_, lean_object* v_opts_1331_, lean_object* v_json_1332_, lean_object* v_severityOverrides_1333_, lean_object* v_numErrors_1334_, lean_object* v_a_1335_){
_start:
{
uint8_t v_json_boxed_1336_; lean_object* v_res_1337_; 
v_json_boxed_1336_ = lean_unbox(v_json_1332_);
v_res_1337_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1330_, v_opts_1331_, v_json_boxed_1336_, v_severityOverrides_1333_, v_numErrors_1334_);
lean_dec(v_severityOverrides_1333_);
lean_dec_ref(v_opts_1331_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object* v_opts_1338_, uint8_t v_json_1339_, lean_object* v_severityOverrides_1340_, lean_object* v_s_1341_, lean_object* v_init_1342_){
_start:
{
lean_object* v_element_1344_; lean_object* v_diagnostics_1345_; lean_object* v_children_1346_; lean_object* v_msgLog_1347_; lean_object* v___x_1348_; 
v_element_1344_ = lean_ctor_get(v_s_1341_, 0);
v_diagnostics_1345_ = lean_ctor_get(v_element_1344_, 1);
lean_inc_ref(v_diagnostics_1345_);
v_children_1346_ = lean_ctor_get(v_s_1341_, 1);
lean_inc_ref(v_children_1346_);
lean_dec_ref(v_s_1341_);
v_msgLog_1347_ = lean_ctor_get(v_diagnostics_1345_, 0);
lean_inc_ref(v_msgLog_1347_);
lean_dec_ref(v_diagnostics_1345_);
v___x_1348_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1347_, v_opts_1338_, v_json_1339_, v_severityOverrides_1340_, v_init_1342_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_array_get_size(v_children_1346_);
v___x_1352_ = lean_nat_dec_lt(v___x_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_dec_ref(v_children_1346_);
return v___x_1348_;
}
else
{
size_t v___x_1353_; size_t v___x_1354_; lean_object* v___x_1355_; 
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1353_ = ((size_t)0ULL);
v___x_1354_ = lean_usize_of_nat(v___x_1351_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1338_, v_json_1339_, v_severityOverrides_1340_, v_children_1346_, v___x_1353_, v___x_1354_, v_a_1349_);
lean_dec_ref(v_children_1346_);
return v___x_1355_;
}
}
else
{
lean_dec_ref(v_children_1346_);
return v___x_1348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object* v_opts_1356_, uint8_t v_json_1357_, lean_object* v_severityOverrides_1358_, lean_object* v_as_1359_, size_t v_i_1360_, size_t v_stop_1361_, lean_object* v_b_1362_){
_start:
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_usize_dec_eq(v_i_1360_, v_stop_1361_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = lean_array_uget_borrowed(v_as_1359_, v_i_1360_);
lean_inc(v___x_1365_);
v___x_1366_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1365_);
v___x_1367_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1356_, v_json_1357_, v_severityOverrides_1358_, v___x_1366_, v_b_1362_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; size_t v___x_1369_; size_t v___x_1370_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v___x_1369_ = ((size_t)1ULL);
v___x_1370_ = lean_usize_add(v_i_1360_, v___x_1369_);
v_i_1360_ = v___x_1370_;
v_b_1362_ = v_a_1368_;
goto _start;
}
else
{
return v___x_1367_;
}
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_b_1362_);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object* v_opts_1373_, lean_object* v_json_1374_, lean_object* v_severityOverrides_1375_, lean_object* v_as_1376_, lean_object* v_i_1377_, lean_object* v_stop_1378_, lean_object* v_b_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v_json_boxed_1381_; size_t v_i_boxed_1382_; size_t v_stop_boxed_1383_; lean_object* v_res_1384_; 
v_json_boxed_1381_ = lean_unbox(v_json_1374_);
v_i_boxed_1382_ = lean_unbox_usize(v_i_1377_);
lean_dec(v_i_1377_);
v_stop_boxed_1383_ = lean_unbox_usize(v_stop_1378_);
lean_dec(v_stop_1378_);
v_res_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1373_, v_json_boxed_1381_, v_severityOverrides_1375_, v_as_1376_, v_i_boxed_1382_, v_stop_boxed_1383_, v_b_1379_);
lean_dec_ref(v_as_1376_);
lean_dec(v_severityOverrides_1375_);
lean_dec_ref(v_opts_1373_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object* v_opts_1385_, lean_object* v_json_1386_, lean_object* v_severityOverrides_1387_, lean_object* v_s_1388_, lean_object* v_init_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v_json_boxed_1391_; lean_object* v_res_1392_; 
v_json_boxed_1391_ = lean_unbox(v_json_1386_);
v_res_1392_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1385_, v_json_boxed_1391_, v_severityOverrides_1387_, v_s_1388_, v_init_1389_);
lean_dec(v_severityOverrides_1387_);
lean_dec_ref(v_opts_1385_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object* v_s_1393_, lean_object* v_opts_1394_, uint8_t v_json_1395_, lean_object* v_severityOverrides_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1394_, v_json_1395_, v_severityOverrides_1396_, v_s_1393_, v___x_1398_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1409_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1409_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1409_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
uint8_t v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1404_ = lean_nat_dec_lt(v___x_1398_, v_a_1400_);
lean_dec(v_a_1400_);
v___x_1405_ = lean_box(v___x_1404_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1405_);
v___x_1407_ = v___x_1402_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_a_1410_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1399_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1399_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object* v_s_1418_, lean_object* v_opts_1419_, lean_object* v_json_1420_, lean_object* v_severityOverrides_1421_, lean_object* v_a_1422_){
_start:
{
uint8_t v_json_boxed_1423_; lean_object* v_res_1424_; 
v_json_boxed_1423_ = lean_unbox(v_json_1420_);
v_res_1424_ = l_Lean_Language_SnapshotTree_runAndReport(v_s_1418_, v_opts_1419_, v_json_boxed_1423_, v_severityOverrides_1421_);
lean_dec(v_severityOverrides_1421_);
lean_dec_ref(v_opts_1419_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(lean_object* v_s_1425_, lean_object* v_init_1426_){
_start:
{
lean_object* v_element_1427_; lean_object* v_children_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v_element_1427_ = lean_ctor_get(v_s_1425_, 0);
lean_inc_ref(v_element_1427_);
v_children_1428_ = lean_ctor_get(v_s_1425_, 1);
lean_inc_ref(v_children_1428_);
lean_dec_ref(v_s_1425_);
v___x_1429_ = lean_array_push(v_init_1426_, v_element_1427_);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_array_get_size(v_children_1428_);
v___x_1432_ = lean_nat_dec_lt(v___x_1430_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_dec_ref(v_children_1428_);
return v___x_1429_;
}
else
{
size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = lean_usize_of_nat(v___x_1431_);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_1428_, v___x_1433_, v___x_1434_, v___x_1429_);
lean_dec_ref(v_children_1428_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object* v_as_1436_, size_t v_i_1437_, size_t v_stop_1438_, lean_object* v_b_1439_){
_start:
{
uint8_t v___x_1440_; 
v___x_1440_ = lean_usize_dec_eq(v_i_1437_, v_stop_1438_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; 
v___x_1441_ = lean_array_uget_borrowed(v_as_1436_, v_i_1437_);
lean_inc(v___x_1441_);
v___x_1442_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1441_);
v___x_1443_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v___x_1442_, v_b_1439_);
v___x_1444_ = ((size_t)1ULL);
v___x_1445_ = lean_usize_add(v_i_1437_, v___x_1444_);
v_i_1437_ = v___x_1445_;
v_b_1439_ = v___x_1443_;
goto _start;
}
else
{
return v_b_1439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object* v_as_1447_, lean_object* v_i_1448_, lean_object* v_stop_1449_, lean_object* v_b_1450_){
_start:
{
size_t v_i_boxed_1451_; size_t v_stop_boxed_1452_; lean_object* v_res_1453_; 
v_i_boxed_1451_ = lean_unbox_usize(v_i_1448_);
lean_dec(v_i_1448_);
v_stop_boxed_1452_ = lean_unbox_usize(v_stop_1449_);
lean_dec(v_stop_1449_);
v_res_1453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_as_1447_, v_i_boxed_1451_, v_stop_boxed_1452_, v_b_1450_);
lean_dec_ref(v_as_1447_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object* v_s_1456_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = ((lean_object*)(l_Lean_Language_SnapshotTree_getAll___closed__0));
v___x_1458_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v_s_1456_, v___x_1457_);
return v___x_1458_;
}
}
static lean_object* _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_box(0);
v___x_1460_ = lean_task_pure(v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed(lean_object* v_tail_1461_, lean_object* v_t_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(v_tail_1461_, v_t_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(lean_object* v_a_1465_){
_start:
{
if (lean_obj_tag(v_a_1465_) == 0)
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_obj_once(&l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0, &l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0_once, _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0);
return v___x_1467_;
}
else
{
lean_object* v_head_1468_; lean_object* v_tail_1469_; lean_object* v_task_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; 
v_head_1468_ = lean_ctor_get(v_a_1465_, 0);
lean_inc(v_head_1468_);
v_tail_1469_ = lean_ctor_get(v_a_1465_, 1);
lean_inc(v_tail_1469_);
lean_dec_ref_known(v_a_1465_, 2);
v_task_1470_ = lean_ctor_get(v_head_1468_, 3);
lean_inc_ref(v_task_1470_);
lean_dec(v_head_1468_);
v___f_1471_ = lean_alloc_closure((void*)(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1471_, 0, v_tail_1469_);
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = 1;
v___x_1474_ = lean_io_bind_task(v_task_1470_, v___f_1471_, v___x_1472_, v___x_1473_);
return v___x_1474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object* v_tail_1475_, lean_object* v_t_1476_){
_start:
{
lean_object* v_children_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_children_1478_ = lean_ctor_get(v_t_1476_, 1);
lean_inc_ref(v_children_1478_);
lean_dec_ref(v_t_1476_);
v___x_1479_ = lean_array_to_list(v_children_1478_);
v___x_1480_ = l_List_appendTR___redArg(v___x_1479_, v_tail_1475_);
v___x_1481_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___boxed(lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v_a_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object* v_x_1485_){
_start:
{
lean_object* v_children_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_children_1487_ = lean_ctor_get(v_x_1485_, 1);
lean_inc_ref(v_children_1487_);
lean_dec_ref(v_x_1485_);
v___x_1488_ = lean_array_to_list(v_children_1487_);
v___x_1489_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll___boxed(lean_object* v_x_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Language_SnapshotTree_waitAll(v_x_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object* v_00_u03b1_1493_, lean_object* v_act_1494_, lean_object* v_ctx_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_apply_2(v_act_1494_, v_ctx_1495_, lean_box(0));
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0___boxed(lean_object* v_00_u03b1_1499_, lean_object* v_act_1500_, lean_object* v_ctx_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(v_00_u03b1_1499_, v_act_1500_, v_ctx_1501_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object* v_msgLog_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1508_ = lean_box(0);
v___x_1509_ = lean_st_mk_ref(v___x_1508_);
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v_msgLog_1506_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog___boxed(lean_object* v_msgLog_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object* v_msg_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_fileMap_1522_; lean_object* v_source_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_fileMap_1522_ = lean_ctor_get(v_a_1520_, 2);
v_source_1523_ = lean_ctor_get(v_fileMap_1522_, 0);
v___x_1524_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__0));
v___x_1525_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__1));
v___x_1526_ = lean_string_utf8_byte_size(v_source_1523_);
lean_inc_ref(v_fileMap_1522_);
v___x_1527_ = l_Lean_FileMap_toPosition(v_fileMap_1522_, v___x_1526_);
v___x_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
v___x_1529_ = 0;
v___x_1530_ = 2;
v___x_1531_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot___closed__0));
v___x_1532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_msg_1519_);
v___x_1533_ = l_Lean_MessageData_ofFormat(v___x_1532_);
v___x_1534_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1534_, 0, v___x_1524_);
lean_ctor_set(v___x_1534_, 1, v___x_1525_);
lean_ctor_set(v___x_1534_, 2, v___x_1528_);
lean_ctor_set(v___x_1534_, 3, v___x_1531_);
lean_ctor_set(v___x_1534_, 4, v___x_1533_);
lean_ctor_set_uint8(v___x_1534_, sizeof(void*)*5, v___x_1529_);
lean_ctor_set_uint8(v___x_1534_, sizeof(void*)*5 + 1, v___x_1530_);
lean_ctor_set_uint8(v___x_1534_, sizeof(void*)*5 + 2, v___x_1529_);
v___x_1535_ = l_Lean_MessageLog_empty;
v___x_1536_ = l_Lean_MessageLog_add(v___x_1534_, v___x_1535_);
v___x_1537_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError___boxed(lean_object* v_msg_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_Language_diagnosticsOfHeaderError(v_msg_1538_, v_a_1539_);
lean_dec_ref(v_a_1539_);
return v_res_1541_;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2(void){
_start:
{
uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = 1;
v___x_1548_ = ((lean_object*)(l_Lean_Language_withHeaderExceptions___redArg___closed__1));
v___x_1549_ = l_Lean_Name_toString(v___x_1548_, v___x_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object* v_ex_1550_, lean_object* v_act_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1554_; 
lean_inc_ref(v_a_1552_);
v___x_1554_ = lean_apply_2(v_act_1551_, v_a_1552_, lean_box(0));
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; 
lean_dec(v_ex_1550_);
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
return v_a_1555_;
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_a_1556_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1557_ = lean_io_error_to_string(v_a_1556_);
v___x_1558_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_1557_, v_a_1552_);
v___x_1559_ = lean_obj_once(&l_Lean_Language_withHeaderExceptions___redArg___closed__2, &l_Lean_Language_withHeaderExceptions___redArg___closed__2_once, _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2);
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_1562_ = 0;
v___x_1563_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1563_, 0, v___x_1559_);
lean_ctor_set(v___x_1563_, 1, v___x_1558_);
lean_ctor_set(v___x_1563_, 2, v___x_1560_);
lean_ctor_set(v___x_1563_, 3, v___x_1561_);
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*4, v___x_1562_);
v___x_1564_ = lean_apply_1(v_ex_1550_, v___x_1563_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg___boxed(lean_object* v_ex_1565_, lean_object* v_act_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1565_, v_act_1566_, v_a_1567_);
lean_dec_ref(v_a_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object* v_00_u03b1_1570_, lean_object* v_ex_1571_, lean_object* v_act_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1571_, v_act_1572_, v_a_1573_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___boxed(lean_object* v_00_u03b1_1576_, lean_object* v_ex_1577_, lean_object* v_act_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Language_withHeaderExceptions(v_00_u03b1_1576_, v_ex_1577_, v_act_1578_, v_a_1579_);
lean_dec_ref(v_a_1579_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object* v_val_1582_, lean_object* v_process_1583_, lean_object* v_ictx_1584_){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1586_ = lean_st_ref_get(v_val_1582_);
v___x_1587_ = lean_apply_3(v_process_1583_, v___x_1586_, v_ictx_1584_, lean_box(0));
lean_inc(v___x_1587_);
v___x_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
v___x_1589_ = lean_st_ref_swap(v_val_1582_, v___x_1588_);
lean_dec(v___x_1589_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object* v_val_1590_, lean_object* v_process_1591_, lean_object* v_ictx_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(v_val_1590_, v_process_1591_, v_ictx_1592_);
lean_dec(v_val_1590_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object* v_process_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___f_1599_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_st_mk_ref(v___x_1597_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1599_, 0, v___x_1598_);
lean_closure_set(v___f_1599_, 1, v_process_1595_);
return v___f_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___boxed(lean_object* v_process_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object* v_InitSnap_1603_, lean_object* v_process_1604_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___boxed(lean_object* v_InitSnap_1607_, lean_object* v_process_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Language_mkIncrementalProcessor(v_InitSnap_1607_, v_process_1608_);
return v_res_1610_;
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
