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
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(lean_object* v_x_141_){
_start:
{
switch(lean_obj_tag(v_x_141_))
{
case 0:
{
lean_object* v___x_142_; 
v___x_142_ = lean_unsigned_to_nat(0u);
return v___x_142_;
}
case 1:
{
lean_object* v___x_143_; 
v___x_143_ = lean_unsigned_to_nat(1u);
return v___x_143_;
}
default: 
{
lean_object* v___x_144_; 
v___x_144_ = lean_unsigned_to_nat(2u);
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___boxed(lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(v_x_145_);
lean_dec(v_x_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(lean_object* v_t_147_, lean_object* v_k_148_){
_start:
{
if (lean_obj_tag(v_t_147_) == 1)
{
lean_object* v_range_149_; lean_object* v___x_150_; 
v_range_149_ = lean_ctor_get(v_t_147_, 0);
lean_inc_ref(v_range_149_);
lean_dec_ref_known(v_t_147_, 1);
v___x_150_ = lean_apply_1(v_k_148_, v_range_149_);
return v___x_150_;
}
else
{
lean_dec(v_t_147_);
return v_k_148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(lean_object* v_motive_151_, lean_object* v_ctorIdx_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_k_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_153_, v_k_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___boxed(lean_object* v_motive_157_, lean_object* v_ctorIdx_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_k_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(v_motive_157_, v_ctorIdx_158_, v_t_159_, v_h_160_, v_k_161_);
lean_dec(v_ctorIdx_158_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim___redArg(lean_object* v_t_163_, lean_object* v_inherit_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_163_, v_inherit_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim(lean_object* v_motive_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_inherit_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_167_, v_inherit_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim___redArg(lean_object* v_t_171_, lean_object* v_some_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_171_, v_some_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim(lean_object* v_motive_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_some_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_175_, v_some_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim___redArg(lean_object* v_t_179_, lean_object* v_skip_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_179_, v_skip_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim(lean_object* v_motive_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_skip_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_183_, v_skip_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default(void){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_box(0);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange(void){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(0);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(lean_object* v_x_189_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(0);
return v___x_190_;
}
else
{
lean_object* v_val_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
v_val_191_ = lean_ctor_get(v_x_189_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v_x_189_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v_x_189_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_val_191_);
lean_dec(v_x_189_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_val_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(0);
v___x_200_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object* v_stx_x3f_201_){
_start:
{
if (lean_obj_tag(v_stx_x3f_201_) == 0)
{
lean_object* v___x_202_; 
v___x_202_ = lean_obj_once(&l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0, &l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0_once, _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0);
return v___x_202_;
}
else
{
lean_object* v_val_203_; uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_val_203_ = lean_ctor_get(v_stx_x3f_201_, 0);
v___x_204_ = 1;
v___x_205_ = l_Lean_Syntax_getRange_x3f(v_val_203_, v___x_204_);
v___x_206_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___x_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange___boxed(lean_object* v_stx_x3f_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v_stx_x3f_207_);
lean_dec(v_stx_x3f_207_);
return v_res_208_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_box(0);
v___x_210_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object* v_inst_211_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_212_ = lean_box(0);
v___x_213_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0, &l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0_once, _init_l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0);
v___x_214_ = lean_task_pure(v_inst_211_);
v___x_215_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_215_, 0, v___x_212_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
lean_ctor_set(v___x_215_, 2, v___x_212_);
lean_ctor_set(v___x_215_, 3, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default(lean_object* v_00_u03b1_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask___redArg(lean_object* v_inst_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask(lean_object* v_a_221_, lean_object* v_inst_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object* v_stx_x3f_224_, lean_object* v_cancelTk_x3f_225_, lean_object* v_reportingRange_226_, lean_object* v_act_227_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_io_as_task(v_act_227_, v___x_229_);
v___x_231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_231_, 0, v_stx_x3f_224_);
lean_ctor_set(v___x_231_, 1, v_reportingRange_226_);
lean_ctor_set(v___x_231_, 2, v_cancelTk_x3f_225_);
lean_ctor_set(v___x_231_, 3, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg___boxed(lean_object* v_stx_x3f_232_, lean_object* v_cancelTk_x3f_233_, lean_object* v_reportingRange_234_, lean_object* v_act_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v_stx_x3f_232_, v_cancelTk_x3f_233_, v_reportingRange_234_, v_act_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object* v_00_u03b1_238_, lean_object* v_stx_x3f_239_, lean_object* v_cancelTk_x3f_240_, lean_object* v_reportingRange_241_, lean_object* v_act_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v_stx_x3f_239_, v_cancelTk_x3f_240_, v_reportingRange_241_, v_act_242_);
return v___x_244_;
}
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
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object* v_t_262_, lean_object* v_f_263_, lean_object* v_stx_x3f_264_, lean_object* v_reportingRange_265_, uint8_t v_sync_266_){
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
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg___boxed(lean_object* v_t_280_, lean_object* v_f_281_, lean_object* v_stx_x3f_282_, lean_object* v_reportingRange_283_, lean_object* v_sync_284_){
_start:
{
uint8_t v_sync_boxed_285_; lean_object* v_res_286_; 
v_sync_boxed_285_ = lean_unbox(v_sync_284_);
v_res_286_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_280_, v_f_281_, v_stx_x3f_282_, v_reportingRange_283_, v_sync_boxed_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map(lean_object* v_00_u03b1_287_, lean_object* v_00_u03b2_288_, lean_object* v_t_289_, lean_object* v_f_290_, lean_object* v_stx_x3f_291_, lean_object* v_reportingRange_292_, uint8_t v_sync_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_289_, v_f_290_, v_stx_x3f_291_, v_reportingRange_292_, v_sync_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___boxed(lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_t_297_, lean_object* v_f_298_, lean_object* v_stx_x3f_299_, lean_object* v_reportingRange_300_, lean_object* v_sync_301_){
_start:
{
uint8_t v_sync_boxed_302_; lean_object* v_res_303_; 
v_sync_boxed_302_ = lean_unbox(v_sync_301_);
v_res_303_ = l_Lean_Language_SnapshotTask_map(v_00_u03b1_295_, v_00_u03b2_296_, v_t_297_, v_f_298_, v_stx_x3f_299_, v_reportingRange_300_, v_sync_boxed_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(lean_object* v_act_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_task_308_; 
v___x_307_ = lean_apply_2(v_act_304_, v_a_305_, lean_box(0));
v_task_308_ = lean_ctor_get(v___x_307_, 3);
lean_inc_ref(v_task_308_);
lean_dec_ref(v___x_307_);
return v_task_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed(lean_object* v_act_309_, lean_object* v_a_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(v_act_309_, v_a_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object* v_t_313_, lean_object* v_act_314_, lean_object* v_stx_x3f_315_, lean_object* v_reportingRange_316_, lean_object* v_cancelTk_x3f_317_, uint8_t v_sync_318_){
_start:
{
lean_object* v_task_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_330_; 
v_task_320_ = lean_ctor_get(v_t_313_, 3);
v_isSharedCheck_330_ = !lean_is_exclusive(v_t_313_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; lean_object* v_unused_332_; lean_object* v_unused_333_; 
v_unused_331_ = lean_ctor_get(v_t_313_, 2);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_t_313_, 1);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_t_313_, 0);
lean_dec(v_unused_333_);
v___x_322_ = v_t_313_;
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_task_320_);
lean_dec(v_t_313_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___f_324_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_324_, 0, v_act_314_);
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_io_bind_task(v_task_320_, v___f_324_, v___x_325_, v_sync_318_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 3, v___x_326_);
lean_ctor_set(v___x_322_, 2, v_cancelTk_x3f_317_);
lean_ctor_set(v___x_322_, 1, v_reportingRange_316_);
lean_ctor_set(v___x_322_, 0, v_stx_x3f_315_);
v___x_328_ = v___x_322_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_stx_x3f_315_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_reportingRange_316_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v_cancelTk_x3f_317_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___boxed(lean_object* v_t_334_, lean_object* v_act_335_, lean_object* v_stx_x3f_336_, lean_object* v_reportingRange_337_, lean_object* v_cancelTk_x3f_338_, lean_object* v_sync_339_, lean_object* v_a_340_){
_start:
{
uint8_t v_sync_boxed_341_; lean_object* v_res_342_; 
v_sync_boxed_341_ = lean_unbox(v_sync_339_);
v_res_342_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_t_334_, v_act_335_, v_stx_x3f_336_, v_reportingRange_337_, v_cancelTk_x3f_338_, v_sync_boxed_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_t_345_, lean_object* v_act_346_, lean_object* v_stx_x3f_347_, lean_object* v_reportingRange_348_, lean_object* v_cancelTk_x3f_349_, uint8_t v_sync_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_t_345_, v_act_346_, v_stx_x3f_347_, v_reportingRange_348_, v_cancelTk_x3f_349_, v_sync_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___boxed(lean_object* v_00_u03b1_353_, lean_object* v_00_u03b2_354_, lean_object* v_t_355_, lean_object* v_act_356_, lean_object* v_stx_x3f_357_, lean_object* v_reportingRange_358_, lean_object* v_cancelTk_x3f_359_, lean_object* v_sync_360_, lean_object* v_a_361_){
_start:
{
uint8_t v_sync_boxed_362_; lean_object* v_res_363_; 
v_sync_boxed_362_ = lean_unbox(v_sync_360_);
v_res_363_ = l_Lean_Language_SnapshotTask_bindIO(v_00_u03b1_353_, v_00_u03b2_354_, v_t_355_, v_act_356_, v_stx_x3f_357_, v_reportingRange_358_, v_cancelTk_x3f_359_, v_sync_boxed_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object* v_t_364_){
_start:
{
lean_object* v_task_365_; lean_object* v___x_366_; 
v_task_365_ = lean_ctor_get(v_t_364_, 3);
lean_inc_ref(v_task_365_);
lean_dec_ref(v_t_364_);
v___x_366_ = lean_task_get_own(v_task_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object* v_00_u03b1_367_, lean_object* v_t_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Language_SnapshotTask_get___redArg(v_t_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object* v_t_370_){
_start:
{
lean_object* v_task_372_; uint8_t v___x_373_; 
v_task_372_ = lean_ctor_get(v_t_370_, 3);
lean_inc_ref(v_task_372_);
lean_dec_ref(v_t_370_);
v___x_373_ = lean_io_get_task_state(v_task_372_);
if (v___x_373_ == 2)
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_task_get_own(v_task_372_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; 
lean_dec_ref(v_task_372_);
v___x_376_ = lean_box(0);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg___boxed(lean_object* v_t_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object* v_00_u03b1_380_, lean_object* v_t_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_381_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___boxed(lean_object* v_00_u03b1_384_, lean_object* v_t_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Language_SnapshotTask_get_x3f(v_00_u03b1_384_, v_t_385_);
return v_res_387_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshotTree_default___closed__0));
v___x_391_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_390_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default(void){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshotTree_default___closed__1, &l_Lean_Language_instInhabitedSnapshotTree_default___closed__1_once, _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree(void){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_394_;
}
}
LEAN_EXPORT uint8_t l_Lean_Language_SnapshotTreeTransform_isIdentity(lean_object* v_trans_408_){
_start:
{
lean_object* v_startPos_409_; lean_object* v_stopPos_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_startPos_409_ = lean_ctor_get(v_trans_408_, 1);
v_stopPos_410_ = lean_ctor_get(v_trans_408_, 2);
v___x_411_ = lean_nat_sub(v_stopPos_410_, v_startPos_409_);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_nat_dec_eq(v___x_411_, v___x_412_);
lean_dec(v___x_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_isIdentity___boxed(lean_object* v_trans_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_trans_414_);
lean_dec_ref(v_trans_414_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformSyntax(lean_object* v_trans_417_, lean_object* v_stx_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Syntax_addTrailing(v_stx_418_, v_trans_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformInfoTree(lean_object* v_trans_420_, lean_object* v_t_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Elab_InfoTree_addTrailing(v_trans_420_, v_t_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformInfoTree_x3f(lean_object* v_trans_423_, lean_object* v_t_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Elab_InfoTree_addTrailing_x3f(v_trans_423_, v_t_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_compose(lean_object* v_outer_426_, lean_object* v_inner_427_){
_start:
{
lean_object* v_str_428_; lean_object* v_startPos_429_; lean_object* v_stopPos_430_; lean_object* v_startPos_431_; lean_object* v_stopPos_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
v_str_428_ = lean_ctor_get(v_inner_427_, 0);
v_startPos_429_ = lean_ctor_get(v_inner_427_, 1);
v_stopPos_430_ = lean_ctor_get(v_inner_427_, 2);
v_startPos_431_ = lean_ctor_get(v_outer_426_, 1);
v_stopPos_432_ = lean_ctor_get(v_outer_426_, 2);
v_isSharedCheck_440_ = !lean_is_exclusive(v_outer_426_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v_outer_426_, 0);
lean_dec(v_unused_441_);
v___x_434_ = v_outer_426_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_stopPos_432_);
lean_inc(v_startPos_431_);
lean_dec(v_outer_426_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
uint8_t v_decide_436_; 
v_decide_436_ = lean_nat_dec_eq(v_stopPos_430_, v_startPos_431_);
lean_dec(v_startPos_431_);
if (v_decide_436_ == 0)
{
lean_del_object(v___x_434_);
lean_dec(v_stopPos_432_);
lean_inc_ref(v_inner_427_);
return v_inner_427_;
}
else
{
lean_object* v___x_438_; 
lean_inc(v_startPos_429_);
lean_inc_ref(v_str_428_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v_startPos_429_);
lean_ctor_set(v___x_434_, 0, v_str_428_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_str_428_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_startPos_429_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_stopPos_432_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_compose___boxed(lean_object* v_outer_442_, lean_object* v_inner_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Language_SnapshotTreeTransform_compose(v_outer_442_, v_inner_443_);
lean_dec_ref(v_inner_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_transform(lean_object* v_s_445_, lean_object* v_a_446_){
_start:
{
uint8_t v___x_447_; 
v___x_447_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_a_446_);
if (v___x_447_ == 0)
{
lean_object* v_infoTree_x3f_448_; 
v_infoTree_x3f_448_ = lean_ctor_get(v_s_445_, 2);
if (lean_obj_tag(v_infoTree_x3f_448_) == 0)
{
return v_s_445_;
}
else
{
lean_object* v_desc_449_; lean_object* v_diagnostics_450_; lean_object* v_traces_451_; uint8_t v_isFatal_452_; lean_object* v_val_453_; lean_object* v___x_454_; 
v_desc_449_ = lean_ctor_get(v_s_445_, 0);
v_diagnostics_450_ = lean_ctor_get(v_s_445_, 1);
v_traces_451_ = lean_ctor_get(v_s_445_, 3);
v_isFatal_452_ = lean_ctor_get_uint8(v_s_445_, sizeof(void*)*4);
v_val_453_ = lean_ctor_get(v_infoTree_x3f_448_, 0);
lean_inc(v_val_453_);
lean_inc_ref(v_a_446_);
v___x_454_ = l_Lean_Elab_InfoTree_addTrailing_x3f(v_a_446_, v_val_453_);
if (lean_obj_tag(v___x_454_) == 0)
{
return v_s_445_;
}
else
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_inc_ref(v_traces_451_);
lean_inc_ref(v_diagnostics_450_);
lean_inc_ref(v_desc_449_);
v_isSharedCheck_461_ = !lean_is_exclusive(v_s_445_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; lean_object* v_unused_463_; lean_object* v_unused_464_; lean_object* v_unused_465_; 
v_unused_462_ = lean_ctor_get(v_s_445_, 3);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_s_445_, 2);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_s_445_, 1);
lean_dec(v_unused_464_);
v_unused_465_ = lean_ctor_get(v_s_445_, 0);
lean_dec(v_unused_465_);
v___x_456_ = v_s_445_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_dec(v_s_445_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 2, v___x_454_);
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_desc_449_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_diagnostics_450_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_460_, 3, v_traces_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_460_, sizeof(void*)*4, v_isFatal_452_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
else
{
return v_s_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_transform___boxed(lean_object* v_s_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Language_Snapshot_transform(v_s_466_, v_a_467_);
lean_dec_ref(v_a_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0___boxed(lean_object* v_a_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0(v_a_469_, v_x_470_);
lean_dec_ref(v_a_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(lean_object* v_a_472_, size_t v_sz_473_, size_t v_i_474_, lean_object* v_bs_475_){
_start:
{
uint8_t v___x_476_; 
v___x_476_ = lean_usize_dec_lt(v_i_474_, v_sz_473_);
if (v___x_476_ == 0)
{
return v_bs_475_;
}
else
{
lean_object* v_v_477_; lean_object* v_stx_x3f_478_; lean_object* v_reportingRange_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v_bs_x27_482_; lean_object* v___x_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; 
v_v_477_ = lean_array_uget(v_bs_475_, v_i_474_);
v_stx_x3f_478_ = lean_ctor_get(v_v_477_, 0);
lean_inc(v_stx_x3f_478_);
v_reportingRange_479_ = lean_ctor_get(v_v_477_, 1);
lean_inc(v_reportingRange_479_);
lean_inc_ref(v_a_472_);
v___f_480_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_480_, 0, v_a_472_);
v___x_481_ = lean_unsigned_to_nat(0u);
v_bs_x27_482_ = lean_array_uset(v_bs_475_, v_i_474_, v___x_481_);
v___x_483_ = l_Lean_Language_SnapshotTask_map___redArg(v_v_477_, v___f_480_, v_stx_x3f_478_, v_reportingRange_479_, v___x_476_);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_add(v_i_474_, v___x_484_);
v___x_486_ = lean_array_uset(v_bs_x27_482_, v_i_474_, v___x_483_);
v_i_474_ = v___x_485_;
v_bs_475_ = v___x_486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_transform(lean_object* v_t_488_, lean_object* v_a_489_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_a_489_);
if (v___x_490_ == 0)
{
lean_object* v_element_491_; lean_object* v_children_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_503_; 
v_element_491_ = lean_ctor_get(v_t_488_, 0);
v_children_492_ = lean_ctor_get(v_t_488_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_t_488_);
if (v_isSharedCheck_503_ == 0)
{
v___x_494_ = v_t_488_;
v_isShared_495_ = v_isSharedCheck_503_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_children_492_);
lean_inc(v_element_491_);
lean_dec(v_t_488_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_503_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; size_t v_sz_497_; size_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_496_ = l_Lean_Language_Snapshot_transform(v_element_491_, v_a_489_);
v_sz_497_ = lean_array_size(v_children_492_);
v___x_498_ = ((size_t)0ULL);
v___x_499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(v_a_489_, v_sz_497_, v___x_498_, v_children_492_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 1, v___x_499_);
lean_ctor_set(v___x_494_, 0, v___x_496_);
v___x_501_ = v___x_494_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
return v_t_488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0(lean_object* v_a_504_, lean_object* v_x_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Language_SnapshotTree_transform(v_x_505_, v_a_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object* v_t_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Language_SnapshotTree_transform(v_t_507_, v_a_508_);
lean_dec_ref(v_a_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___boxed(lean_object* v_a_510_, lean_object* v_sz_511_, lean_object* v_i_512_, lean_object* v_bs_513_){
_start:
{
size_t v_sz_boxed_514_; size_t v_i_boxed_515_; lean_object* v_res_516_; 
v_sz_boxed_514_ = lean_unbox_usize(v_sz_511_);
lean_dec(v_sz_511_);
v_i_boxed_515_ = lean_unbox_usize(v_i_512_);
lean_dec(v_i_512_);
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(v_a_510_, v_sz_boxed_514_, v_i_boxed_515_, v_bs_513_);
lean_dec_ref(v_a_510_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___redArg(lean_object* v_inst_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshotTreeTransform_default));
v___x_520_ = lean_apply_2(v_inst_517_, v_a_518_, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree(lean_object* v_00_u03b1_521_, lean_object* v_inst_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Language_toSnapshotTree___redArg(v_inst_522_, v_a_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedTransformedSnap___redArg(lean_object* v_inst_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshotTreeTransform_default));
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_inst_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedTransformedSnap(lean_object* v_00_u03b1_528_, lean_object* v_inst_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Language_instInhabitedTransformedSnap___redArg(v_inst_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0(lean_object* v_inst_531_, lean_object* v_s_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_raw_534_; lean_object* v_transform_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_raw_534_ = lean_ctor_get(v_s_532_, 0);
lean_inc(v_raw_534_);
v_transform_535_ = lean_ctor_get(v_s_532_, 1);
lean_inc_ref(v_transform_535_);
lean_dec_ref(v_s_532_);
lean_inc_ref(v___y_533_);
v___x_536_ = l_Lean_Language_SnapshotTreeTransform_compose(v___y_533_, v_transform_535_);
lean_dec_ref(v_transform_535_);
v___x_537_ = lean_apply_2(v_inst_531_, v_raw_534_, v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed(lean_object* v_inst_538_, lean_object* v_s_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0(v_inst_538_, v_s_539_, v___y_540_);
lean_dec_ref(v___y_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg(lean_object* v_inst_542_){
_start:
{
lean_object* v___f_543_; 
v___f_543_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_543_, 0, v_inst_542_);
return v___f_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap(lean_object* v_00_u03b1_544_, lean_object* v_inst_545_){
_start:
{
lean_object* v___f_546_; 
v___f_546_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_546_, 0, v_inst_545_);
return v___f_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_TransformedSnap_compose___redArg(lean_object* v_outer_547_, lean_object* v_s_548_){
_start:
{
lean_object* v_raw_549_; lean_object* v_transform_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_558_; 
v_raw_549_ = lean_ctor_get(v_s_548_, 0);
v_transform_550_ = lean_ctor_get(v_s_548_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_s_548_);
if (v_isSharedCheck_558_ == 0)
{
v___x_552_ = v_s_548_;
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_transform_550_);
lean_inc(v_raw_549_);
lean_dec(v_s_548_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = l_Lean_Language_SnapshotTreeTransform_compose(v_outer_547_, v_transform_550_);
lean_dec_ref(v_transform_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_raw_549_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_TransformedSnap_compose(lean_object* v_00_u03b1_559_, lean_object* v_outer_560_, lean_object* v_s_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Language_TransformedSnap_compose___redArg(v_outer_560_, v_s_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0(lean_object* v_f_563_, lean_object* v_a_564_, lean_object* v_x_565_){
_start:
{
lean_object* v___x_566_; 
lean_inc_ref(v_a_564_);
v___x_566_ = lean_apply_2(v_f_563_, v_x_565_, v_a_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0___boxed(lean_object* v_f_567_, lean_object* v_a_568_, lean_object* v_x_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0(v_f_567_, v_a_568_, v_x_569_);
lean_dec_ref(v_a_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object* v_t_571_, lean_object* v_f_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_stx_x3f_574_; lean_object* v_reportingRange_575_; lean_object* v___f_576_; uint8_t v___x_577_; lean_object* v___x_578_; 
v_stx_x3f_574_ = lean_ctor_get(v_t_571_, 0);
lean_inc(v_stx_x3f_574_);
v_reportingRange_575_ = lean_ctor_get(v_t_571_, 1);
lean_inc(v_reportingRange_575_);
lean_inc_ref(v_a_573_);
v___f_576_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_576_, 0, v_f_572_);
lean_closure_set(v___f_576_, 1, v_a_573_);
v___x_577_ = 1;
v___x_578_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_571_, v___f_576_, v_stx_x3f_574_, v_reportingRange_575_, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___boxed(lean_object* v_t_579_, lean_object* v_f_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_579_, v_f_580_, v_a_581_);
lean_dec_ref(v_a_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith(lean_object* v_00_u03b1_583_, lean_object* v_t_584_, lean_object* v_f_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_584_, v_f_585_, v_a_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___boxed(lean_object* v_00_u03b1_588_, lean_object* v_t_589_, lean_object* v_f_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Language_SnapshotTask_transformWith(v_00_u03b1_588_, v_t_589_, v_f_590_, v_a_591_);
lean_dec_ref(v_a_591_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___redArg(lean_object* v_inst_593_, lean_object* v_t_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_594_, v_inst_593_, v_a_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___redArg___boxed(lean_object* v_inst_597_, lean_object* v_t_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Language_SnapshotTask_transform___redArg(v_inst_597_, v_t_598_, v_a_599_);
lean_dec_ref(v_a_599_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform(lean_object* v_00_u03b1_601_, lean_object* v_inst_602_, lean_object* v_t_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_603_, v_inst_602_, v_a_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___boxed(lean_object* v_00_u03b1_606_, lean_object* v_inst_607_, lean_object* v_t_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Language_SnapshotTask_transform(v_00_u03b1_606_, v_inst_607_, v_t_608_, v_a_609_);
lean_dec_ref(v_a_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object* v_inst_613_, lean_object* v_x_614_, lean_object* v___y_615_){
_start:
{
if (lean_obj_tag(v_x_614_) == 0)
{
lean_object* v___x_616_; 
lean_dec_ref(v_inst_613_);
v___x_616_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_616_;
}
else
{
lean_object* v_val_617_; lean_object* v___x_618_; 
v_val_617_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v_x_614_, 1);
lean_inc_ref(v___y_615_);
v___x_618_ = lean_apply_2(v_inst_613_, v_val_617_, v___y_615_);
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed(lean_object* v_inst_619_, lean_object* v_x_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(v_inst_619_, v_x_620_, v___y_621_);
lean_dec_ref(v___y_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg(lean_object* v_inst_623_){
_start:
{
lean_object* v___f_624_; 
v___f_624_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_624_, 0, v_inst_623_);
return v___f_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object* v_00_u03b1_625_, lean_object* v_inst_626_){
_start:
{
lean_object* v___f_627_; 
v___f_627_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_627_, 0, v_inst_626_);
return v___f_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(lean_object* v_inst_628_, lean_object* v___x_629_, lean_object* v___f_630_, lean_object* v_snap_631_){
_start:
{
lean_object* v___x_633_; lean_object* v_children_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_633_ = l_Lean_Language_toSnapshotTree___redArg(v_inst_628_, v_snap_631_);
v_children_634_ = lean_ctor_get(v___x_633_, 1);
lean_inc_ref(v_children_634_);
lean_dec_ref(v___x_633_);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_array_get_size(v_children_634_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_nat_dec_lt(v___x_635_, v___x_636_);
if (v___x_638_ == 0)
{
lean_dec_ref(v_children_634_);
lean_dec_ref(v___f_630_);
lean_dec_ref(v___x_629_);
return v___x_637_;
}
else
{
uint8_t v___x_639_; 
v___x_639_ = lean_nat_dec_le(v___x_636_, v___x_636_);
if (v___x_639_ == 0)
{
if (v___x_638_ == 0)
{
lean_dec_ref(v_children_634_);
lean_dec_ref(v___f_630_);
lean_dec_ref(v___x_629_);
return v___x_637_;
}
else
{
size_t v___x_640_; size_t v___x_641_; lean_object* v___x_205__overap_642_; lean_object* v___x_643_; 
v___x_640_ = ((size_t)0ULL);
v___x_641_ = lean_usize_of_nat(v___x_636_);
v___x_205__overap_642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_629_, v___f_630_, v_children_634_, v___x_640_, v___x_641_, v___x_637_);
v___x_643_ = lean_apply_1(v___x_205__overap_642_, lean_box(0));
return v___x_643_;
}
}
else
{
size_t v___x_644_; size_t v___x_645_; lean_object* v___x_208__overap_646_; lean_object* v___x_647_; 
v___x_644_ = ((size_t)0ULL);
v___x_645_ = lean_usize_of_nat(v___x_636_);
v___x_208__overap_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_629_, v___f_630_, v_children_634_, v___x_644_, v___x_645_, v___x_637_);
v___x_647_ = lean_apply_1(v___x_208__overap_646_, lean_box(0));
return v___x_647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed(lean_object* v_inst_648_, lean_object* v___x_649_, lean_object* v___f_650_, lean_object* v_snap_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(v_inst_648_, v___x_649_, v___f_650_, v_snap_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(lean_object* v___f_654_, lean_object* v_x_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(v___f_654_, v_x_655_, v___y_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object* v_inst_659_, lean_object* v_t_660_){
_start:
{
lean_object* v___x_662_; lean_object* v_cancelTk_x3f_663_; lean_object* v_task_664_; lean_object* v___f_665_; lean_object* v___f_666_; lean_object* v___f_667_; 
v___x_662_ = l_instMonadBaseIO;
v_cancelTk_x3f_663_ = lean_ctor_get(v_t_660_, 2);
lean_inc(v_cancelTk_x3f_663_);
v_task_664_ = lean_ctor_get(v_t_660_, 3);
lean_inc_ref(v_task_664_);
lean_dec_ref(v_t_660_);
v___f_665_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0));
v___f_666_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_666_, 0, v___f_665_);
v___f_667_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_667_, 0, v_inst_659_);
lean_closure_set(v___f_667_, 1, v___x_662_);
lean_closure_set(v___f_667_, 2, v___f_666_);
if (lean_obj_tag(v_cancelTk_x3f_663_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_673_; 
v_val_672_ = lean_ctor_get(v_cancelTk_x3f_663_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v_cancelTk_x3f_663_, 1);
v___x_673_ = l_IO_CancelToken_set(v_val_672_);
lean_dec(v_val_672_);
goto v___jp_668_;
}
else
{
lean_dec(v_cancelTk_x3f_663_);
goto v___jp_668_;
}
v___jp_668_:
{
lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = 1;
v___x_671_ = l_BaseIO_chainTask___redArg(v_task_664_, v___f_667_, v___x_669_, v___x_670_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object* v___f_674_, lean_object* v_x_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_674_, v___y_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___boxed(lean_object* v_inst_679_, lean_object* v_t_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_679_, v_t_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object* v_00_u03b1_683_, lean_object* v_inst_684_, lean_object* v_t_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_684_, v_t_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___boxed(lean_object* v_00_u03b1_688_, lean_object* v_inst_689_, lean_object* v_t_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Language_SnapshotTask_cancelRec(v_00_u03b1_688_, v_inst_689_, v_t_690_);
return v_res_692_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotLeaf(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_unsigned_to_nat(32u);
v___x_701_ = lean_mk_empty_array_with_capacity(v___x_700_);
lean_dec_ref(v___x_701_);
v___x_702_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object* v_s_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = l_Lean_Language_Snapshot_transform(v_s_705_, v___y_706_);
v___x_708_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0));
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___boxed(lean_object* v_s_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(v_s_710_, v___y_711_);
lean_dec_ref(v___y_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object* v_s_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_toSnapshotTreeM_717_; lean_object* v___x_718_; 
v_toSnapshotTreeM_717_ = lean_ctor_get(v_s_715_, 1);
lean_inc_ref(v_toSnapshotTreeM_717_);
lean_dec_ref(v_s_715_);
lean_inc_ref(v___y_716_);
v___x_718_ = lean_apply_1(v_toSnapshotTreeM_717_, v___y_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object* v_s_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(v_s_719_, v___y_720_);
lean_dec_ref(v___y_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_val_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_inc(v_val_726_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v_inst_724_);
lean_ctor_set(v___x_727_, 1, v_val_726_);
v___x_728_ = lean_apply_1(v_inst_725_, v_val_726_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object* v_00_u03b1_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_val_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v_inst_731_, v_inst_732_, v_val_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object* v_inst_735_, lean_object* v_snap_736_){
_start:
{
lean_object* v_val_737_; lean_object* v___x_738_; 
v_val_737_ = lean_ctor_get(v_snap_736_, 0);
v___x_738_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_737_, v_inst_735_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object* v_inst_739_, lean_object* v_snap_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_739_, v_snap_740_);
lean_dec_ref(v_snap_740_);
lean_dec(v_inst_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object* v_00_u03b1_742_, lean_object* v_inst_743_, lean_object* v_snap_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_743_, v_snap_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object* v_00_u03b1_746_, lean_object* v_inst_747_, lean_object* v_snap_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f(v_00_u03b1_746_, v_inst_747_, v_snap_748_);
lean_dec_ref(v_snap_748_);
lean_dec(v_inst_747_);
return v_res_749_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2(void){
_start:
{
uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = 1;
v___x_756_ = ((lean_object*)(l_Lean_Language_instInhabitedDynamicSnapshot___closed__1));
v___x_757_ = l_Lean_Name_toString(v___x_756_, v___x_755_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3(void){
_start:
{
uint8_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_758_ = 0;
v___x_759_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_760_ = lean_box(0);
v___x_761_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_762_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__2, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__2_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2);
v___x_763_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___x_761_);
lean_ctor_set(v___x_763_, 2, v___x_760_);
lean_ctor_set(v___x_763_, 3, v___x_759_);
lean_ctor_set_uint8(v___x_763_, sizeof(void*)*4, v___x_758_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4(void){
_start:
{
lean_object* v___x_764_; lean_object* v___f_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_764_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__3, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3);
v___f_765_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0));
v___x_766_ = ((lean_object*)(l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_));
v___x_767_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v___x_766_, v___f_765_, v___x_764_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot(void){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__4, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object* v_toApplicative_769_, lean_object* v_children_770_, lean_object* v_inst_771_, lean_object* v___f_772_, lean_object* v_____r_773_){
_start:
{
lean_object* v_toPure_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_toPure_774_ = lean_ctor_get(v_toApplicative_769_, 1);
lean_inc(v_toPure_774_);
lean_dec_ref(v_toApplicative_769_);
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_array_get_size(v_children_770_);
v___x_777_ = lean_box(0);
v___x_778_ = lean_nat_dec_lt(v___x_775_, v___x_776_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec(v___f_772_);
lean_dec_ref(v_inst_771_);
lean_dec_ref(v_children_770_);
v___x_779_ = lean_apply_2(v_toPure_774_, lean_box(0), v___x_777_);
return v___x_779_;
}
else
{
uint8_t v___x_780_; 
v___x_780_ = lean_nat_dec_le(v___x_776_, v___x_776_);
if (v___x_780_ == 0)
{
if (v___x_778_ == 0)
{
lean_object* v___x_781_; 
lean_dec(v___f_772_);
lean_dec_ref(v_inst_771_);
lean_dec_ref(v_children_770_);
v___x_781_ = lean_apply_2(v_toPure_774_, lean_box(0), v___x_777_);
return v___x_781_;
}
else
{
size_t v___x_782_; size_t v___x_783_; lean_object* v___x_784_; 
lean_dec(v_toPure_774_);
v___x_782_ = ((size_t)0ULL);
v___x_783_ = lean_usize_of_nat(v___x_776_);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_771_, v___f_772_, v_children_770_, v___x_782_, v___x_783_, v___x_777_);
return v___x_784_;
}
}
else
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
lean_dec(v_toPure_774_);
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_of_nat(v___x_776_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_771_, v___f_772_, v_children_770_, v___x_785_, v___x_786_, v___x_777_);
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object* v_inst_788_, lean_object* v_s_789_, lean_object* v_f_790_){
_start:
{
lean_object* v_toApplicative_791_; lean_object* v_toBind_792_; lean_object* v_element_793_; lean_object* v_children_794_; lean_object* v___f_795_; lean_object* v___f_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_toApplicative_791_ = lean_ctor_get(v_inst_788_, 0);
lean_inc_ref(v_toApplicative_791_);
v_toBind_792_ = lean_ctor_get(v_inst_788_, 1);
lean_inc(v_toBind_792_);
v_element_793_ = lean_ctor_get(v_s_789_, 0);
lean_inc_ref(v_element_793_);
v_children_794_ = lean_ctor_get(v_s_789_, 1);
lean_inc_ref(v_children_794_);
lean_dec_ref(v_s_789_);
lean_inc(v_f_790_);
lean_inc_ref(v_inst_788_);
v___f_795_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_795_, 0, v_inst_788_);
lean_closure_set(v___f_795_, 1, v_f_790_);
v___f_796_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_796_, 0, v_toApplicative_791_);
lean_closure_set(v___f_796_, 1, v_children_794_);
lean_closure_set(v___f_796_, 2, v_inst_788_);
lean_closure_set(v___f_796_, 3, v___f_795_);
v___x_797_ = lean_apply_1(v_f_790_, v_element_793_);
v___x_798_ = lean_apply_4(v_toBind_792_, lean_box(0), lean_box(0), v___x_797_, v___f_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object* v_inst_799_, lean_object* v_f_800_, lean_object* v_x_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = l_Lean_Language_SnapshotTask_get___redArg(v___y_802_);
v___x_804_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_799_, v___x_803_, v_f_800_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object* v_m_805_, lean_object* v_inst_806_, lean_object* v_s_807_, lean_object* v_f_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_806_, v_s_807_, v_f_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object* v_toApplicative_810_, lean_object* v_children_811_, lean_object* v_inst_812_, lean_object* v___f_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_toPure_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_toPure_815_ = lean_ctor_get(v_toApplicative_810_, 1);
lean_inc(v_toPure_815_);
lean_dec_ref(v_toApplicative_810_);
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = lean_array_get_size(v_children_811_);
v___x_818_ = lean_nat_dec_lt(v___x_816_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
lean_dec(v___f_813_);
lean_dec_ref(v_inst_812_);
lean_dec_ref(v_children_811_);
v___x_819_ = lean_apply_2(v_toPure_815_, lean_box(0), v_a_814_);
return v___x_819_;
}
else
{
uint8_t v___x_820_; 
v___x_820_ = lean_nat_dec_le(v___x_817_, v___x_817_);
if (v___x_820_ == 0)
{
if (v___x_818_ == 0)
{
lean_object* v___x_821_; 
lean_dec(v___f_813_);
lean_dec_ref(v_inst_812_);
lean_dec_ref(v_children_811_);
v___x_821_ = lean_apply_2(v_toPure_815_, lean_box(0), v_a_814_);
return v___x_821_;
}
else
{
size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
lean_dec(v_toPure_815_);
v___x_822_ = ((size_t)0ULL);
v___x_823_ = lean_usize_of_nat(v___x_817_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_812_, v___f_813_, v_children_811_, v___x_822_, v___x_823_, v_a_814_);
return v___x_824_;
}
}
else
{
size_t v___x_825_; size_t v___x_826_; lean_object* v___x_827_; 
lean_dec(v_toPure_815_);
v___x_825_ = ((size_t)0ULL);
v___x_826_ = lean_usize_of_nat(v___x_817_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_812_, v___f_813_, v_children_811_, v___x_825_, v___x_826_, v_a_814_);
return v___x_827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object* v_inst_828_, lean_object* v_s_829_, lean_object* v_f_830_, lean_object* v_init_831_){
_start:
{
lean_object* v_toApplicative_832_; lean_object* v_toBind_833_; lean_object* v_element_834_; lean_object* v_children_835_; lean_object* v___f_836_; lean_object* v___f_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_toApplicative_832_ = lean_ctor_get(v_inst_828_, 0);
lean_inc_ref(v_toApplicative_832_);
v_toBind_833_ = lean_ctor_get(v_inst_828_, 1);
lean_inc(v_toBind_833_);
v_element_834_ = lean_ctor_get(v_s_829_, 0);
lean_inc_ref(v_element_834_);
v_children_835_ = lean_ctor_get(v_s_829_, 1);
lean_inc_ref(v_children_835_);
lean_dec_ref(v_s_829_);
lean_inc(v_f_830_);
lean_inc_ref(v_inst_828_);
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_836_, 0, v_inst_828_);
lean_closure_set(v___f_836_, 1, v_f_830_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_837_, 0, v_toApplicative_832_);
lean_closure_set(v___f_837_, 1, v_children_835_);
lean_closure_set(v___f_837_, 2, v_inst_828_);
lean_closure_set(v___f_837_, 3, v___f_836_);
v___x_838_ = lean_apply_2(v_f_830_, v_init_831_, v_element_834_);
v___x_839_ = lean_apply_4(v_toBind_833_, lean_box(0), lean_box(0), v___x_838_, v___f_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object* v_inst_840_, lean_object* v_f_841_, lean_object* v_a_842_, lean_object* v_snap_843_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = l_Lean_Language_SnapshotTask_get___redArg(v_snap_843_);
v___x_845_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_840_, v___x_844_, v_f_841_, v_a_842_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object* v_m_846_, lean_object* v_00_u03b1_847_, lean_object* v_inst_848_, lean_object* v_s_849_, lean_object* v_f_850_, lean_object* v_init_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_848_, v_s_849_, v_f_850_, v_init_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(lean_object* v_name_853_, lean_object* v_decl_854_, lean_object* v_ref_855_){
_start:
{
lean_object* v_defValue_857_; lean_object* v_descr_858_; lean_object* v_deprecation_x3f_859_; lean_object* v___x_860_; uint8_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_defValue_857_ = lean_ctor_get(v_decl_854_, 0);
v_descr_858_ = lean_ctor_get(v_decl_854_, 1);
v_deprecation_x3f_859_ = lean_ctor_get(v_decl_854_, 2);
v___x_860_ = lean_alloc_ctor(1, 0, 1);
v___x_861_ = lean_unbox(v_defValue_857_);
lean_ctor_set_uint8(v___x_860_, 0, v___x_861_);
lean_inc(v_deprecation_x3f_859_);
lean_inc_ref(v_descr_858_);
lean_inc_n(v_name_853_, 2);
v___x_862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_862_, 0, v_name_853_);
lean_ctor_set(v___x_862_, 1, v_ref_855_);
lean_ctor_set(v___x_862_, 2, v___x_860_);
lean_ctor_set(v___x_862_, 3, v_descr_858_);
lean_ctor_set(v___x_862_, 4, v_deprecation_x3f_859_);
v___x_863_ = lean_register_option(v_name_853_, v___x_862_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_863_, 0);
lean_dec(v_unused_872_);
v___x_865_ = v___x_863_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_dec(v___x_863_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_869_; 
lean_inc(v_defValue_857_);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v_name_853_);
lean_ctor_set(v___x_867_, 1, v_defValue_857_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_867_);
v___x_869_ = v___x_865_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_name_853_);
v_a_873_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_863_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_863_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_881_, lean_object* v_decl_882_, lean_object* v_ref_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v_name_881_, v_decl_882_, v_ref_883_);
lean_dec_ref(v_decl_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_900_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_901_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_902_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_903_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v___x_900_, v___x_901_, v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4____boxed(lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(lean_object* v_name_906_, lean_object* v_decl_907_, lean_object* v_ref_908_){
_start:
{
lean_object* v_defValue_910_; lean_object* v_descr_911_; lean_object* v_deprecation_x3f_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_defValue_910_ = lean_ctor_get(v_decl_907_, 0);
v_descr_911_ = lean_ctor_get(v_decl_907_, 1);
v_deprecation_x3f_912_ = lean_ctor_get(v_decl_907_, 2);
lean_inc(v_defValue_910_);
v___x_913_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_913_, 0, v_defValue_910_);
lean_inc(v_deprecation_x3f_912_);
lean_inc_ref(v_descr_911_);
lean_inc_n(v_name_906_, 2);
v___x_914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_914_, 0, v_name_906_);
lean_ctor_set(v___x_914_, 1, v_ref_908_);
lean_ctor_set(v___x_914_, 2, v___x_913_);
lean_ctor_set(v___x_914_, 3, v_descr_911_);
lean_ctor_set(v___x_914_, 4, v_deprecation_x3f_912_);
v___x_915_ = lean_register_option(v_name_906_, v___x_914_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_923_; 
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v___x_915_, 0);
lean_dec(v_unused_924_);
v___x_917_ = v___x_915_;
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
else
{
lean_dec(v___x_915_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
lean_inc(v_defValue_910_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_name_906_);
lean_ctor_set(v___x_919_, 1, v_defValue_910_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_name_906_);
v_a_925_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_915_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_915_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_933_, lean_object* v_decl_934_, lean_object* v_ref_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v_name_933_, v_decl_934_, v_ref_935_);
lean_dec_ref(v_decl_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_951_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_952_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_953_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_954_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v___x_951_, v___x_952_, v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4____boxed(lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
return v_res_956_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(lean_object* v_opts_957_, lean_object* v_opt_958_){
_start:
{
lean_object* v_name_959_; lean_object* v_defValue_960_; lean_object* v_map_961_; lean_object* v___x_962_; 
v_name_959_ = lean_ctor_get(v_opt_958_, 0);
v_defValue_960_ = lean_ctor_get(v_opt_958_, 1);
v_map_961_ = lean_ctor_get(v_opts_957_, 0);
v___x_962_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_961_, v_name_959_);
if (lean_obj_tag(v___x_962_) == 0)
{
uint8_t v___x_963_; 
v___x_963_ = lean_unbox(v_defValue_960_);
return v___x_963_;
}
else
{
lean_object* v_val_964_; 
v_val_964_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_val_964_);
lean_dec_ref_known(v___x_962_, 1);
if (lean_obj_tag(v_val_964_) == 1)
{
uint8_t v_v_965_; 
v_v_965_ = lean_ctor_get_uint8(v_val_964_, 0);
lean_dec_ref_known(v_val_964_, 0);
return v_v_965_;
}
else
{
uint8_t v___x_966_; 
lean_dec(v_val_964_);
v___x_966_ = lean_unbox(v_defValue_960_);
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0___boxed(lean_object* v_opts_967_, lean_object* v_opt_968_){
_start:
{
uint8_t v_res_969_; lean_object* v_r_970_; 
v_res_969_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_967_, v_opt_968_);
lean_dec_ref(v_opt_968_);
lean_dec_ref(v_opts_967_);
v_r_970_ = lean_box(v_res_969_);
return v_r_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(lean_object* v_opts_971_, lean_object* v_opt_972_){
_start:
{
lean_object* v_name_973_; lean_object* v_defValue_974_; lean_object* v_map_975_; lean_object* v___x_976_; 
v_name_973_ = lean_ctor_get(v_opt_972_, 0);
v_defValue_974_ = lean_ctor_get(v_opt_972_, 1);
v_map_975_ = lean_ctor_get(v_opts_971_, 0);
v___x_976_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_975_, v_name_973_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_inc(v_defValue_974_);
return v_defValue_974_;
}
else
{
lean_object* v_val_977_; 
v_val_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v___x_976_, 1);
if (lean_obj_tag(v_val_977_) == 3)
{
lean_object* v_v_978_; 
v_v_978_ = lean_ctor_get(v_val_977_, 0);
lean_inc(v_v_978_);
lean_dec_ref_known(v_val_977_, 1);
return v_v_978_;
}
else
{
lean_dec(v_val_977_);
lean_inc(v_defValue_974_);
return v_defValue_974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1___boxed(lean_object* v_opts_979_, lean_object* v_opt_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_979_, v_opt_980_);
lean_dec_ref(v_opt_980_);
lean_dec_ref(v_opts_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(lean_object* v_s_982_){
_start:
{
lean_object* v___x_984_; lean_object* v_putStr_985_; lean_object* v___x_986_; 
v___x_984_ = lean_get_stdout();
v_putStr_985_ = lean_ctor_get(v___x_984_, 4);
lean_inc_ref(v_putStr_985_);
lean_dec_ref(v___x_984_);
v___x_986_ = lean_apply_2(v_putStr_985_, v_s_982_, lean_box(0));
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2___boxed(lean_object* v_s_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v_s_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object* v_s_990_){
_start:
{
uint32_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = 10;
v___x_993_ = lean_string_push(v_s_990_, v___x_992_);
v___x_994_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3___boxed(lean_object* v_s_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v_s_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(lean_object* v_opts_1000_, uint8_t v_json_1001_, uint8_t v_includeEndPos_1002_, lean_object* v_severityOverrides_1003_, lean_object* v_as_1004_, size_t v_i_1005_, size_t v_stop_1006_, lean_object* v_b_1007_){
_start:
{
lean_object* v_a_1010_; uint8_t v___y_1015_; lean_object* v___y_1016_; uint8_t v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; uint8_t v_isSilent_1031_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; uint8_t v___y_1057_; uint8_t v___x_1081_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1092_; uint8_t v_severity_1093_; 
v___x_1081_ = lean_usize_dec_eq(v_i_1005_, v_stop_1006_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1096_; lean_object* v_fileName_1097_; lean_object* v_pos_1098_; lean_object* v_endPos_1099_; uint8_t v_keepFullRange_1100_; uint8_t v_isSilent_1101_; lean_object* v_caption_1102_; lean_object* v_data_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1096_ = lean_array_uget(v_as_1004_, v_i_1005_);
v_fileName_1097_ = lean_ctor_get(v___x_1096_, 0);
v_pos_1098_ = lean_ctor_get(v___x_1096_, 1);
v_endPos_1099_ = lean_ctor_get(v___x_1096_, 2);
v_keepFullRange_1100_ = lean_ctor_get_uint8(v___x_1096_, sizeof(void*)*5);
v_isSilent_1101_ = lean_ctor_get_uint8(v___x_1096_, sizeof(void*)*5 + 2);
v_caption_1102_ = lean_ctor_get(v___x_1096_, 3);
v_data_1103_ = lean_ctor_get(v___x_1096_, 4);
v___x_1104_ = l_Lean_MessageData_kind(v_data_1103_);
v___x_1105_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_severityOverrides_1003_, v___x_1104_);
lean_dec(v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 1)
{
lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1115_; 
lean_inc(v_data_1103_);
lean_inc_ref(v_caption_1102_);
lean_inc(v_endPos_1099_);
lean_inc_ref(v_pos_1098_);
lean_inc_ref(v_fileName_1097_);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; lean_object* v_unused_1119_; lean_object* v_unused_1120_; 
v_unused_1116_ = lean_ctor_get(v___x_1096_, 4);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v___x_1096_, 3);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v___x_1096_, 2);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v___x_1096_, 1);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v___x_1096_, 0);
lean_dec(v_unused_1120_);
v___x_1107_ = v___x_1096_;
v_isShared_1108_ = v_isSharedCheck_1115_;
goto v_resetjp_1106_;
}
else
{
lean_dec(v___x_1096_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1115_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v_val_1109_; lean_object* v___x_1111_; 
v_val_1109_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_val_1109_);
lean_dec_ref_known(v___x_1105_, 1);
if (v_isShared_1108_ == 0)
{
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_fileName_1097_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_pos_1098_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_endPos_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_caption_1102_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_data_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1114_, sizeof(void*)*5, v_keepFullRange_1100_);
v___x_1111_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
uint8_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = lean_unbox(v_val_1109_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*5 + 1, v___x_1112_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*5 + 2, v_isSilent_1101_);
v___x_1113_ = lean_unbox(v_val_1109_);
lean_dec(v_val_1109_);
v___y_1092_ = v___x_1111_;
v_severity_1093_ = v___x_1113_;
goto v___jp_1091_;
}
}
}
else
{
uint8_t v_severity_1121_; 
lean_dec(v___x_1105_);
v_severity_1121_ = lean_ctor_get_uint8(v___x_1096_, sizeof(void*)*5 + 1);
v___y_1092_ = v___x_1096_;
v_severity_1093_ = v_severity_1121_;
goto v___jp_1091_;
}
}
else
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v_b_1007_);
return v___x_1122_;
}
v___jp_1009_:
{
size_t v___x_1011_; size_t v___x_1012_; 
v___x_1011_ = ((size_t)1ULL);
v___x_1012_ = lean_usize_add(v_i_1005_, v___x_1011_);
v_i_1005_ = v___x_1012_;
v_b_1007_ = v_a_1010_;
goto _start;
}
v___jp_1014_:
{
if (v___y_1015_ == 0)
{
v_a_1010_ = v___y_1016_;
goto v___jp_1009_;
}
else
{
uint8_t v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = 1;
v___x_1018_ = lean_io_exit(v___x_1017_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_dec_ref_known(v___x_1018_, 1);
v_a_1010_ = v___y_1016_;
goto v___jp_1009_;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v___y_1016_);
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
v___jp_1027_:
{
if (v_isSilent_1031_ == 0)
{
if (v_json_1001_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = l_Lean_Message_toString(v___y_1030_, v_includeEndPos_1002_);
v___x_1033_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_1032_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_dec_ref_known(v___x_1033_, 1);
v___y_1015_ = v___y_1028_;
v___y_1016_ = v___y_1029_;
goto v___jp_1014_;
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v___y_1029_);
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = l_Lean_Message_toJson(v___y_1030_);
v___x_1043_ = l_Lean_Json_compress(v___x_1042_);
v___x_1044_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_1043_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_dec_ref_known(v___x_1044_, 1);
v___y_1015_ = v___y_1028_;
v___y_1016_ = v___y_1029_;
goto v___jp_1014_;
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v___y_1029_);
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1030_);
v___y_1015_ = v___y_1028_;
v___y_1016_ = v___y_1029_;
goto v___jp_1014_;
}
}
v___jp_1053_:
{
if (v___y_1057_ == 0)
{
uint8_t v_isSilent_1058_; 
lean_dec(v___y_1054_);
v_isSilent_1058_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*5 + 2);
v___y_1028_ = v___y_1057_;
v___y_1029_ = v___y_1056_;
v___y_1030_ = v___y_1055_;
v_isSilent_1031_ = v_isSilent_1058_;
goto v___jp_1027_;
}
else
{
lean_object* v_fileName_1059_; lean_object* v_pos_1060_; lean_object* v_endPos_1061_; uint8_t v_keepFullRange_1062_; uint8_t v_isSilent_1063_; lean_object* v_caption_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1079_; 
v_fileName_1059_ = lean_ctor_get(v___y_1055_, 0);
v_pos_1060_ = lean_ctor_get(v___y_1055_, 1);
v_endPos_1061_ = lean_ctor_get(v___y_1055_, 2);
v_keepFullRange_1062_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*5);
v_isSilent_1063_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*5 + 2);
v_caption_1064_ = lean_ctor_get(v___y_1055_, 3);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___y_1055_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v___y_1055_, 4);
lean_dec(v_unused_1080_);
v___x_1066_ = v___y_1055_;
v_isShared_1067_ = v_isSharedCheck_1079_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_caption_1064_);
lean_inc(v_endPos_1061_);
lean_inc(v_pos_1060_);
lean_inc(v_fileName_1059_);
lean_dec(v___y_1055_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1079_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1068_ = 2;
v___x_1069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0));
v___x_1070_ = l_Nat_reprFast(v___y_1054_);
v___x_1071_ = lean_string_append(v___x_1069_, v___x_1070_);
lean_dec_ref(v___x_1070_);
v___x_1072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1));
v___x_1073_ = lean_string_append(v___x_1071_, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
v___x_1075_ = l_Lean_MessageData_ofFormat(v___x_1074_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 4, v___x_1075_);
v___x_1077_ = v___x_1066_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_fileName_1059_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_pos_1060_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_endPos_1061_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_caption_1064_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v___x_1075_);
lean_ctor_set_uint8(v_reuseFailAlloc_1078_, sizeof(void*)*5, v_keepFullRange_1062_);
lean_ctor_set_uint8(v_reuseFailAlloc_1078_, sizeof(void*)*5 + 2, v_isSilent_1063_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*5 + 1, v___x_1068_);
v___y_1028_ = v___y_1057_;
v___y_1029_ = v___y_1056_;
v___y_1030_ = v___x_1077_;
v_isSilent_1031_ = v_isSilent_1063_;
goto v___jp_1027_;
}
}
}
}
v___jp_1082_:
{
lean_object* v_numErrors_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_numErrors_1085_ = lean_nat_add(v_b_1007_, v___y_1084_);
lean_dec(v_b_1007_);
v___x_1086_ = l_Lean_Language_maxErrors;
v___x_1087_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_1000_, v___x_1086_);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = lean_nat_dec_eq(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; 
v___x_1090_ = lean_nat_dec_lt(v___x_1087_, v_numErrors_1085_);
v___y_1054_ = v___x_1087_;
v___y_1055_ = v___y_1083_;
v___y_1056_ = v_numErrors_1085_;
v___y_1057_ = v___x_1090_;
goto v___jp_1053_;
}
else
{
v___y_1054_ = v___x_1087_;
v___y_1055_ = v___y_1083_;
v___y_1056_ = v_numErrors_1085_;
v___y_1057_ = v___x_1081_;
goto v___jp_1053_;
}
}
v___jp_1091_:
{
if (v_severity_1093_ == 2)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_unsigned_to_nat(1u);
v___y_1083_ = v___y_1092_;
v___y_1084_ = v___x_1094_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_unsigned_to_nat(0u);
v___y_1083_ = v___y_1092_;
v___y_1084_ = v___x_1095_;
goto v___jp_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___boxed(lean_object* v_opts_1123_, lean_object* v_json_1124_, lean_object* v_includeEndPos_1125_, lean_object* v_severityOverrides_1126_, lean_object* v_as_1127_, lean_object* v_i_1128_, lean_object* v_stop_1129_, lean_object* v_b_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v_json_boxed_1132_; uint8_t v_includeEndPos_boxed_1133_; size_t v_i_boxed_1134_; size_t v_stop_boxed_1135_; lean_object* v_res_1136_; 
v_json_boxed_1132_ = lean_unbox(v_json_1124_);
v_includeEndPos_boxed_1133_ = lean_unbox(v_includeEndPos_1125_);
v_i_boxed_1134_ = lean_unbox_usize(v_i_1128_);
lean_dec(v_i_1128_);
v_stop_boxed_1135_ = lean_unbox_usize(v_stop_1129_);
lean_dec(v_stop_1129_);
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1123_, v_json_boxed_1132_, v_includeEndPos_boxed_1133_, v_severityOverrides_1126_, v_as_1127_, v_i_boxed_1134_, v_stop_boxed_1135_, v_b_1130_);
lean_dec_ref(v_as_1127_);
lean_dec(v_severityOverrides_1126_);
lean_dec_ref(v_opts_1123_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(lean_object* v_opts_1137_, uint8_t v_json_1138_, uint8_t v_includeEndPos_1139_, lean_object* v_severityOverrides_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_){
_start:
{
if (lean_obj_tag(v_x_1141_) == 0)
{
lean_object* v_cs_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1157_; 
v_cs_1144_ = lean_ctor_get(v_x_1141_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_x_1141_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1146_ = v_x_1141_;
v_isShared_1147_ = v_isSharedCheck_1157_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_cs_1144_);
lean_dec(v_x_1141_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1157_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_array_get_size(v_cs_1144_);
v___x_1150_ = lean_nat_dec_lt(v___x_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1152_; 
lean_dec_ref(v_cs_1144_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v_x_1142_);
v___x_1152_ = v___x_1146_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_x_1142_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
size_t v___x_1154_; size_t v___x_1155_; lean_object* v___x_1156_; 
lean_del_object(v___x_1146_);
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = lean_usize_of_nat(v___x_1149_);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1137_, v_json_1138_, v_includeEndPos_1139_, v_severityOverrides_1140_, v_cs_1144_, v___x_1154_, v___x_1155_, v_x_1142_);
lean_dec_ref(v_cs_1144_);
return v___x_1156_;
}
}
}
else
{
lean_object* v_vs_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1171_; 
v_vs_1158_ = lean_ctor_get(v_x_1141_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_x_1141_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1160_ = v_x_1141_;
v_isShared_1161_ = v_isSharedCheck_1171_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_vs_1158_);
lean_dec(v_x_1141_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1171_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = lean_array_get_size(v_vs_1158_);
v___x_1164_ = lean_nat_dec_lt(v___x_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1166_; 
lean_dec_ref(v_vs_1158_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 0);
lean_ctor_set(v___x_1160_, 0, v_x_1142_);
v___x_1166_ = v___x_1160_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_x_1142_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
else
{
size_t v___x_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
lean_del_object(v___x_1160_);
v___x_1168_ = ((size_t)0ULL);
v___x_1169_ = lean_usize_of_nat(v___x_1163_);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1137_, v_json_1138_, v_includeEndPos_1139_, v_severityOverrides_1140_, v_vs_1158_, v___x_1168_, v___x_1169_, v_x_1142_);
lean_dec_ref(v_vs_1158_);
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(lean_object* v_opts_1172_, uint8_t v_json_1173_, uint8_t v_includeEndPos_1174_, lean_object* v_severityOverrides_1175_, lean_object* v_as_1176_, size_t v_i_1177_, size_t v_stop_1178_, lean_object* v_b_1179_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_usize_dec_eq(v_i_1177_, v_stop_1178_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_array_uget_borrowed(v_as_1176_, v_i_1177_);
lean_inc(v___x_1182_);
v___x_1183_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1172_, v_json_1173_, v_includeEndPos_1174_, v_severityOverrides_1175_, v___x_1182_, v_b_1179_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; size_t v___x_1185_; size_t v___x_1186_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = ((size_t)1ULL);
v___x_1186_ = lean_usize_add(v_i_1177_, v___x_1185_);
v_i_1177_ = v___x_1186_;
v_b_1179_ = v_a_1184_;
goto _start;
}
else
{
return v___x_1183_;
}
}
else
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v_b_1179_);
return v___x_1188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5___boxed(lean_object* v_opts_1189_, lean_object* v_json_1190_, lean_object* v_includeEndPos_1191_, lean_object* v_severityOverrides_1192_, lean_object* v_as_1193_, lean_object* v_i_1194_, lean_object* v_stop_1195_, lean_object* v_b_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v_json_boxed_1198_; uint8_t v_includeEndPos_boxed_1199_; size_t v_i_boxed_1200_; size_t v_stop_boxed_1201_; lean_object* v_res_1202_; 
v_json_boxed_1198_ = lean_unbox(v_json_1190_);
v_includeEndPos_boxed_1199_ = lean_unbox(v_includeEndPos_1191_);
v_i_boxed_1200_ = lean_unbox_usize(v_i_1194_);
lean_dec(v_i_1194_);
v_stop_boxed_1201_ = lean_unbox_usize(v_stop_1195_);
lean_dec(v_stop_1195_);
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1189_, v_json_boxed_1198_, v_includeEndPos_boxed_1199_, v_severityOverrides_1192_, v_as_1193_, v_i_boxed_1200_, v_stop_boxed_1201_, v_b_1196_);
lean_dec_ref(v_as_1193_);
lean_dec(v_severityOverrides_1192_);
lean_dec_ref(v_opts_1189_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6___boxed(lean_object* v_opts_1203_, lean_object* v_json_1204_, lean_object* v_includeEndPos_1205_, lean_object* v_severityOverrides_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_, lean_object* v___y_1209_){
_start:
{
uint8_t v_json_boxed_1210_; uint8_t v_includeEndPos_boxed_1211_; lean_object* v_res_1212_; 
v_json_boxed_1210_ = lean_unbox(v_json_1204_);
v_includeEndPos_boxed_1211_ = lean_unbox(v_includeEndPos_1205_);
v_res_1212_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1203_, v_json_boxed_1210_, v_includeEndPos_boxed_1211_, v_severityOverrides_1206_, v_x_1207_, v_x_1208_);
lean_dec(v_severityOverrides_1206_);
lean_dec_ref(v_opts_1203_);
return v_res_1212_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(lean_object* v_opts_1214_, uint8_t v_json_1215_, uint8_t v_includeEndPos_1216_, lean_object* v_severityOverrides_1217_, lean_object* v_x_1218_, size_t v_x_1219_, size_t v_x_1220_, lean_object* v_x_1221_){
_start:
{
if (lean_obj_tag(v_x_1218_) == 0)
{
lean_object* v_cs_1223_; lean_object* v___x_1224_; size_t v___x_1225_; lean_object* v_j_1226_; lean_object* v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; lean_object* v___x_1234_; 
v_cs_1223_ = lean_ctor_get(v_x_1218_, 0);
lean_inc_ref(v_cs_1223_);
lean_dec_ref_known(v_x_1218_, 1);
v___x_1224_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0);
v___x_1225_ = lean_usize_shift_right(v_x_1219_, v_x_1220_);
v_j_1226_ = lean_usize_to_nat(v___x_1225_);
v___x_1227_ = lean_array_get_borrowed(v___x_1224_, v_cs_1223_, v_j_1226_);
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_shift_left(v___x_1228_, v_x_1220_);
v___x_1230_ = lean_usize_sub(v___x_1229_, v___x_1228_);
v___x_1231_ = lean_usize_land(v_x_1219_, v___x_1230_);
v___x_1232_ = ((size_t)5ULL);
v___x_1233_ = lean_usize_sub(v_x_1220_, v___x_1232_);
lean_inc(v___x_1227_);
v___x_1234_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1214_, v_json_1215_, v_includeEndPos_1216_, v_severityOverrides_1217_, v___x_1227_, v___x_1231_, v___x_1233_, v_x_1221_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = lean_nat_add(v_j_1226_, v___x_1236_);
lean_dec(v_j_1226_);
v___x_1238_ = lean_array_get_size(v_cs_1223_);
v___x_1239_ = lean_nat_dec_lt(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec(v___x_1237_);
lean_dec_ref(v_cs_1223_);
return v___x_1234_;
}
else
{
size_t v___x_1240_; size_t v___x_1241_; lean_object* v___x_1242_; 
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1240_ = lean_usize_of_nat(v___x_1237_);
lean_dec(v___x_1237_);
v___x_1241_ = lean_usize_of_nat(v___x_1238_);
v___x_1242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1214_, v_json_1215_, v_includeEndPos_1216_, v_severityOverrides_1217_, v_cs_1223_, v___x_1240_, v___x_1241_, v_a_1235_);
lean_dec_ref(v_cs_1223_);
return v___x_1242_;
}
}
else
{
lean_dec(v_j_1226_);
lean_dec_ref(v_cs_1223_);
return v___x_1234_;
}
}
else
{
lean_object* v_vs_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1256_; 
v_vs_1243_ = lean_ctor_get(v_x_1218_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_1218_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1245_ = v_x_1218_;
v_isShared_1246_ = v_isSharedCheck_1256_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_vs_1243_);
lean_dec(v_x_1218_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1256_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1247_ = lean_usize_to_nat(v_x_1219_);
v___x_1248_ = lean_array_get_size(v_vs_1243_);
v___x_1249_ = lean_nat_dec_lt(v___x_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1251_; 
lean_dec(v___x_1247_);
lean_dec_ref(v_vs_1243_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 0);
lean_ctor_set(v___x_1245_, 0, v_x_1221_);
v___x_1251_ = v___x_1245_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_x_1221_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
else
{
size_t v___x_1253_; size_t v___x_1254_; lean_object* v___x_1255_; 
lean_del_object(v___x_1245_);
v___x_1253_ = lean_usize_of_nat(v___x_1247_);
lean_dec(v___x_1247_);
v___x_1254_ = lean_usize_of_nat(v___x_1248_);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1214_, v_json_1215_, v_includeEndPos_1216_, v_severityOverrides_1217_, v_vs_1243_, v___x_1253_, v___x_1254_, v_x_1221_);
lean_dec_ref(v_vs_1243_);
return v___x_1255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___boxed(lean_object* v_opts_1257_, lean_object* v_json_1258_, lean_object* v_includeEndPos_1259_, lean_object* v_severityOverrides_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v___y_1265_){
_start:
{
uint8_t v_json_boxed_1266_; uint8_t v_includeEndPos_boxed_1267_; size_t v_x_2228__boxed_1268_; size_t v_x_2229__boxed_1269_; lean_object* v_res_1270_; 
v_json_boxed_1266_ = lean_unbox(v_json_1258_);
v_includeEndPos_boxed_1267_ = lean_unbox(v_includeEndPos_1259_);
v_x_2228__boxed_1268_ = lean_unbox_usize(v_x_1262_);
lean_dec(v_x_1262_);
v_x_2229__boxed_1269_ = lean_unbox_usize(v_x_1263_);
lean_dec(v_x_1263_);
v_res_1270_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1257_, v_json_boxed_1266_, v_includeEndPos_boxed_1267_, v_severityOverrides_1260_, v_x_1261_, v_x_2228__boxed_1268_, v_x_2229__boxed_1269_, v_x_1264_);
lean_dec(v_severityOverrides_1260_);
lean_dec_ref(v_opts_1257_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(lean_object* v_opts_1271_, uint8_t v_json_1272_, uint8_t v_includeEndPos_1273_, lean_object* v_severityOverrides_1274_, lean_object* v_t_1275_, lean_object* v_init_1276_, lean_object* v_start_1277_){
_start:
{
lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = lean_nat_dec_eq(v_start_1277_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v_root_1281_; lean_object* v_tail_1282_; size_t v_shift_1283_; lean_object* v_tailOff_1284_; uint8_t v___x_1285_; 
v_root_1281_ = lean_ctor_get(v_t_1275_, 0);
lean_inc_ref(v_root_1281_);
v_tail_1282_ = lean_ctor_get(v_t_1275_, 1);
lean_inc_ref(v_tail_1282_);
v_shift_1283_ = lean_ctor_get_usize(v_t_1275_, 4);
v_tailOff_1284_ = lean_ctor_get(v_t_1275_, 3);
lean_inc(v_tailOff_1284_);
lean_dec_ref(v_t_1275_);
v___x_1285_ = lean_nat_dec_le(v_tailOff_1284_, v_start_1277_);
if (v___x_1285_ == 0)
{
size_t v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_tailOff_1284_);
v___x_1286_ = lean_usize_of_nat(v_start_1277_);
v___x_1287_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1271_, v_json_1272_, v_includeEndPos_1273_, v_severityOverrides_1274_, v_root_1281_, v___x_1286_, v_shift_1283_, v_init_1276_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v___x_1289_ = lean_array_get_size(v_tail_1282_);
v___x_1290_ = lean_nat_dec_lt(v___x_1279_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_dec_ref(v_tail_1282_);
return v___x_1287_;
}
else
{
size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1291_ = ((size_t)0ULL);
v___x_1292_ = lean_usize_of_nat(v___x_1289_);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1271_, v_json_1272_, v_includeEndPos_1273_, v_severityOverrides_1274_, v_tail_1282_, v___x_1291_, v___x_1292_, v_a_1288_);
lean_dec_ref(v_tail_1282_);
return v___x_1293_;
}
}
else
{
lean_dec_ref(v_tail_1282_);
return v___x_1287_;
}
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
lean_dec_ref(v_root_1281_);
v___x_1294_ = lean_nat_sub(v_start_1277_, v_tailOff_1284_);
lean_dec(v_tailOff_1284_);
v___x_1295_ = lean_array_get_size(v_tail_1282_);
v___x_1296_ = lean_nat_dec_lt(v___x_1294_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
lean_dec(v___x_1294_);
lean_dec_ref(v_tail_1282_);
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v_init_1276_);
return v___x_1297_;
}
else
{
size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_usize_of_nat(v___x_1294_);
lean_dec(v___x_1294_);
v___x_1299_ = lean_usize_of_nat(v___x_1295_);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1271_, v_json_1272_, v_includeEndPos_1273_, v_severityOverrides_1274_, v_tail_1282_, v___x_1298_, v___x_1299_, v_init_1276_);
lean_dec_ref(v_tail_1282_);
return v___x_1300_;
}
}
}
else
{
lean_object* v_root_1301_; lean_object* v_tail_1302_; lean_object* v___x_1303_; 
v_root_1301_ = lean_ctor_get(v_t_1275_, 0);
lean_inc_ref(v_root_1301_);
v_tail_1302_ = lean_ctor_get(v_t_1275_, 1);
lean_inc_ref(v_tail_1302_);
lean_dec_ref(v_t_1275_);
v___x_1303_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1271_, v_json_1272_, v_includeEndPos_1273_, v_severityOverrides_1274_, v_root_1301_, v_init_1276_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v___x_1305_ = lean_array_get_size(v_tail_1302_);
v___x_1306_ = lean_nat_dec_lt(v___x_1279_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_dec_ref(v_tail_1302_);
return v___x_1303_;
}
else
{
size_t v___x_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1307_ = ((size_t)0ULL);
v___x_1308_ = lean_usize_of_nat(v___x_1305_);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1271_, v_json_1272_, v_includeEndPos_1273_, v_severityOverrides_1274_, v_tail_1302_, v___x_1307_, v___x_1308_, v_a_1304_);
lean_dec_ref(v_tail_1302_);
return v___x_1309_;
}
}
else
{
lean_dec_ref(v_tail_1302_);
return v___x_1303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4___boxed(lean_object* v_opts_1310_, lean_object* v_json_1311_, lean_object* v_includeEndPos_1312_, lean_object* v_severityOverrides_1313_, lean_object* v_t_1314_, lean_object* v_init_1315_, lean_object* v_start_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v_json_boxed_1318_; uint8_t v_includeEndPos_boxed_1319_; lean_object* v_res_1320_; 
v_json_boxed_1318_ = lean_unbox(v_json_1311_);
v_includeEndPos_boxed_1319_ = lean_unbox(v_includeEndPos_1312_);
v_res_1320_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1310_, v_json_boxed_1318_, v_includeEndPos_boxed_1319_, v_severityOverrides_1313_, v_t_1314_, v_init_1315_, v_start_1316_);
lean_dec(v_start_1316_);
lean_dec(v_severityOverrides_1313_);
lean_dec_ref(v_opts_1310_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(lean_object* v_msgLog_1321_, lean_object* v_opts_1322_, uint8_t v_json_1323_, lean_object* v_severityOverrides_1324_, lean_object* v_numErrors_1325_){
_start:
{
lean_object* v_unreported_1327_; lean_object* v___x_1328_; uint8_t v_includeEndPos_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_unreported_1327_ = lean_ctor_get(v_msgLog_1321_, 1);
lean_inc_ref(v_unreported_1327_);
lean_dec_ref(v_msgLog_1321_);
v___x_1328_ = l_Lean_Language_printMessageEndPos;
v_includeEndPos_1329_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_1322_, v___x_1328_);
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1322_, v_json_1323_, v_includeEndPos_1329_, v_severityOverrides_1324_, v_unreported_1327_, v_numErrors_1325_, v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___boxed(lean_object* v_msgLog_1332_, lean_object* v_opts_1333_, lean_object* v_json_1334_, lean_object* v_severityOverrides_1335_, lean_object* v_numErrors_1336_, lean_object* v_a_1337_){
_start:
{
uint8_t v_json_boxed_1338_; lean_object* v_res_1339_; 
v_json_boxed_1338_ = lean_unbox(v_json_1334_);
v_res_1339_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1332_, v_opts_1333_, v_json_boxed_1338_, v_severityOverrides_1335_, v_numErrors_1336_);
lean_dec(v_severityOverrides_1335_);
lean_dec_ref(v_opts_1333_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object* v_opts_1340_, uint8_t v_json_1341_, lean_object* v_severityOverrides_1342_, lean_object* v_s_1343_, lean_object* v_init_1344_){
_start:
{
lean_object* v_element_1346_; lean_object* v_diagnostics_1347_; lean_object* v_children_1348_; lean_object* v_msgLog_1349_; lean_object* v___x_1350_; 
v_element_1346_ = lean_ctor_get(v_s_1343_, 0);
v_diagnostics_1347_ = lean_ctor_get(v_element_1346_, 1);
lean_inc_ref(v_diagnostics_1347_);
v_children_1348_ = lean_ctor_get(v_s_1343_, 1);
lean_inc_ref(v_children_1348_);
lean_dec_ref(v_s_1343_);
v_msgLog_1349_ = lean_ctor_get(v_diagnostics_1347_, 0);
lean_inc_ref(v_msgLog_1349_);
lean_dec_ref(v_diagnostics_1347_);
v___x_1350_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1349_, v_opts_1340_, v_json_1341_, v_severityOverrides_1342_, v_init_1344_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v___x_1352_ = lean_unsigned_to_nat(0u);
v___x_1353_ = lean_array_get_size(v_children_1348_);
v___x_1354_ = lean_nat_dec_lt(v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_dec_ref(v_children_1348_);
return v___x_1350_;
}
else
{
size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = lean_usize_of_nat(v___x_1353_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1340_, v_json_1341_, v_severityOverrides_1342_, v_children_1348_, v___x_1355_, v___x_1356_, v_a_1351_);
lean_dec_ref(v_children_1348_);
return v___x_1357_;
}
}
else
{
lean_dec_ref(v_children_1348_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object* v_opts_1358_, uint8_t v_json_1359_, lean_object* v_severityOverrides_1360_, lean_object* v_as_1361_, size_t v_i_1362_, size_t v_stop_1363_, lean_object* v_b_1364_){
_start:
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_usize_dec_eq(v_i_1362_, v_stop_1363_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = lean_array_uget_borrowed(v_as_1361_, v_i_1362_);
lean_inc(v___x_1367_);
v___x_1368_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1367_);
v___x_1369_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1358_, v_json_1359_, v_severityOverrides_1360_, v___x_1368_, v_b_1364_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; size_t v___x_1371_; size_t v___x_1372_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = ((size_t)1ULL);
v___x_1372_ = lean_usize_add(v_i_1362_, v___x_1371_);
v_i_1362_ = v___x_1372_;
v_b_1364_ = v_a_1370_;
goto _start;
}
else
{
return v___x_1369_;
}
}
else
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_b_1364_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object* v_opts_1375_, lean_object* v_json_1376_, lean_object* v_severityOverrides_1377_, lean_object* v_as_1378_, lean_object* v_i_1379_, lean_object* v_stop_1380_, lean_object* v_b_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v_json_boxed_1383_; size_t v_i_boxed_1384_; size_t v_stop_boxed_1385_; lean_object* v_res_1386_; 
v_json_boxed_1383_ = lean_unbox(v_json_1376_);
v_i_boxed_1384_ = lean_unbox_usize(v_i_1379_);
lean_dec(v_i_1379_);
v_stop_boxed_1385_ = lean_unbox_usize(v_stop_1380_);
lean_dec(v_stop_1380_);
v_res_1386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1375_, v_json_boxed_1383_, v_severityOverrides_1377_, v_as_1378_, v_i_boxed_1384_, v_stop_boxed_1385_, v_b_1381_);
lean_dec_ref(v_as_1378_);
lean_dec(v_severityOverrides_1377_);
lean_dec_ref(v_opts_1375_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object* v_opts_1387_, lean_object* v_json_1388_, lean_object* v_severityOverrides_1389_, lean_object* v_s_1390_, lean_object* v_init_1391_, lean_object* v___y_1392_){
_start:
{
uint8_t v_json_boxed_1393_; lean_object* v_res_1394_; 
v_json_boxed_1393_ = lean_unbox(v_json_1388_);
v_res_1394_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1387_, v_json_boxed_1393_, v_severityOverrides_1389_, v_s_1390_, v_init_1391_);
lean_dec(v_severityOverrides_1389_);
lean_dec_ref(v_opts_1387_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object* v_s_1395_, lean_object* v_opts_1396_, uint8_t v_json_1397_, lean_object* v_severityOverrides_1398_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1396_, v_json_1397_, v_severityOverrides_1398_, v_s_1395_, v___x_1400_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1411_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1406_ = lean_nat_dec_lt(v___x_1400_, v_a_1402_);
lean_dec(v_a_1402_);
v___x_1407_ = lean_box(v___x_1406_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1407_);
v___x_1409_ = v___x_1404_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_a_1412_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1401_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1401_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object* v_s_1420_, lean_object* v_opts_1421_, lean_object* v_json_1422_, lean_object* v_severityOverrides_1423_, lean_object* v_a_1424_){
_start:
{
uint8_t v_json_boxed_1425_; lean_object* v_res_1426_; 
v_json_boxed_1425_ = lean_unbox(v_json_1422_);
v_res_1426_ = l_Lean_Language_SnapshotTree_runAndReport(v_s_1420_, v_opts_1421_, v_json_boxed_1425_, v_severityOverrides_1423_);
lean_dec(v_severityOverrides_1423_);
lean_dec_ref(v_opts_1421_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(lean_object* v_s_1427_, lean_object* v_init_1428_){
_start:
{
lean_object* v_element_1429_; lean_object* v_children_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_element_1429_ = lean_ctor_get(v_s_1427_, 0);
lean_inc_ref(v_element_1429_);
v_children_1430_ = lean_ctor_get(v_s_1427_, 1);
lean_inc_ref(v_children_1430_);
lean_dec_ref(v_s_1427_);
v___x_1431_ = lean_array_push(v_init_1428_, v_element_1429_);
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1433_ = lean_array_get_size(v_children_1430_);
v___x_1434_ = lean_nat_dec_lt(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_dec_ref(v_children_1430_);
return v___x_1431_;
}
else
{
size_t v___x_1435_; size_t v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = lean_usize_of_nat(v___x_1433_);
v___x_1437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_1430_, v___x_1435_, v___x_1436_, v___x_1431_);
lean_dec_ref(v_children_1430_);
return v___x_1437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object* v_as_1438_, size_t v_i_1439_, size_t v_stop_1440_, lean_object* v_b_1441_){
_start:
{
uint8_t v___x_1442_; 
v___x_1442_ = lean_usize_dec_eq(v_i_1439_, v_stop_1440_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; 
v___x_1443_ = lean_array_uget_borrowed(v_as_1438_, v_i_1439_);
lean_inc(v___x_1443_);
v___x_1444_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1443_);
v___x_1445_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v___x_1444_, v_b_1441_);
v___x_1446_ = ((size_t)1ULL);
v___x_1447_ = lean_usize_add(v_i_1439_, v___x_1446_);
v_i_1439_ = v___x_1447_;
v_b_1441_ = v___x_1445_;
goto _start;
}
else
{
return v_b_1441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object* v_as_1449_, lean_object* v_i_1450_, lean_object* v_stop_1451_, lean_object* v_b_1452_){
_start:
{
size_t v_i_boxed_1453_; size_t v_stop_boxed_1454_; lean_object* v_res_1455_; 
v_i_boxed_1453_ = lean_unbox_usize(v_i_1450_);
lean_dec(v_i_1450_);
v_stop_boxed_1454_ = lean_unbox_usize(v_stop_1451_);
lean_dec(v_stop_1451_);
v_res_1455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_as_1449_, v_i_boxed_1453_, v_stop_boxed_1454_, v_b_1452_);
lean_dec_ref(v_as_1449_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object* v_s_1458_){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_Lean_Language_SnapshotTree_getAll___closed__0));
v___x_1460_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v_s_1458_, v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_box(0);
v___x_1462_ = lean_task_pure(v___x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed(lean_object* v_tail_1463_, lean_object* v_t_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(v_tail_1463_, v_t_1464_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(lean_object* v_a_1467_){
_start:
{
if (lean_obj_tag(v_a_1467_) == 0)
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_obj_once(&l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0, &l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0_once, _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0);
return v___x_1469_;
}
else
{
lean_object* v_head_1470_; lean_object* v_tail_1471_; lean_object* v_task_1472_; lean_object* v___f_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; 
v_head_1470_ = lean_ctor_get(v_a_1467_, 0);
lean_inc(v_head_1470_);
v_tail_1471_ = lean_ctor_get(v_a_1467_, 1);
lean_inc(v_tail_1471_);
lean_dec_ref_known(v_a_1467_, 2);
v_task_1472_ = lean_ctor_get(v_head_1470_, 3);
lean_inc_ref(v_task_1472_);
lean_dec(v_head_1470_);
v___f_1473_ = lean_alloc_closure((void*)(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1473_, 0, v_tail_1471_);
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = 1;
v___x_1476_ = lean_io_bind_task(v_task_1472_, v___f_1473_, v___x_1474_, v___x_1475_);
return v___x_1476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object* v_tail_1477_, lean_object* v_t_1478_){
_start:
{
lean_object* v_children_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_children_1480_ = lean_ctor_get(v_t_1478_, 1);
lean_inc_ref(v_children_1480_);
lean_dec_ref(v_t_1478_);
v___x_1481_ = lean_array_to_list(v_children_1480_);
v___x_1482_ = l_List_appendTR___redArg(v___x_1481_, v_tail_1477_);
v___x_1483_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___boxed(lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v_a_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object* v_x_1487_){
_start:
{
lean_object* v_children_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_children_1489_ = lean_ctor_get(v_x_1487_, 1);
lean_inc_ref(v_children_1489_);
lean_dec_ref(v_x_1487_);
v___x_1490_ = lean_array_to_list(v_children_1489_);
v___x_1491_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll___boxed(lean_object* v_x_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Language_SnapshotTree_waitAll(v_x_1492_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object* v_00_u03b1_1495_, lean_object* v_act_1496_, lean_object* v_ctx_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_apply_2(v_act_1496_, v_ctx_1497_, lean_box(0));
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0___boxed(lean_object* v_00_u03b1_1501_, lean_object* v_act_1502_, lean_object* v_ctx_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(v_00_u03b1_1501_, v_act_1502_, v_ctx_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object* v_msgLog_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_st_mk_ref(v___x_1510_);
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v_msgLog_1508_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog___boxed(lean_object* v_msgLog_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object* v_msg_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_fileMap_1524_; lean_object* v_source_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; uint8_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_fileMap_1524_ = lean_ctor_get(v_a_1522_, 2);
v_source_1525_ = lean_ctor_get(v_fileMap_1524_, 0);
v___x_1526_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__0));
v___x_1527_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__1));
v___x_1528_ = lean_string_utf8_byte_size(v_source_1525_);
lean_inc_ref(v_fileMap_1524_);
v___x_1529_ = l_Lean_FileMap_toPosition(v_fileMap_1524_, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
v___x_1531_ = 0;
v___x_1532_ = 2;
v___x_1533_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot___closed__0));
v___x_1534_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_msg_1521_);
v___x_1535_ = l_Lean_MessageData_ofFormat(v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1536_, 0, v___x_1526_);
lean_ctor_set(v___x_1536_, 1, v___x_1527_);
lean_ctor_set(v___x_1536_, 2, v___x_1530_);
lean_ctor_set(v___x_1536_, 3, v___x_1533_);
lean_ctor_set(v___x_1536_, 4, v___x_1535_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*5, v___x_1531_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*5 + 1, v___x_1532_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*5 + 2, v___x_1531_);
v___x_1537_ = l_Lean_MessageLog_empty;
v___x_1538_ = l_Lean_MessageLog_add(v___x_1536_, v___x_1537_);
v___x_1539_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError___boxed(lean_object* v_msg_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Language_diagnosticsOfHeaderError(v_msg_1540_, v_a_1541_);
lean_dec_ref(v_a_1541_);
return v_res_1543_;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2(void){
_start:
{
uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = 1;
v___x_1550_ = ((lean_object*)(l_Lean_Language_withHeaderExceptions___redArg___closed__1));
v___x_1551_ = l_Lean_Name_toString(v___x_1550_, v___x_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object* v_ex_1552_, lean_object* v_act_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1556_; 
lean_inc_ref(v_a_1554_);
v___x_1556_ = lean_apply_2(v_act_1553_, v_a_1554_, lean_box(0));
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; 
lean_dec(v_ex_1552_);
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
return v_a_1557_;
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_a_1558_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1559_ = lean_io_error_to_string(v_a_1558_);
v___x_1560_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_1559_, v_a_1554_);
v___x_1561_ = lean_obj_once(&l_Lean_Language_withHeaderExceptions___redArg___closed__2, &l_Lean_Language_withHeaderExceptions___redArg___closed__2_once, _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2);
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_1564_ = 0;
v___x_1565_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1565_, 0, v___x_1561_);
lean_ctor_set(v___x_1565_, 1, v___x_1560_);
lean_ctor_set(v___x_1565_, 2, v___x_1562_);
lean_ctor_set(v___x_1565_, 3, v___x_1563_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*4, v___x_1564_);
v___x_1566_ = lean_apply_1(v_ex_1552_, v___x_1565_);
return v___x_1566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg___boxed(lean_object* v_ex_1567_, lean_object* v_act_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1567_, v_act_1568_, v_a_1569_);
lean_dec_ref(v_a_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object* v_00_u03b1_1572_, lean_object* v_ex_1573_, lean_object* v_act_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1573_, v_act_1574_, v_a_1575_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___boxed(lean_object* v_00_u03b1_1578_, lean_object* v_ex_1579_, lean_object* v_act_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Language_withHeaderExceptions(v_00_u03b1_1578_, v_ex_1579_, v_act_1580_, v_a_1581_);
lean_dec_ref(v_a_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object* v_val_1584_, lean_object* v_process_1585_, lean_object* v_ictx_1586_){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1588_ = lean_st_ref_get(v_val_1584_);
v___x_1589_ = lean_apply_3(v_process_1585_, v___x_1588_, v_ictx_1586_, lean_box(0));
lean_inc(v___x_1589_);
v___x_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
v___x_1591_ = lean_st_ref_swap(v_val_1584_, v___x_1590_);
lean_dec(v___x_1591_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object* v_val_1592_, lean_object* v_process_1593_, lean_object* v_ictx_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(v_val_1592_, v_process_1593_, v_ictx_1594_);
lean_dec(v_val_1592_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object* v_process_1597_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___f_1601_; 
v___x_1599_ = lean_box(0);
v___x_1600_ = lean_st_mk_ref(v___x_1599_);
v___f_1601_ = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1601_, 0, v___x_1600_);
lean_closure_set(v___f_1601_, 1, v_process_1597_);
return v___f_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___boxed(lean_object* v_process_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1602_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object* v_InitSnap_1605_, lean_object* v_process_1606_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___boxed(lean_object* v_InitSnap_1609_, lean_object* v_process_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Language_mkIncrementalProcessor(v_InitSnap_1609_, v_process_1610_);
return v_res_1612_;
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
