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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* lean_io_error_to_string(lean_object*);
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
static lean_once_cell_t l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__0;
static lean_once_cell_t l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform;
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
static const lean_ctor_object l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
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
lean_dec_ref_known(v_t_149_, 1);
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
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__0(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot___closed__0));
v___x_406_ = lean_string_utf8_byte_size(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__1(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_407_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__0, &l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__0_once, _init_l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__0);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot___closed__0));
v___x_410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_407_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTreeTransform_default(void){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__1, &l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__1_once, _init_l_Lean_Language_instInhabitedSnapshotTreeTransform_default___closed__1);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTreeTransform(void){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
return v___x_412_;
}
}
LEAN_EXPORT uint8_t l_Lean_Language_SnapshotTreeTransform_isIdentity(lean_object* v_trans_413_){
_start:
{
lean_object* v_startPos_414_; lean_object* v_stopPos_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_startPos_414_ = lean_ctor_get(v_trans_413_, 1);
v_stopPos_415_ = lean_ctor_get(v_trans_413_, 2);
v___x_416_ = lean_nat_sub(v_stopPos_415_, v_startPos_414_);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_nat_dec_eq(v___x_416_, v___x_417_);
lean_dec(v___x_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_isIdentity___boxed(lean_object* v_trans_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_trans_419_);
lean_dec_ref(v_trans_419_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformSyntax(lean_object* v_trans_422_, lean_object* v_stx_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Syntax_addTrailing(v_stx_423_, v_trans_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformInfoTree(lean_object* v_trans_425_, lean_object* v_t_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Elab_InfoTree_addTrailing(v_trans_425_, v_t_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_transformInfoTree_x3f(lean_object* v_trans_428_, lean_object* v_t_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Elab_InfoTree_addTrailing_x3f(v_trans_428_, v_t_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_compose(lean_object* v_outer_431_, lean_object* v_inner_432_){
_start:
{
lean_object* v_str_433_; lean_object* v_startPos_434_; lean_object* v_stopPos_435_; lean_object* v_startPos_436_; lean_object* v_stopPos_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_445_; 
v_str_433_ = lean_ctor_get(v_inner_432_, 0);
v_startPos_434_ = lean_ctor_get(v_inner_432_, 1);
v_stopPos_435_ = lean_ctor_get(v_inner_432_, 2);
v_startPos_436_ = lean_ctor_get(v_outer_431_, 1);
v_stopPos_437_ = lean_ctor_get(v_outer_431_, 2);
v_isSharedCheck_445_ = !lean_is_exclusive(v_outer_431_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v_outer_431_, 0);
lean_dec(v_unused_446_);
v___x_439_ = v_outer_431_;
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_stopPos_437_);
lean_inc(v_startPos_436_);
lean_dec(v_outer_431_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
uint8_t v___x_441_; 
v___x_441_ = lean_nat_dec_eq(v_stopPos_435_, v_startPos_436_);
lean_dec(v_startPos_436_);
if (v___x_441_ == 0)
{
lean_del_object(v___x_439_);
lean_dec(v_stopPos_437_);
lean_inc_ref(v_inner_432_);
return v_inner_432_;
}
else
{
lean_object* v___x_443_; 
lean_inc(v_startPos_434_);
lean_inc_ref(v_str_433_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_startPos_434_);
lean_ctor_set(v___x_439_, 0, v_str_433_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_str_433_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_startPos_434_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_stopPos_437_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTreeTransform_compose___boxed(lean_object* v_outer_447_, lean_object* v_inner_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Language_SnapshotTreeTransform_compose(v_outer_447_, v_inner_448_);
lean_dec_ref(v_inner_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_transform(lean_object* v_s_450_, lean_object* v_a_451_){
_start:
{
uint8_t v___x_452_; 
v___x_452_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_a_451_);
if (v___x_452_ == 0)
{
lean_object* v_infoTree_x3f_453_; 
v_infoTree_x3f_453_ = lean_ctor_get(v_s_450_, 2);
if (lean_obj_tag(v_infoTree_x3f_453_) == 0)
{
return v_s_450_;
}
else
{
lean_object* v_desc_454_; lean_object* v_diagnostics_455_; lean_object* v_traces_456_; uint8_t v_isFatal_457_; lean_object* v_val_458_; lean_object* v___x_459_; 
v_desc_454_ = lean_ctor_get(v_s_450_, 0);
v_diagnostics_455_ = lean_ctor_get(v_s_450_, 1);
v_traces_456_ = lean_ctor_get(v_s_450_, 3);
v_isFatal_457_ = lean_ctor_get_uint8(v_s_450_, sizeof(void*)*4);
v_val_458_ = lean_ctor_get(v_infoTree_x3f_453_, 0);
lean_inc(v_val_458_);
lean_inc_ref(v_a_451_);
v___x_459_ = l_Lean_Elab_InfoTree_addTrailing_x3f(v_a_451_, v_val_458_);
if (lean_obj_tag(v___x_459_) == 0)
{
return v_s_450_;
}
else
{
lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_inc_ref(v_traces_456_);
lean_inc_ref(v_diagnostics_455_);
lean_inc_ref(v_desc_454_);
v_isSharedCheck_466_ = !lean_is_exclusive(v_s_450_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; lean_object* v_unused_468_; lean_object* v_unused_469_; lean_object* v_unused_470_; 
v_unused_467_ = lean_ctor_get(v_s_450_, 3);
lean_dec(v_unused_467_);
v_unused_468_ = lean_ctor_get(v_s_450_, 2);
lean_dec(v_unused_468_);
v_unused_469_ = lean_ctor_get(v_s_450_, 1);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_s_450_, 0);
lean_dec(v_unused_470_);
v___x_461_ = v_s_450_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_dec(v_s_450_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 2, v___x_459_);
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_desc_454_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_diagnostics_455_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_traces_456_);
lean_ctor_set_uint8(v_reuseFailAlloc_465_, sizeof(void*)*4, v_isFatal_457_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
else
{
return v_s_450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_transform___boxed(lean_object* v_s_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Language_Snapshot_transform(v_s_471_, v_a_472_);
lean_dec_ref(v_a_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0___boxed(lean_object* v_a_474_, lean_object* v_x_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0(v_a_474_, v_x_475_);
lean_dec_ref(v_a_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(lean_object* v_a_477_, size_t v_sz_478_, size_t v_i_479_, lean_object* v_bs_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = lean_usize_dec_lt(v_i_479_, v_sz_478_);
if (v___x_481_ == 0)
{
return v_bs_480_;
}
else
{
lean_object* v_v_482_; lean_object* v_stx_x3f_483_; lean_object* v_reportingRange_484_; lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v_bs_x27_487_; lean_object* v___x_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
v_v_482_ = lean_array_uget(v_bs_480_, v_i_479_);
v_stx_x3f_483_ = lean_ctor_get(v_v_482_, 0);
lean_inc(v_stx_x3f_483_);
v_reportingRange_484_ = lean_ctor_get(v_v_482_, 1);
lean_inc(v_reportingRange_484_);
lean_inc_ref(v_a_477_);
v___f_485_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_485_, 0, v_a_477_);
v___x_486_ = lean_unsigned_to_nat(0u);
v_bs_x27_487_ = lean_array_uset(v_bs_480_, v_i_479_, v___x_486_);
v___x_488_ = l_Lean_Language_SnapshotTask_map___redArg(v_v_482_, v___f_485_, v_stx_x3f_483_, v_reportingRange_484_, v___x_481_);
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_479_, v___x_489_);
v___x_491_ = lean_array_uset(v_bs_x27_487_, v_i_479_, v___x_488_);
v_i_479_ = v___x_490_;
v_bs_480_ = v___x_491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_transform(lean_object* v_t_493_, lean_object* v_a_494_){
_start:
{
uint8_t v___x_495_; 
v___x_495_ = l_Lean_Language_SnapshotTreeTransform_isIdentity(v_a_494_);
if (v___x_495_ == 0)
{
lean_object* v_element_496_; lean_object* v_children_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_508_; 
v_element_496_ = lean_ctor_get(v_t_493_, 0);
v_children_497_ = lean_ctor_get(v_t_493_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_t_493_);
if (v_isSharedCheck_508_ == 0)
{
v___x_499_ = v_t_493_;
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_children_497_);
lean_inc(v_element_496_);
lean_dec(v_t_493_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; size_t v_sz_502_; size_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_501_ = l_Lean_Language_Snapshot_transform(v_element_496_, v_a_494_);
v_sz_502_ = lean_array_size(v_children_497_);
v___x_503_ = ((size_t)0ULL);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(v_a_494_, v_sz_502_, v___x_503_, v_children_497_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v___x_504_);
lean_ctor_set(v___x_499_, 0, v___x_501_);
v___x_506_ = v___x_499_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
return v_t_493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___lam__0(lean_object* v_a_509_, lean_object* v_x_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_Language_SnapshotTree_transform(v_x_510_, v_a_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object* v_t_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Language_SnapshotTree_transform(v_t_512_, v_a_513_);
lean_dec_ref(v_a_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0___boxed(lean_object* v_a_515_, lean_object* v_sz_516_, lean_object* v_i_517_, lean_object* v_bs_518_){
_start:
{
size_t v_sz_boxed_519_; size_t v_i_boxed_520_; lean_object* v_res_521_; 
v_sz_boxed_519_ = lean_unbox_usize(v_sz_516_);
lean_dec(v_sz_516_);
v_i_boxed_520_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Language_SnapshotTree_transform_spec__0(v_a_515_, v_sz_boxed_519_, v_i_boxed_520_, v_bs_518_);
lean_dec_ref(v_a_515_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___redArg(lean_object* v_inst_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_525_ = lean_apply_2(v_inst_522_, v_a_523_, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree(lean_object* v_00_u03b1_526_, lean_object* v_inst_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Language_toSnapshotTree___redArg(v_inst_527_, v_a_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedTransformedSnap___redArg(lean_object* v_inst_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_inst_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedTransformedSnap(lean_object* v_00_u03b1_533_, lean_object* v_inst_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Language_instInhabitedTransformedSnap___redArg(v_inst_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0(lean_object* v_inst_536_, lean_object* v_s_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_raw_539_; lean_object* v_transform_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_raw_539_ = lean_ctor_get(v_s_537_, 0);
lean_inc(v_raw_539_);
v_transform_540_ = lean_ctor_get(v_s_537_, 1);
lean_inc_ref(v_transform_540_);
lean_dec_ref(v_s_537_);
lean_inc_ref(v___y_538_);
v___x_541_ = l_Lean_Language_SnapshotTreeTransform_compose(v___y_538_, v_transform_540_);
lean_dec_ref(v_transform_540_);
v___x_542_ = lean_apply_2(v_inst_536_, v_raw_539_, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed(lean_object* v_inst_543_, lean_object* v_s_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0(v_inst_543_, v_s_544_, v___y_545_);
lean_dec_ref(v___y_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg(lean_object* v_inst_547_){
_start:
{
lean_object* v___f_548_; 
v___f_548_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_548_, 0, v_inst_547_);
return v___f_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeTransformedSnap(lean_object* v_00_u03b1_549_, lean_object* v_inst_550_){
_start:
{
lean_object* v___f_551_; 
v___f_551_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeTransformedSnap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_551_, 0, v_inst_550_);
return v___f_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_TransformedSnap_compose___redArg(lean_object* v_outer_552_, lean_object* v_s_553_){
_start:
{
lean_object* v_raw_554_; lean_object* v_transform_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_raw_554_ = lean_ctor_get(v_s_553_, 0);
v_transform_555_ = lean_ctor_get(v_s_553_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_s_553_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v_s_553_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_transform_555_);
lean_inc(v_raw_554_);
lean_dec(v_s_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = l_Lean_Language_SnapshotTreeTransform_compose(v_outer_552_, v_transform_555_);
lean_dec_ref(v_transform_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_raw_554_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_TransformedSnap_compose(lean_object* v_00_u03b1_564_, lean_object* v_outer_565_, lean_object* v_s_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Language_TransformedSnap_compose___redArg(v_outer_565_, v_s_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0(lean_object* v_f_568_, lean_object* v_a_569_, lean_object* v_x_570_){
_start:
{
lean_object* v___x_571_; 
lean_inc_ref(v_a_569_);
v___x_571_ = lean_apply_2(v_f_568_, v_x_570_, v_a_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0___boxed(lean_object* v_f_572_, lean_object* v_a_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0(v_f_572_, v_a_573_, v_x_574_);
lean_dec_ref(v_a_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object* v_t_576_, lean_object* v_f_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_stx_x3f_579_; lean_object* v_reportingRange_580_; lean_object* v___f_581_; uint8_t v___x_582_; lean_object* v___x_583_; 
v_stx_x3f_579_ = lean_ctor_get(v_t_576_, 0);
lean_inc(v_stx_x3f_579_);
v_reportingRange_580_ = lean_ctor_get(v_t_576_, 1);
lean_inc(v_reportingRange_580_);
lean_inc_ref(v_a_578_);
v___f_581_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_transformWith___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_581_, 0, v_f_577_);
lean_closure_set(v___f_581_, 1, v_a_578_);
v___x_582_ = 1;
v___x_583_ = l_Lean_Language_SnapshotTask_map___redArg(v_t_576_, v___f_581_, v_stx_x3f_579_, v_reportingRange_580_, v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg___boxed(lean_object* v_t_584_, lean_object* v_f_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_584_, v_f_585_, v_a_586_);
lean_dec_ref(v_a_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith(lean_object* v_00_u03b1_588_, lean_object* v_t_589_, lean_object* v_f_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_589_, v_f_590_, v_a_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transformWith___boxed(lean_object* v_00_u03b1_593_, lean_object* v_t_594_, lean_object* v_f_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Language_SnapshotTask_transformWith(v_00_u03b1_593_, v_t_594_, v_f_595_, v_a_596_);
lean_dec_ref(v_a_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___redArg(lean_object* v_inst_598_, lean_object* v_t_599_, lean_object* v_a_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_599_, v_inst_598_, v_a_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___redArg___boxed(lean_object* v_inst_602_, lean_object* v_t_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_Language_SnapshotTask_transform___redArg(v_inst_602_, v_t_603_, v_a_604_);
lean_dec_ref(v_a_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform(lean_object* v_00_u03b1_606_, lean_object* v_inst_607_, lean_object* v_t_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_608_, v_inst_607_, v_a_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___boxed(lean_object* v_00_u03b1_611_, lean_object* v_inst_612_, lean_object* v_t_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Language_SnapshotTask_transform(v_00_u03b1_611_, v_inst_612_, v_t_613_, v_a_614_);
lean_dec_ref(v_a_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object* v_inst_618_, lean_object* v_x_619_, lean_object* v___y_620_){
_start:
{
if (lean_obj_tag(v_x_619_) == 0)
{
lean_object* v___x_621_; 
lean_dec_ref(v_inst_618_);
v___x_621_ = l_Lean_Language_instInhabitedSnapshotTree_default;
return v___x_621_;
}
else
{
lean_object* v_val_622_; lean_object* v___x_623_; 
v_val_622_ = lean_ctor_get(v_x_619_, 0);
lean_inc(v_val_622_);
lean_dec_ref_known(v_x_619_, 1);
lean_inc_ref(v___y_620_);
v___x_623_ = lean_apply_2(v_inst_618_, v_val_622_, v___y_620_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed(lean_object* v_inst_624_, lean_object* v_x_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(v_inst_624_, v_x_625_, v___y_626_);
lean_dec_ref(v___y_626_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg(lean_object* v_inst_628_){
_start:
{
lean_object* v___f_629_; 
v___f_629_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_629_, 0, v_inst_628_);
return v___f_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object* v_00_u03b1_630_, lean_object* v_inst_631_){
_start:
{
lean_object* v___f_632_; 
v___f_632_ = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_632_, 0, v_inst_631_);
return v___f_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(lean_object* v_inst_633_, lean_object* v___x_634_, lean_object* v___f_635_, lean_object* v_snap_636_){
_start:
{
lean_object* v___x_638_; lean_object* v_children_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_638_ = l_Lean_Language_toSnapshotTree___redArg(v_inst_633_, v_snap_636_);
v_children_639_ = lean_ctor_get(v___x_638_, 1);
lean_inc_ref(v_children_639_);
lean_dec_ref(v___x_638_);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_array_get_size(v_children_639_);
v___x_642_ = lean_box(0);
v___x_643_ = lean_nat_dec_lt(v___x_640_, v___x_641_);
if (v___x_643_ == 0)
{
lean_dec_ref(v_children_639_);
lean_dec_ref(v___f_635_);
lean_dec_ref(v___x_634_);
return v___x_642_;
}
else
{
uint8_t v___x_644_; 
v___x_644_ = lean_nat_dec_le(v___x_641_, v___x_641_);
if (v___x_644_ == 0)
{
if (v___x_643_ == 0)
{
lean_dec_ref(v_children_639_);
lean_dec_ref(v___f_635_);
lean_dec_ref(v___x_634_);
return v___x_642_;
}
else
{
size_t v___x_645_; size_t v___x_646_; lean_object* v___x_218__overap_647_; lean_object* v___x_648_; 
v___x_645_ = ((size_t)0ULL);
v___x_646_ = lean_usize_of_nat(v___x_641_);
v___x_218__overap_647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_634_, v___f_635_, v_children_639_, v___x_645_, v___x_646_, v___x_642_);
v___x_648_ = lean_apply_1(v___x_218__overap_647_, lean_box(0));
return v___x_648_;
}
}
else
{
size_t v___x_649_; size_t v___x_650_; lean_object* v___x_221__overap_651_; lean_object* v___x_652_; 
v___x_649_ = ((size_t)0ULL);
v___x_650_ = lean_usize_of_nat(v___x_641_);
v___x_221__overap_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_634_, v___f_635_, v_children_639_, v___x_649_, v___x_650_, v___x_642_);
v___x_652_ = lean_apply_1(v___x_221__overap_651_, lean_box(0));
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed(lean_object* v_inst_653_, lean_object* v___x_654_, lean_object* v___f_655_, lean_object* v_snap_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(v_inst_653_, v___x_654_, v___f_655_, v_snap_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(lean_object* v___f_659_, lean_object* v_x_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(v___f_659_, v_x_660_, v___y_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object* v_inst_664_, lean_object* v_t_665_){
_start:
{
lean_object* v___x_667_; lean_object* v_cancelTk_x3f_668_; lean_object* v_task_669_; lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___f_672_; 
v___x_667_ = l_instMonadBaseIO;
v_cancelTk_x3f_668_ = lean_ctor_get(v_t_665_, 2);
lean_inc(v_cancelTk_x3f_668_);
v_task_669_ = lean_ctor_get(v_t_665_, 3);
lean_inc_ref(v_task_669_);
lean_dec_ref(v_t_665_);
v___f_670_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0));
v___f_671_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_671_, 0, v___f_670_);
v___f_672_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_672_, 0, v_inst_664_);
lean_closure_set(v___f_672_, 1, v___x_667_);
lean_closure_set(v___f_672_, 2, v___f_671_);
if (lean_obj_tag(v_cancelTk_x3f_668_) == 1)
{
lean_object* v_val_677_; lean_object* v___x_678_; 
v_val_677_ = lean_ctor_get(v_cancelTk_x3f_668_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v_cancelTk_x3f_668_, 1);
v___x_678_ = l_IO_CancelToken_set(v_val_677_);
lean_dec(v_val_677_);
goto v___jp_673_;
}
else
{
lean_dec(v_cancelTk_x3f_668_);
goto v___jp_673_;
}
v___jp_673_:
{
lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = 1;
v___x_676_ = l_BaseIO_chainTask___redArg(v_task_669_, v___f_672_, v___x_674_, v___x_675_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object* v___f_679_, lean_object* v_x_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_679_, v___y_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___boxed(lean_object* v_inst_684_, lean_object* v_t_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_684_, v_t_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object* v_00_u03b1_688_, lean_object* v_inst_689_, lean_object* v_t_690_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_689_, v_t_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___boxed(lean_object* v_00_u03b1_693_, lean_object* v_inst_694_, lean_object* v_t_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Language_SnapshotTask_cancelRec(v_00_u03b1_693_, v_inst_694_, v_t_695_);
return v_res_697_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotLeaf(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_unsigned_to_nat(32u);
v___x_706_ = lean_mk_empty_array_with_capacity(v___x_705_);
lean_dec_ref(v___x_706_);
v___x_707_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__4, &l_Lean_Language_instInhabitedSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__4);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object* v_s_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = l_Lean_Language_Snapshot_transform(v_s_710_, v___y_711_);
v___x_713_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0));
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___boxed(lean_object* v_s_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(v_s_715_, v___y_716_);
lean_dec_ref(v___y_716_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object* v_s_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_toSnapshotTreeM_722_; lean_object* v___x_723_; 
v_toSnapshotTreeM_722_ = lean_ctor_get(v_s_720_, 1);
lean_inc_ref(v_toSnapshotTreeM_722_);
lean_dec_ref(v_s_720_);
lean_inc_ref(v___y_721_);
v___x_723_ = lean_apply_1(v_toSnapshotTreeM_722_, v___y_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object* v_s_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(v_s_724_, v___y_725_);
lean_dec_ref(v___y_725_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_val_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
lean_inc(v_val_731_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_inst_729_);
lean_ctor_set(v___x_732_, 1, v_val_731_);
v___x_733_ = lean_apply_1(v_inst_730_, v_val_731_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object* v_00_u03b1_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_val_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v_inst_736_, v_inst_737_, v_val_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object* v_inst_740_, lean_object* v_snap_741_){
_start:
{
lean_object* v_val_742_; lean_object* v___x_743_; 
v_val_742_ = lean_ctor_get(v_snap_741_, 0);
v___x_743_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_742_, v_inst_740_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object* v_inst_744_, lean_object* v_snap_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_744_, v_snap_745_);
lean_dec_ref(v_snap_745_);
lean_dec(v_inst_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object* v_00_u03b1_747_, lean_object* v_inst_748_, lean_object* v_snap_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_748_, v_snap_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object* v_00_u03b1_751_, lean_object* v_inst_752_, lean_object* v_snap_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f(v_00_u03b1_751_, v_inst_752_, v_snap_753_);
lean_dec_ref(v_snap_753_);
lean_dec(v_inst_752_);
return v_res_754_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2(void){
_start:
{
uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = 1;
v___x_761_ = ((lean_object*)(l_Lean_Language_instInhabitedDynamicSnapshot___closed__1));
v___x_762_ = l_Lean_Name_toString(v___x_761_, v___x_760_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3(void){
_start:
{
uint8_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_763_ = 0;
v___x_764_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_765_ = lean_box(0);
v___x_766_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_767_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__2, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__2_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2);
v___x_768_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v___x_766_);
lean_ctor_set(v___x_768_, 2, v___x_765_);
lean_ctor_set(v___x_768_, 3, v___x_764_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*4, v___x_763_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4(void){
_start:
{
lean_object* v___x_769_; lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_769_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__3, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3);
v___f_770_ = ((lean_object*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0));
v___x_771_ = ((lean_object*)(l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_));
v___x_772_ = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v___x_771_, v___f_770_, v___x_769_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot(void){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_obj_once(&l_Lean_Language_instInhabitedDynamicSnapshot___closed__4, &l_Lean_Language_instInhabitedDynamicSnapshot___closed__4_once, _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object* v_children_774_, lean_object* v_toApplicative_775_, lean_object* v_inst_776_, lean_object* v___f_777_, lean_object* v_____r_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_array_get_size(v_children_774_);
v___x_781_ = lean_box(0);
v___x_782_ = lean_nat_dec_lt(v___x_779_, v___x_780_);
if (v___x_782_ == 0)
{
lean_object* v_toPure_783_; lean_object* v___x_784_; 
lean_dec(v___f_777_);
lean_dec_ref(v_inst_776_);
lean_dec_ref(v_children_774_);
v_toPure_783_ = lean_ctor_get(v_toApplicative_775_, 1);
lean_inc(v_toPure_783_);
lean_dec_ref(v_toApplicative_775_);
v___x_784_ = lean_apply_2(v_toPure_783_, lean_box(0), v___x_781_);
return v___x_784_;
}
else
{
uint8_t v___x_785_; 
v___x_785_ = lean_nat_dec_le(v___x_780_, v___x_780_);
if (v___x_785_ == 0)
{
if (v___x_782_ == 0)
{
lean_object* v_toPure_786_; lean_object* v___x_787_; 
lean_dec(v___f_777_);
lean_dec_ref(v_inst_776_);
lean_dec_ref(v_children_774_);
v_toPure_786_ = lean_ctor_get(v_toApplicative_775_, 1);
lean_inc(v_toPure_786_);
lean_dec_ref(v_toApplicative_775_);
v___x_787_ = lean_apply_2(v_toPure_786_, lean_box(0), v___x_781_);
return v___x_787_;
}
else
{
size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
lean_dec_ref(v_toApplicative_775_);
v___x_788_ = ((size_t)0ULL);
v___x_789_ = lean_usize_of_nat(v___x_780_);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_776_, v___f_777_, v_children_774_, v___x_788_, v___x_789_, v___x_781_);
return v___x_790_;
}
}
else
{
size_t v___x_791_; size_t v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v_toApplicative_775_);
v___x_791_ = ((size_t)0ULL);
v___x_792_ = lean_usize_of_nat(v___x_780_);
v___x_793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_776_, v___f_777_, v_children_774_, v___x_791_, v___x_792_, v___x_781_);
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object* v_inst_794_, lean_object* v_s_795_, lean_object* v_f_796_){
_start:
{
lean_object* v_toApplicative_797_; lean_object* v_toBind_798_; lean_object* v_element_799_; lean_object* v_children_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_toApplicative_797_ = lean_ctor_get(v_inst_794_, 0);
lean_inc_ref(v_toApplicative_797_);
v_toBind_798_ = lean_ctor_get(v_inst_794_, 1);
lean_inc(v_toBind_798_);
v_element_799_ = lean_ctor_get(v_s_795_, 0);
lean_inc_ref(v_element_799_);
v_children_800_ = lean_ctor_get(v_s_795_, 1);
lean_inc_ref(v_children_800_);
lean_dec_ref(v_s_795_);
lean_inc(v_f_796_);
lean_inc_ref(v_inst_794_);
v___f_801_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_801_, 0, v_inst_794_);
lean_closure_set(v___f_801_, 1, v_f_796_);
v___f_802_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_802_, 0, v_children_800_);
lean_closure_set(v___f_802_, 1, v_toApplicative_797_);
lean_closure_set(v___f_802_, 2, v_inst_794_);
lean_closure_set(v___f_802_, 3, v___f_801_);
v___x_803_ = lean_apply_1(v_f_796_, v_element_799_);
v___x_804_ = lean_apply_4(v_toBind_798_, lean_box(0), lean_box(0), v___x_803_, v___f_802_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object* v_inst_805_, lean_object* v_f_806_, lean_object* v_x_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = l_Lean_Language_SnapshotTask_get___redArg(v___y_808_);
v___x_810_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_805_, v___x_809_, v_f_806_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object* v_m_811_, lean_object* v_inst_812_, lean_object* v_s_813_, lean_object* v_f_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_812_, v_s_813_, v_f_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object* v_children_816_, lean_object* v_toApplicative_817_, lean_object* v_inst_818_, lean_object* v___f_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_array_get_size(v_children_816_);
v___x_823_ = lean_nat_dec_lt(v___x_821_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v_toPure_824_; lean_object* v___x_825_; 
lean_dec(v___f_819_);
lean_dec_ref(v_inst_818_);
lean_dec_ref(v_children_816_);
v_toPure_824_ = lean_ctor_get(v_toApplicative_817_, 1);
lean_inc(v_toPure_824_);
lean_dec_ref(v_toApplicative_817_);
v___x_825_ = lean_apply_2(v_toPure_824_, lean_box(0), v_a_820_);
return v___x_825_;
}
else
{
uint8_t v___x_826_; 
v___x_826_ = lean_nat_dec_le(v___x_822_, v___x_822_);
if (v___x_826_ == 0)
{
if (v___x_823_ == 0)
{
lean_object* v_toPure_827_; lean_object* v___x_828_; 
lean_dec(v___f_819_);
lean_dec_ref(v_inst_818_);
lean_dec_ref(v_children_816_);
v_toPure_827_ = lean_ctor_get(v_toApplicative_817_, 1);
lean_inc(v_toPure_827_);
lean_dec_ref(v_toApplicative_817_);
v___x_828_ = lean_apply_2(v_toPure_827_, lean_box(0), v_a_820_);
return v___x_828_;
}
else
{
size_t v___x_829_; size_t v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v_toApplicative_817_);
v___x_829_ = ((size_t)0ULL);
v___x_830_ = lean_usize_of_nat(v___x_822_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_818_, v___f_819_, v_children_816_, v___x_829_, v___x_830_, v_a_820_);
return v___x_831_;
}
}
else
{
size_t v___x_832_; size_t v___x_833_; lean_object* v___x_834_; 
lean_dec_ref(v_toApplicative_817_);
v___x_832_ = ((size_t)0ULL);
v___x_833_ = lean_usize_of_nat(v___x_822_);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_818_, v___f_819_, v_children_816_, v___x_832_, v___x_833_, v_a_820_);
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object* v_inst_835_, lean_object* v_s_836_, lean_object* v_f_837_, lean_object* v_init_838_){
_start:
{
lean_object* v_toApplicative_839_; lean_object* v_toBind_840_; lean_object* v_element_841_; lean_object* v_children_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_toApplicative_839_ = lean_ctor_get(v_inst_835_, 0);
lean_inc_ref(v_toApplicative_839_);
v_toBind_840_ = lean_ctor_get(v_inst_835_, 1);
lean_inc(v_toBind_840_);
v_element_841_ = lean_ctor_get(v_s_836_, 0);
lean_inc_ref(v_element_841_);
v_children_842_ = lean_ctor_get(v_s_836_, 1);
lean_inc_ref(v_children_842_);
lean_dec_ref(v_s_836_);
lean_inc(v_f_837_);
lean_inc_ref(v_inst_835_);
v___f_843_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_843_, 0, v_inst_835_);
lean_closure_set(v___f_843_, 1, v_f_837_);
v___f_844_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_844_, 0, v_children_842_);
lean_closure_set(v___f_844_, 1, v_toApplicative_839_);
lean_closure_set(v___f_844_, 2, v_inst_835_);
lean_closure_set(v___f_844_, 3, v___f_843_);
v___x_845_ = lean_apply_2(v_f_837_, v_init_838_, v_element_841_);
v___x_846_ = lean_apply_4(v_toBind_840_, lean_box(0), lean_box(0), v___x_845_, v___f_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object* v_inst_847_, lean_object* v_f_848_, lean_object* v_a_849_, lean_object* v_snap_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = l_Lean_Language_SnapshotTask_get___redArg(v_snap_850_);
v___x_852_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_847_, v___x_851_, v_f_848_, v_a_849_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object* v_m_853_, lean_object* v_00_u03b1_854_, lean_object* v_inst_855_, lean_object* v_s_856_, lean_object* v_f_857_, lean_object* v_init_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Language_SnapshotTree_foldM___redArg(v_inst_855_, v_s_856_, v_f_857_, v_init_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(lean_object* v_name_860_, lean_object* v_decl_861_, lean_object* v_ref_862_){
_start:
{
lean_object* v_defValue_864_; lean_object* v_descr_865_; lean_object* v_deprecation_x3f_866_; lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_defValue_864_ = lean_ctor_get(v_decl_861_, 0);
v_descr_865_ = lean_ctor_get(v_decl_861_, 1);
v_deprecation_x3f_866_ = lean_ctor_get(v_decl_861_, 2);
v___x_867_ = lean_alloc_ctor(1, 0, 1);
v___x_868_ = lean_unbox(v_defValue_864_);
lean_ctor_set_uint8(v___x_867_, 0, v___x_868_);
lean_inc(v_deprecation_x3f_866_);
lean_inc_ref(v_descr_865_);
lean_inc_n(v_name_860_, 2);
v___x_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_869_, 0, v_name_860_);
lean_ctor_set(v___x_869_, 1, v_ref_862_);
lean_ctor_set(v___x_869_, 2, v___x_867_);
lean_ctor_set(v___x_869_, 3, v_descr_865_);
lean_ctor_set(v___x_869_, 4, v_deprecation_x3f_866_);
v___x_870_ = lean_register_option(v_name_860_, v___x_869_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_878_; 
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; 
v_unused_879_ = lean_ctor_get(v___x_870_, 0);
lean_dec(v_unused_879_);
v___x_872_ = v___x_870_;
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
else
{
lean_dec(v___x_870_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
lean_inc(v_defValue_864_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_name_860_);
lean_ctor_set(v___x_874_, 1, v_defValue_864_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_874_);
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_name_860_);
v_a_880_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_870_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_870_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_888_, lean_object* v_decl_889_, lean_object* v_ref_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v_name_888_, v_decl_889_, v_ref_890_);
lean_dec_ref(v_decl_889_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_907_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_908_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_909_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_));
v___x_910_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v___x_907_, v___x_908_, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4____boxed(lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(lean_object* v_name_913_, lean_object* v_decl_914_, lean_object* v_ref_915_){
_start:
{
lean_object* v_defValue_917_; lean_object* v_descr_918_; lean_object* v_deprecation_x3f_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_defValue_917_ = lean_ctor_get(v_decl_914_, 0);
v_descr_918_ = lean_ctor_get(v_decl_914_, 1);
v_deprecation_x3f_919_ = lean_ctor_get(v_decl_914_, 2);
lean_inc(v_defValue_917_);
v___x_920_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_920_, 0, v_defValue_917_);
lean_inc(v_deprecation_x3f_919_);
lean_inc_ref(v_descr_918_);
lean_inc_n(v_name_913_, 2);
v___x_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_921_, 0, v_name_913_);
lean_ctor_set(v___x_921_, 1, v_ref_915_);
lean_ctor_set(v___x_921_, 2, v___x_920_);
lean_ctor_set(v___x_921_, 3, v_descr_918_);
lean_ctor_set(v___x_921_, 4, v_deprecation_x3f_919_);
v___x_922_ = lean_register_option(v_name_913_, v___x_921_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v___x_922_, 0);
lean_dec(v_unused_931_);
v___x_924_ = v___x_922_;
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
else
{
lean_dec(v___x_922_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
lean_inc(v_defValue_917_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_name_913_);
lean_ctor_set(v___x_926_, 1, v_defValue_917_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v_name_913_);
v_a_932_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_922_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_922_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_940_, lean_object* v_decl_941_, lean_object* v_ref_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v_name_940_, v_decl_941_, v_ref_942_);
lean_dec_ref(v_decl_941_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_958_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_959_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_960_ = ((lean_object*)(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_));
v___x_961_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v___x_958_, v___x_959_, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4____boxed(lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
return v_res_963_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(lean_object* v_opts_964_, lean_object* v_opt_965_){
_start:
{
lean_object* v_name_966_; lean_object* v_defValue_967_; lean_object* v_map_968_; lean_object* v___x_969_; 
v_name_966_ = lean_ctor_get(v_opt_965_, 0);
v_defValue_967_ = lean_ctor_get(v_opt_965_, 1);
v_map_968_ = lean_ctor_get(v_opts_964_, 0);
v___x_969_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_968_, v_name_966_);
if (lean_obj_tag(v___x_969_) == 0)
{
uint8_t v___x_970_; 
v___x_970_ = lean_unbox(v_defValue_967_);
return v___x_970_;
}
else
{
lean_object* v_val_971_; 
v_val_971_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_val_971_);
lean_dec_ref_known(v___x_969_, 1);
if (lean_obj_tag(v_val_971_) == 1)
{
uint8_t v_v_972_; 
v_v_972_ = lean_ctor_get_uint8(v_val_971_, 0);
lean_dec_ref_known(v_val_971_, 0);
return v_v_972_;
}
else
{
uint8_t v___x_973_; 
lean_dec(v_val_971_);
v___x_973_ = lean_unbox(v_defValue_967_);
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0___boxed(lean_object* v_opts_974_, lean_object* v_opt_975_){
_start:
{
uint8_t v_res_976_; lean_object* v_r_977_; 
v_res_976_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_974_, v_opt_975_);
lean_dec_ref(v_opt_975_);
lean_dec_ref(v_opts_974_);
v_r_977_ = lean_box(v_res_976_);
return v_r_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(lean_object* v_opts_978_, lean_object* v_opt_979_){
_start:
{
lean_object* v_name_980_; lean_object* v_defValue_981_; lean_object* v_map_982_; lean_object* v___x_983_; 
v_name_980_ = lean_ctor_get(v_opt_979_, 0);
v_defValue_981_ = lean_ctor_get(v_opt_979_, 1);
v_map_982_ = lean_ctor_get(v_opts_978_, 0);
v___x_983_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_982_, v_name_980_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_inc(v_defValue_981_);
return v_defValue_981_;
}
else
{
lean_object* v_val_984_; 
v_val_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_val_984_);
lean_dec_ref_known(v___x_983_, 1);
if (lean_obj_tag(v_val_984_) == 3)
{
lean_object* v_v_985_; 
v_v_985_ = lean_ctor_get(v_val_984_, 0);
lean_inc(v_v_985_);
lean_dec_ref_known(v_val_984_, 1);
return v_v_985_;
}
else
{
lean_dec(v_val_984_);
lean_inc(v_defValue_981_);
return v_defValue_981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1___boxed(lean_object* v_opts_986_, lean_object* v_opt_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_986_, v_opt_987_);
lean_dec_ref(v_opt_987_);
lean_dec_ref(v_opts_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(lean_object* v_s_989_){
_start:
{
lean_object* v___x_991_; lean_object* v_putStr_992_; lean_object* v___x_993_; 
v___x_991_ = lean_get_stdout();
v_putStr_992_ = lean_ctor_get(v___x_991_, 4);
lean_inc_ref(v_putStr_992_);
lean_dec_ref(v___x_991_);
v___x_993_ = lean_apply_2(v_putStr_992_, v_s_989_, lean_box(0));
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2___boxed(lean_object* v_s_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v_s_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object* v_s_997_){
_start:
{
uint32_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = 10;
v___x_1000_ = lean_string_push(v_s_997_, v___x_999_);
v___x_1001_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3___boxed(lean_object* v_s_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v_s_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(lean_object* v_opts_1007_, uint8_t v_json_1008_, uint8_t v_includeEndPos_1009_, lean_object* v_severityOverrides_1010_, lean_object* v_as_1011_, size_t v_i_1012_, size_t v_stop_1013_, lean_object* v_b_1014_){
_start:
{
lean_object* v_a_1017_; uint8_t v___y_1022_; lean_object* v___y_1023_; uint8_t v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; uint8_t v_isSilent_1038_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; uint8_t v___y_1064_; uint8_t v___x_1088_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1099_; uint8_t v_severity_1100_; 
v___x_1088_ = lean_usize_dec_eq(v_i_1012_, v_stop_1013_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1103_; lean_object* v_fileName_1104_; lean_object* v_pos_1105_; lean_object* v_endPos_1106_; uint8_t v_keepFullRange_1107_; uint8_t v_isSilent_1108_; lean_object* v_caption_1109_; lean_object* v_data_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1103_ = lean_array_uget(v_as_1011_, v_i_1012_);
v_fileName_1104_ = lean_ctor_get(v___x_1103_, 0);
v_pos_1105_ = lean_ctor_get(v___x_1103_, 1);
v_endPos_1106_ = lean_ctor_get(v___x_1103_, 2);
v_keepFullRange_1107_ = lean_ctor_get_uint8(v___x_1103_, sizeof(void*)*5);
v_isSilent_1108_ = lean_ctor_get_uint8(v___x_1103_, sizeof(void*)*5 + 2);
v_caption_1109_ = lean_ctor_get(v___x_1103_, 3);
v_data_1110_ = lean_ctor_get(v___x_1103_, 4);
v___x_1111_ = l_Lean_MessageData_kind(v_data_1110_);
v___x_1112_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_severityOverrides_1010_, v___x_1111_);
lean_dec(v___x_1111_);
if (lean_obj_tag(v___x_1112_) == 1)
{
lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1122_; 
lean_inc(v_data_1110_);
lean_inc_ref(v_caption_1109_);
lean_inc(v_endPos_1106_);
lean_inc_ref(v_pos_1105_);
lean_inc_ref(v_fileName_1104_);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; lean_object* v_unused_1124_; lean_object* v_unused_1125_; lean_object* v_unused_1126_; lean_object* v_unused_1127_; 
v_unused_1123_ = lean_ctor_get(v___x_1103_, 4);
lean_dec(v_unused_1123_);
v_unused_1124_ = lean_ctor_get(v___x_1103_, 3);
lean_dec(v_unused_1124_);
v_unused_1125_ = lean_ctor_get(v___x_1103_, 2);
lean_dec(v_unused_1125_);
v_unused_1126_ = lean_ctor_get(v___x_1103_, 1);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v___x_1103_, 0);
lean_dec(v_unused_1127_);
v___x_1114_ = v___x_1103_;
v_isShared_1115_ = v_isSharedCheck_1122_;
goto v_resetjp_1113_;
}
else
{
lean_dec(v___x_1103_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1122_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_val_1116_; lean_object* v___x_1118_; 
v_val_1116_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_val_1116_);
lean_dec_ref_known(v___x_1112_, 1);
if (v_isShared_1115_ == 0)
{
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_fileName_1104_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_pos_1105_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_endPos_1106_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_caption_1109_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_data_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1121_, sizeof(void*)*5, v_keepFullRange_1107_);
v___x_1118_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
uint8_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_unbox(v_val_1116_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*5 + 1, v___x_1119_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*5 + 2, v_isSilent_1108_);
v___x_1120_ = lean_unbox(v_val_1116_);
lean_dec(v_val_1116_);
v___y_1099_ = v___x_1118_;
v_severity_1100_ = v___x_1120_;
goto v___jp_1098_;
}
}
}
else
{
uint8_t v_severity_1128_; 
lean_dec(v___x_1112_);
v_severity_1128_ = lean_ctor_get_uint8(v___x_1103_, sizeof(void*)*5 + 1);
v___y_1099_ = v___x_1103_;
v_severity_1100_ = v_severity_1128_;
goto v___jp_1098_;
}
}
else
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_b_1014_);
return v___x_1129_;
}
v___jp_1016_:
{
size_t v___x_1018_; size_t v___x_1019_; 
v___x_1018_ = ((size_t)1ULL);
v___x_1019_ = lean_usize_add(v_i_1012_, v___x_1018_);
v_i_1012_ = v___x_1019_;
v_b_1014_ = v_a_1017_;
goto _start;
}
v___jp_1021_:
{
if (v___y_1022_ == 0)
{
v_a_1017_ = v___y_1023_;
goto v___jp_1016_;
}
else
{
uint8_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = 1;
v___x_1025_ = lean_io_exit(v___x_1024_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_dec_ref_known(v___x_1025_, 1);
v_a_1017_ = v___y_1023_;
goto v___jp_1016_;
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v___y_1023_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
v___jp_1034_:
{
if (v_isSilent_1038_ == 0)
{
if (v_json_1008_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = l_Lean_Message_toString(v___y_1037_, v_includeEndPos_1009_);
v___x_1040_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_1039_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_dec_ref_known(v___x_1040_, 1);
v___y_1022_ = v___y_1035_;
v___y_1023_ = v___y_1036_;
goto v___jp_1021_;
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v___y_1036_);
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = l_Lean_Message_toJson(v___y_1037_);
v___x_1050_ = l_Lean_Json_compress(v___x_1049_);
v___x_1051_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_1050_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_dec_ref_known(v___x_1051_, 1);
v___y_1022_ = v___y_1035_;
v___y_1023_ = v___y_1036_;
goto v___jp_1021_;
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec(v___y_1036_);
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1037_);
v___y_1022_ = v___y_1035_;
v___y_1023_ = v___y_1036_;
goto v___jp_1021_;
}
}
v___jp_1060_:
{
if (v___y_1064_ == 0)
{
uint8_t v_isSilent_1065_; 
lean_dec(v___y_1062_);
v_isSilent_1065_ = lean_ctor_get_uint8(v___y_1061_, sizeof(void*)*5 + 2);
v___y_1035_ = v___y_1064_;
v___y_1036_ = v___y_1063_;
v___y_1037_ = v___y_1061_;
v_isSilent_1038_ = v_isSilent_1065_;
goto v___jp_1034_;
}
else
{
lean_object* v_fileName_1066_; lean_object* v_pos_1067_; lean_object* v_endPos_1068_; uint8_t v_keepFullRange_1069_; uint8_t v_isSilent_1070_; lean_object* v_caption_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1086_; 
v_fileName_1066_ = lean_ctor_get(v___y_1061_, 0);
v_pos_1067_ = lean_ctor_get(v___y_1061_, 1);
v_endPos_1068_ = lean_ctor_get(v___y_1061_, 2);
v_keepFullRange_1069_ = lean_ctor_get_uint8(v___y_1061_, sizeof(void*)*5);
v_isSilent_1070_ = lean_ctor_get_uint8(v___y_1061_, sizeof(void*)*5 + 2);
v_caption_1071_ = lean_ctor_get(v___y_1061_, 3);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___y_1061_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v___y_1061_, 4);
lean_dec(v_unused_1087_);
v___x_1073_ = v___y_1061_;
v_isShared_1074_ = v_isSharedCheck_1086_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_caption_1071_);
lean_inc(v_endPos_1068_);
lean_inc(v_pos_1067_);
lean_inc(v_fileName_1066_);
lean_dec(v___y_1061_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1086_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1075_ = 2;
v___x_1076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0));
v___x_1077_ = l_Nat_reprFast(v___y_1062_);
v___x_1078_ = lean_string_append(v___x_1076_, v___x_1077_);
lean_dec_ref(v___x_1077_);
v___x_1079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1));
v___x_1080_ = lean_string_append(v___x_1078_, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
v___x_1082_ = l_Lean_MessageData_ofFormat(v___x_1081_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 4, v___x_1082_);
v___x_1084_ = v___x_1073_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_fileName_1066_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_pos_1067_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_endPos_1068_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_caption_1071_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v___x_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*5, v_keepFullRange_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*5 + 2, v_isSilent_1070_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*5 + 1, v___x_1075_);
v___y_1035_ = v___y_1064_;
v___y_1036_ = v___y_1063_;
v___y_1037_ = v___x_1084_;
v_isSilent_1038_ = v_isSilent_1070_;
goto v___jp_1034_;
}
}
}
}
v___jp_1089_:
{
lean_object* v_numErrors_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_numErrors_1092_ = lean_nat_add(v_b_1014_, v___y_1091_);
lean_dec(v_b_1014_);
v___x_1093_ = l_Lean_Language_maxErrors;
v___x_1094_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_1007_, v___x_1093_);
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = lean_nat_dec_eq(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_nat_dec_lt(v___x_1094_, v_numErrors_1092_);
if (v___x_1097_ == 0)
{
v___y_1061_ = v___y_1090_;
v___y_1062_ = v___x_1094_;
v___y_1063_ = v_numErrors_1092_;
v___y_1064_ = v___x_1088_;
goto v___jp_1060_;
}
else
{
v___y_1061_ = v___y_1090_;
v___y_1062_ = v___x_1094_;
v___y_1063_ = v_numErrors_1092_;
v___y_1064_ = v___x_1097_;
goto v___jp_1060_;
}
}
else
{
v___y_1061_ = v___y_1090_;
v___y_1062_ = v___x_1094_;
v___y_1063_ = v_numErrors_1092_;
v___y_1064_ = v___x_1088_;
goto v___jp_1060_;
}
}
v___jp_1098_:
{
if (v_severity_1100_ == 2)
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_unsigned_to_nat(1u);
v___y_1090_ = v___y_1099_;
v___y_1091_ = v___x_1101_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_unsigned_to_nat(0u);
v___y_1090_ = v___y_1099_;
v___y_1091_ = v___x_1102_;
goto v___jp_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___boxed(lean_object* v_opts_1130_, lean_object* v_json_1131_, lean_object* v_includeEndPos_1132_, lean_object* v_severityOverrides_1133_, lean_object* v_as_1134_, lean_object* v_i_1135_, lean_object* v_stop_1136_, lean_object* v_b_1137_, lean_object* v___y_1138_){
_start:
{
uint8_t v_json_boxed_1139_; uint8_t v_includeEndPos_boxed_1140_; size_t v_i_boxed_1141_; size_t v_stop_boxed_1142_; lean_object* v_res_1143_; 
v_json_boxed_1139_ = lean_unbox(v_json_1131_);
v_includeEndPos_boxed_1140_ = lean_unbox(v_includeEndPos_1132_);
v_i_boxed_1141_ = lean_unbox_usize(v_i_1135_);
lean_dec(v_i_1135_);
v_stop_boxed_1142_ = lean_unbox_usize(v_stop_1136_);
lean_dec(v_stop_1136_);
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1130_, v_json_boxed_1139_, v_includeEndPos_boxed_1140_, v_severityOverrides_1133_, v_as_1134_, v_i_boxed_1141_, v_stop_boxed_1142_, v_b_1137_);
lean_dec_ref(v_as_1134_);
lean_dec(v_severityOverrides_1133_);
lean_dec_ref(v_opts_1130_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(lean_object* v_opts_1144_, uint8_t v_json_1145_, uint8_t v_includeEndPos_1146_, lean_object* v_severityOverrides_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
if (lean_obj_tag(v_x_1148_) == 0)
{
lean_object* v_cs_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1171_; 
v_cs_1151_ = lean_ctor_get(v_x_1148_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1153_ = v_x_1148_;
v_isShared_1154_ = v_isSharedCheck_1171_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_cs_1151_);
lean_dec(v_x_1148_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1171_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_array_get_size(v_cs_1151_);
v___x_1157_ = lean_nat_dec_lt(v___x_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1159_; 
lean_dec_ref(v_cs_1151_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v_x_1149_);
v___x_1159_ = v___x_1153_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_x_1149_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_nat_dec_le(v___x_1156_, v___x_1156_);
if (v___x_1161_ == 0)
{
if (v___x_1157_ == 0)
{
lean_object* v___x_1163_; 
lean_dec_ref(v_cs_1151_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v_x_1149_);
v___x_1163_ = v___x_1153_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_x_1149_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
else
{
size_t v___x_1165_; size_t v___x_1166_; lean_object* v___x_1167_; 
lean_del_object(v___x_1153_);
v___x_1165_ = ((size_t)0ULL);
v___x_1166_ = lean_usize_of_nat(v___x_1156_);
v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1144_, v_json_1145_, v_includeEndPos_1146_, v_severityOverrides_1147_, v_cs_1151_, v___x_1165_, v___x_1166_, v_x_1149_);
lean_dec_ref(v_cs_1151_);
return v___x_1167_;
}
}
else
{
size_t v___x_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
lean_del_object(v___x_1153_);
v___x_1168_ = ((size_t)0ULL);
v___x_1169_ = lean_usize_of_nat(v___x_1156_);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1144_, v_json_1145_, v_includeEndPos_1146_, v_severityOverrides_1147_, v_cs_1151_, v___x_1168_, v___x_1169_, v_x_1149_);
lean_dec_ref(v_cs_1151_);
return v___x_1170_;
}
}
}
}
else
{
lean_object* v_vs_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1192_; 
v_vs_1172_ = lean_ctor_get(v_x_1148_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1174_ = v_x_1148_;
v_isShared_1175_ = v_isSharedCheck_1192_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_vs_1172_);
lean_dec(v_x_1148_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1192_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1176_ = lean_unsigned_to_nat(0u);
v___x_1177_ = lean_array_get_size(v_vs_1172_);
v___x_1178_ = lean_nat_dec_lt(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1180_; 
lean_dec_ref(v_vs_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set_tag(v___x_1174_, 0);
lean_ctor_set(v___x_1174_, 0, v_x_1149_);
v___x_1180_ = v___x_1174_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_x_1149_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
else
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_nat_dec_le(v___x_1177_, v___x_1177_);
if (v___x_1182_ == 0)
{
if (v___x_1178_ == 0)
{
lean_object* v___x_1184_; 
lean_dec_ref(v_vs_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set_tag(v___x_1174_, 0);
lean_ctor_set(v___x_1174_, 0, v_x_1149_);
v___x_1184_ = v___x_1174_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_x_1149_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
else
{
size_t v___x_1186_; size_t v___x_1187_; lean_object* v___x_1188_; 
lean_del_object(v___x_1174_);
v___x_1186_ = ((size_t)0ULL);
v___x_1187_ = lean_usize_of_nat(v___x_1177_);
v___x_1188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1144_, v_json_1145_, v_includeEndPos_1146_, v_severityOverrides_1147_, v_vs_1172_, v___x_1186_, v___x_1187_, v_x_1149_);
lean_dec_ref(v_vs_1172_);
return v___x_1188_;
}
}
else
{
size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
lean_del_object(v___x_1174_);
v___x_1189_ = ((size_t)0ULL);
v___x_1190_ = lean_usize_of_nat(v___x_1177_);
v___x_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1144_, v_json_1145_, v_includeEndPos_1146_, v_severityOverrides_1147_, v_vs_1172_, v___x_1189_, v___x_1190_, v_x_1149_);
lean_dec_ref(v_vs_1172_);
return v___x_1191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(lean_object* v_opts_1193_, uint8_t v_json_1194_, uint8_t v_includeEndPos_1195_, lean_object* v_severityOverrides_1196_, lean_object* v_as_1197_, size_t v_i_1198_, size_t v_stop_1199_, lean_object* v_b_1200_){
_start:
{
uint8_t v___x_1202_; 
v___x_1202_ = lean_usize_dec_eq(v_i_1198_, v_stop_1199_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_array_uget_borrowed(v_as_1197_, v_i_1198_);
lean_inc(v___x_1203_);
v___x_1204_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1193_, v_json_1194_, v_includeEndPos_1195_, v_severityOverrides_1196_, v___x_1203_, v_b_1200_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; size_t v___x_1206_; size_t v___x_1207_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v___x_1206_ = ((size_t)1ULL);
v___x_1207_ = lean_usize_add(v_i_1198_, v___x_1206_);
v_i_1198_ = v___x_1207_;
v_b_1200_ = v_a_1205_;
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
lean_ctor_set(v___x_1209_, 0, v_b_1200_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5___boxed(lean_object* v_opts_1210_, lean_object* v_json_1211_, lean_object* v_includeEndPos_1212_, lean_object* v_severityOverrides_1213_, lean_object* v_as_1214_, lean_object* v_i_1215_, lean_object* v_stop_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v_json_boxed_1219_; uint8_t v_includeEndPos_boxed_1220_; size_t v_i_boxed_1221_; size_t v_stop_boxed_1222_; lean_object* v_res_1223_; 
v_json_boxed_1219_ = lean_unbox(v_json_1211_);
v_includeEndPos_boxed_1220_ = lean_unbox(v_includeEndPos_1212_);
v_i_boxed_1221_ = lean_unbox_usize(v_i_1215_);
lean_dec(v_i_1215_);
v_stop_boxed_1222_ = lean_unbox_usize(v_stop_1216_);
lean_dec(v_stop_1216_);
v_res_1223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1210_, v_json_boxed_1219_, v_includeEndPos_boxed_1220_, v_severityOverrides_1213_, v_as_1214_, v_i_boxed_1221_, v_stop_boxed_1222_, v_b_1217_);
lean_dec_ref(v_as_1214_);
lean_dec(v_severityOverrides_1213_);
lean_dec_ref(v_opts_1210_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6___boxed(lean_object* v_opts_1224_, lean_object* v_json_1225_, lean_object* v_includeEndPos_1226_, lean_object* v_severityOverrides_1227_, lean_object* v_x_1228_, lean_object* v_x_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v_json_boxed_1231_; uint8_t v_includeEndPos_boxed_1232_; lean_object* v_res_1233_; 
v_json_boxed_1231_ = lean_unbox(v_json_1225_);
v_includeEndPos_boxed_1232_ = lean_unbox(v_includeEndPos_1226_);
v_res_1233_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1224_, v_json_boxed_1231_, v_includeEndPos_boxed_1232_, v_severityOverrides_1227_, v_x_1228_, v_x_1229_);
lean_dec(v_severityOverrides_1227_);
lean_dec_ref(v_opts_1224_);
return v_res_1233_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(lean_object* v_opts_1235_, uint8_t v_json_1236_, uint8_t v_includeEndPos_1237_, lean_object* v_severityOverrides_1238_, lean_object* v_x_1239_, size_t v_x_1240_, size_t v_x_1241_, lean_object* v_x_1242_){
_start:
{
if (lean_obj_tag(v_x_1239_) == 0)
{
lean_object* v_cs_1244_; lean_object* v___x_1245_; size_t v___x_1246_; lean_object* v_j_1247_; lean_object* v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; size_t v___x_1254_; lean_object* v___x_1255_; 
v_cs_1244_ = lean_ctor_get(v_x_1239_, 0);
lean_inc_ref(v_cs_1244_);
lean_dec_ref_known(v_x_1239_, 1);
v___x_1245_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0);
v___x_1246_ = lean_usize_shift_right(v_x_1240_, v_x_1241_);
v_j_1247_ = lean_usize_to_nat(v___x_1246_);
v___x_1248_ = lean_array_get_borrowed(v___x_1245_, v_cs_1244_, v_j_1247_);
v___x_1249_ = ((size_t)1ULL);
v___x_1250_ = lean_usize_shift_left(v___x_1249_, v_x_1241_);
v___x_1251_ = lean_usize_sub(v___x_1250_, v___x_1249_);
v___x_1252_ = lean_usize_land(v_x_1240_, v___x_1251_);
v___x_1253_ = ((size_t)5ULL);
v___x_1254_ = lean_usize_sub(v_x_1241_, v___x_1253_);
lean_inc(v___x_1248_);
v___x_1255_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1235_, v_json_1236_, v_includeEndPos_1237_, v_severityOverrides_1238_, v___x_1248_, v___x_1252_, v___x_1254_, v_x_1242_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_add(v_j_1247_, v___x_1257_);
lean_dec(v_j_1247_);
v___x_1259_ = lean_array_get_size(v_cs_1244_);
v___x_1260_ = lean_nat_dec_lt(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_dec(v___x_1258_);
lean_dec(v_a_1256_);
lean_dec_ref(v_cs_1244_);
return v___x_1255_;
}
else
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_nat_dec_le(v___x_1259_, v___x_1259_);
if (v___x_1261_ == 0)
{
if (v___x_1260_ == 0)
{
lean_dec(v___x_1258_);
lean_dec(v_a_1256_);
lean_dec_ref(v_cs_1244_);
return v___x_1255_;
}
else
{
size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref_known(v___x_1255_, 1);
v___x_1262_ = lean_usize_of_nat(v___x_1258_);
lean_dec(v___x_1258_);
v___x_1263_ = lean_usize_of_nat(v___x_1259_);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1235_, v_json_1236_, v_includeEndPos_1237_, v_severityOverrides_1238_, v_cs_1244_, v___x_1262_, v___x_1263_, v_a_1256_);
lean_dec_ref(v_cs_1244_);
return v___x_1264_;
}
}
else
{
size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
lean_dec_ref_known(v___x_1255_, 1);
v___x_1265_ = lean_usize_of_nat(v___x_1258_);
lean_dec(v___x_1258_);
v___x_1266_ = lean_usize_of_nat(v___x_1259_);
v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_1235_, v_json_1236_, v_includeEndPos_1237_, v_severityOverrides_1238_, v_cs_1244_, v___x_1265_, v___x_1266_, v_a_1256_);
lean_dec_ref(v_cs_1244_);
return v___x_1267_;
}
}
}
else
{
lean_dec(v_j_1247_);
lean_dec_ref(v_cs_1244_);
return v___x_1255_;
}
}
else
{
lean_object* v_vs_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1288_; 
v_vs_1268_ = lean_ctor_get(v_x_1239_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_x_1239_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1270_ = v_x_1239_;
v_isShared_1271_ = v_isSharedCheck_1288_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_vs_1268_);
lean_dec(v_x_1239_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1288_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = lean_usize_to_nat(v_x_1240_);
v___x_1273_ = lean_array_get_size(v_vs_1268_);
v___x_1274_ = lean_nat_dec_lt(v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1276_; 
lean_dec(v___x_1272_);
lean_dec_ref(v_vs_1268_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 0);
lean_ctor_set(v___x_1270_, 0, v_x_1242_);
v___x_1276_ = v___x_1270_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_x_1242_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
else
{
uint8_t v___x_1278_; 
v___x_1278_ = lean_nat_dec_le(v___x_1273_, v___x_1273_);
if (v___x_1278_ == 0)
{
if (v___x_1274_ == 0)
{
lean_object* v___x_1280_; 
lean_dec(v___x_1272_);
lean_dec_ref(v_vs_1268_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 0);
lean_ctor_set(v___x_1270_, 0, v_x_1242_);
v___x_1280_ = v___x_1270_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_x_1242_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
else
{
size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
lean_del_object(v___x_1270_);
v___x_1282_ = lean_usize_of_nat(v___x_1272_);
lean_dec(v___x_1272_);
v___x_1283_ = lean_usize_of_nat(v___x_1273_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1235_, v_json_1236_, v_includeEndPos_1237_, v_severityOverrides_1238_, v_vs_1268_, v___x_1282_, v___x_1283_, v_x_1242_);
lean_dec_ref(v_vs_1268_);
return v___x_1284_;
}
}
else
{
size_t v___x_1285_; size_t v___x_1286_; lean_object* v___x_1287_; 
lean_del_object(v___x_1270_);
v___x_1285_ = lean_usize_of_nat(v___x_1272_);
lean_dec(v___x_1272_);
v___x_1286_ = lean_usize_of_nat(v___x_1273_);
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1235_, v_json_1236_, v_includeEndPos_1237_, v_severityOverrides_1238_, v_vs_1268_, v___x_1285_, v___x_1286_, v_x_1242_);
lean_dec_ref(v_vs_1268_);
return v___x_1287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___boxed(lean_object* v_opts_1289_, lean_object* v_json_1290_, lean_object* v_includeEndPos_1291_, lean_object* v_severityOverrides_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_){
_start:
{
uint8_t v_json_boxed_1298_; uint8_t v_includeEndPos_boxed_1299_; size_t v_x_2643__boxed_1300_; size_t v_x_2644__boxed_1301_; lean_object* v_res_1302_; 
v_json_boxed_1298_ = lean_unbox(v_json_1290_);
v_includeEndPos_boxed_1299_ = lean_unbox(v_includeEndPos_1291_);
v_x_2643__boxed_1300_ = lean_unbox_usize(v_x_1294_);
lean_dec(v_x_1294_);
v_x_2644__boxed_1301_ = lean_unbox_usize(v_x_1295_);
lean_dec(v_x_1295_);
v_res_1302_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1289_, v_json_boxed_1298_, v_includeEndPos_boxed_1299_, v_severityOverrides_1292_, v_x_1293_, v_x_2643__boxed_1300_, v_x_2644__boxed_1301_, v_x_1296_);
lean_dec(v_severityOverrides_1292_);
lean_dec_ref(v_opts_1289_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(lean_object* v_opts_1303_, uint8_t v_json_1304_, uint8_t v_includeEndPos_1305_, lean_object* v_severityOverrides_1306_, lean_object* v_t_1307_, lean_object* v_init_1308_, lean_object* v_start_1309_){
_start:
{
lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_nat_dec_eq(v_start_1309_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v_root_1313_; lean_object* v_tail_1314_; size_t v_shift_1315_; lean_object* v_tailOff_1316_; uint8_t v___x_1317_; 
v_root_1313_ = lean_ctor_get(v_t_1307_, 0);
lean_inc_ref(v_root_1313_);
v_tail_1314_ = lean_ctor_get(v_t_1307_, 1);
lean_inc_ref(v_tail_1314_);
v_shift_1315_ = lean_ctor_get_usize(v_t_1307_, 4);
v_tailOff_1316_ = lean_ctor_get(v_t_1307_, 3);
lean_inc(v_tailOff_1316_);
lean_dec_ref(v_t_1307_);
v___x_1317_ = lean_nat_dec_le(v_tailOff_1316_, v_start_1309_);
if (v___x_1317_ == 0)
{
size_t v___x_1318_; lean_object* v___x_1319_; 
lean_dec(v_tailOff_1316_);
v___x_1318_ = lean_usize_of_nat(v_start_1309_);
v___x_1319_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_1303_, v_json_1304_, v_includeEndPos_1305_, v_severityOverrides_1306_, v_root_1313_, v___x_1318_, v_shift_1315_, v_init_1308_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
v___x_1321_ = lean_array_get_size(v_tail_1314_);
v___x_1322_ = lean_nat_dec_lt(v___x_1311_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec(v_a_1320_);
lean_dec_ref(v_tail_1314_);
return v___x_1319_;
}
else
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_nat_dec_le(v___x_1321_, v___x_1321_);
if (v___x_1323_ == 0)
{
if (v___x_1322_ == 0)
{
lean_dec(v_a_1320_);
lean_dec_ref(v_tail_1314_);
return v___x_1319_;
}
else
{
size_t v___x_1324_; size_t v___x_1325_; lean_object* v___x_1326_; 
lean_dec_ref_known(v___x_1319_, 1);
v___x_1324_ = ((size_t)0ULL);
v___x_1325_ = lean_usize_of_nat(v___x_1321_);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1303_, v_json_1304_, v_includeEndPos_1305_, v_severityOverrides_1306_, v_tail_1314_, v___x_1324_, v___x_1325_, v_a_1320_);
lean_dec_ref(v_tail_1314_);
return v___x_1326_;
}
}
else
{
size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref_known(v___x_1319_, 1);
v___x_1327_ = ((size_t)0ULL);
v___x_1328_ = lean_usize_of_nat(v___x_1321_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1303_, v_json_1304_, v_includeEndPos_1305_, v_severityOverrides_1306_, v_tail_1314_, v___x_1327_, v___x_1328_, v_a_1320_);
lean_dec_ref(v_tail_1314_);
return v___x_1329_;
}
}
}
else
{
lean_dec_ref(v_tail_1314_);
return v___x_1319_;
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
lean_dec_ref(v_root_1313_);
v___x_1330_ = lean_nat_sub(v_start_1309_, v_tailOff_1316_);
lean_dec(v_tailOff_1316_);
v___x_1331_ = lean_array_get_size(v_tail_1314_);
v___x_1332_ = lean_nat_dec_lt(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_dec(v___x_1330_);
lean_dec_ref(v_tail_1314_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v_init_1308_);
return v___x_1333_;
}
else
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_nat_dec_le(v___x_1331_, v___x_1331_);
if (v___x_1334_ == 0)
{
if (v___x_1332_ == 0)
{
lean_object* v___x_1335_; 
lean_dec(v___x_1330_);
lean_dec_ref(v_tail_1314_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_init_1308_);
return v___x_1335_;
}
else
{
size_t v___x_1336_; size_t v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_usize_of_nat(v___x_1330_);
lean_dec(v___x_1330_);
v___x_1337_ = lean_usize_of_nat(v___x_1331_);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1303_, v_json_1304_, v_includeEndPos_1305_, v_severityOverrides_1306_, v_tail_1314_, v___x_1336_, v___x_1337_, v_init_1308_);
lean_dec_ref(v_tail_1314_);
return v___x_1338_;
}
}
else
{
size_t v___x_1339_; size_t v___x_1340_; lean_object* v___x_1341_; 
v___x_1339_ = lean_usize_of_nat(v___x_1330_);
lean_dec(v___x_1330_);
v___x_1340_ = lean_usize_of_nat(v___x_1331_);
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1303_, v_json_1304_, v_includeEndPos_1305_, v_severityOverrides_1306_, v_tail_1314_, v___x_1339_, v___x_1340_, v_init_1308_);
lean_dec_ref(v_tail_1314_);
return v___x_1341_;
}
}
}
}
else
{
lean_object* v_root_1342_; lean_object* v_tail_1343_; lean_object* v___x_1344_; 
v_root_1342_ = lean_ctor_get(v_t_1307_, 0);
lean_inc_ref(v_root_1342_);
v_tail_1343_ = lean_ctor_get(v_t_1307_, 1);
lean_inc_ref(v_tail_1343_);
lean_dec_ref(v_t_1307_);
v___x_1344_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_1303_, v_json_1304_, v_includeEndPos_1305_, v_severityOverrides_1306_, v_root_1342_, v_init_1308_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
v___x_1346_ = lean_array_get_size(v_tail_1343_);
v___x_1347_ = lean_nat_dec_lt(v___x_1311_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_dec(v_a_1345_);
lean_dec_ref(v_tail_1343_);
return v___x_1344_;
}
else
{
uint8_t v___x_1348_; 
v___x_1348_ = lean_nat_dec_le(v___x_1346_, v___x_1346_);
if (v___x_1348_ == 0)
{
if (v___x_1347_ == 0)
{
lean_dec(v_a_1345_);
lean_dec_ref(v_tail_1343_);
return v___x_1344_;
}
else
{
size_t v___x_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
lean_dec_ref_known(v___x_1344_, 1);
v___x_1349_ = ((size_t)0ULL);
v___x_1350_ = lean_usize_of_nat(v___x_1346_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1303_, v_json_1304_, v_includeEndPos_1305_, v_severityOverrides_1306_, v_tail_1343_, v___x_1349_, v___x_1350_, v_a_1345_);
lean_dec_ref(v_tail_1343_);
return v___x_1351_;
}
}
else
{
size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
lean_dec_ref_known(v___x_1344_, 1);
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = lean_usize_of_nat(v___x_1346_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_1303_, v_json_1304_, v_includeEndPos_1305_, v_severityOverrides_1306_, v_tail_1343_, v___x_1352_, v___x_1353_, v_a_1345_);
lean_dec_ref(v_tail_1343_);
return v___x_1354_;
}
}
}
else
{
lean_dec_ref(v_tail_1343_);
return v___x_1344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4___boxed(lean_object* v_opts_1355_, lean_object* v_json_1356_, lean_object* v_includeEndPos_1357_, lean_object* v_severityOverrides_1358_, lean_object* v_t_1359_, lean_object* v_init_1360_, lean_object* v_start_1361_, lean_object* v___y_1362_){
_start:
{
uint8_t v_json_boxed_1363_; uint8_t v_includeEndPos_boxed_1364_; lean_object* v_res_1365_; 
v_json_boxed_1363_ = lean_unbox(v_json_1356_);
v_includeEndPos_boxed_1364_ = lean_unbox(v_includeEndPos_1357_);
v_res_1365_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1355_, v_json_boxed_1363_, v_includeEndPos_boxed_1364_, v_severityOverrides_1358_, v_t_1359_, v_init_1360_, v_start_1361_);
lean_dec(v_start_1361_);
lean_dec(v_severityOverrides_1358_);
lean_dec_ref(v_opts_1355_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(lean_object* v_msgLog_1366_, lean_object* v_opts_1367_, uint8_t v_json_1368_, lean_object* v_severityOverrides_1369_, lean_object* v_numErrors_1370_){
_start:
{
lean_object* v_unreported_1372_; lean_object* v___x_1373_; uint8_t v_includeEndPos_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_unreported_1372_ = lean_ctor_get(v_msgLog_1366_, 1);
lean_inc_ref(v_unreported_1372_);
lean_dec_ref(v_msgLog_1366_);
v___x_1373_ = l_Lean_Language_printMessageEndPos;
v_includeEndPos_1374_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_1367_, v___x_1373_);
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_1367_, v_json_1368_, v_includeEndPos_1374_, v_severityOverrides_1369_, v_unreported_1372_, v_numErrors_1370_, v___x_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___boxed(lean_object* v_msgLog_1377_, lean_object* v_opts_1378_, lean_object* v_json_1379_, lean_object* v_severityOverrides_1380_, lean_object* v_numErrors_1381_, lean_object* v_a_1382_){
_start:
{
uint8_t v_json_boxed_1383_; lean_object* v_res_1384_; 
v_json_boxed_1383_ = lean_unbox(v_json_1379_);
v_res_1384_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1377_, v_opts_1378_, v_json_boxed_1383_, v_severityOverrides_1380_, v_numErrors_1381_);
lean_dec(v_severityOverrides_1380_);
lean_dec_ref(v_opts_1378_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object* v_opts_1385_, uint8_t v_json_1386_, lean_object* v_severityOverrides_1387_, lean_object* v_s_1388_, lean_object* v_init_1389_){
_start:
{
lean_object* v_element_1391_; lean_object* v_diagnostics_1392_; lean_object* v_children_1393_; lean_object* v_msgLog_1394_; lean_object* v___x_1395_; 
v_element_1391_ = lean_ctor_get(v_s_1388_, 0);
v_diagnostics_1392_ = lean_ctor_get(v_element_1391_, 1);
lean_inc_ref(v_diagnostics_1392_);
v_children_1393_ = lean_ctor_get(v_s_1388_, 1);
lean_inc_ref(v_children_1393_);
lean_dec_ref(v_s_1388_);
v_msgLog_1394_ = lean_ctor_get(v_diagnostics_1392_, 0);
lean_inc_ref(v_msgLog_1394_);
lean_dec_ref(v_diagnostics_1392_);
v___x_1395_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(v_msgLog_1394_, v_opts_1385_, v_json_1386_, v_severityOverrides_1387_, v_init_1389_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_array_get_size(v_children_1393_);
v___x_1399_ = lean_nat_dec_lt(v___x_1397_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_dec(v_a_1396_);
lean_dec_ref(v_children_1393_);
return v___x_1395_;
}
else
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_nat_dec_le(v___x_1398_, v___x_1398_);
if (v___x_1400_ == 0)
{
if (v___x_1399_ == 0)
{
lean_dec(v_a_1396_);
lean_dec_ref(v_children_1393_);
return v___x_1395_;
}
else
{
size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
lean_dec_ref_known(v___x_1395_, 1);
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = lean_usize_of_nat(v___x_1398_);
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1385_, v_json_1386_, v_severityOverrides_1387_, v_children_1393_, v___x_1401_, v___x_1402_, v_a_1396_);
lean_dec_ref(v_children_1393_);
return v___x_1403_;
}
}
else
{
size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
lean_dec_ref_known(v___x_1395_, 1);
v___x_1404_ = ((size_t)0ULL);
v___x_1405_ = lean_usize_of_nat(v___x_1398_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1385_, v_json_1386_, v_severityOverrides_1387_, v_children_1393_, v___x_1404_, v___x_1405_, v_a_1396_);
lean_dec_ref(v_children_1393_);
return v___x_1406_;
}
}
}
else
{
lean_dec_ref(v_children_1393_);
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object* v_opts_1407_, uint8_t v_json_1408_, lean_object* v_severityOverrides_1409_, lean_object* v_as_1410_, size_t v_i_1411_, size_t v_stop_1412_, lean_object* v_b_1413_){
_start:
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_usize_dec_eq(v_i_1411_, v_stop_1412_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = lean_array_uget_borrowed(v_as_1410_, v_i_1411_);
lean_inc(v___x_1416_);
v___x_1417_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1416_);
v___x_1418_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1407_, v_json_1408_, v_severityOverrides_1409_, v___x_1417_, v_b_1413_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; size_t v___x_1420_; size_t v___x_1421_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_add(v_i_1411_, v___x_1420_);
v_i_1411_ = v___x_1421_;
v_b_1413_ = v_a_1419_;
goto _start;
}
else
{
return v___x_1418_;
}
}
else
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_b_1413_);
return v___x_1423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object* v_opts_1424_, lean_object* v_json_1425_, lean_object* v_severityOverrides_1426_, lean_object* v_as_1427_, lean_object* v_i_1428_, lean_object* v_stop_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v_json_boxed_1432_; size_t v_i_boxed_1433_; size_t v_stop_boxed_1434_; lean_object* v_res_1435_; 
v_json_boxed_1432_ = lean_unbox(v_json_1425_);
v_i_boxed_1433_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_stop_boxed_1434_ = lean_unbox_usize(v_stop_1429_);
lean_dec(v_stop_1429_);
v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_1424_, v_json_boxed_1432_, v_severityOverrides_1426_, v_as_1427_, v_i_boxed_1433_, v_stop_boxed_1434_, v_b_1430_);
lean_dec_ref(v_as_1427_);
lean_dec(v_severityOverrides_1426_);
lean_dec_ref(v_opts_1424_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object* v_opts_1436_, lean_object* v_json_1437_, lean_object* v_severityOverrides_1438_, lean_object* v_s_1439_, lean_object* v_init_1440_, lean_object* v___y_1441_){
_start:
{
uint8_t v_json_boxed_1442_; lean_object* v_res_1443_; 
v_json_boxed_1442_ = lean_unbox(v_json_1437_);
v_res_1443_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1436_, v_json_boxed_1442_, v_severityOverrides_1438_, v_s_1439_, v_init_1440_);
lean_dec(v_severityOverrides_1438_);
lean_dec_ref(v_opts_1436_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object* v_s_1444_, lean_object* v_opts_1445_, uint8_t v_json_1446_, lean_object* v_severityOverrides_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_1445_, v_json_1446_, v_severityOverrides_1447_, v_s_1444_, v___x_1449_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1460_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
uint8_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1455_ = lean_nat_dec_lt(v___x_1449_, v_a_1451_);
lean_dec(v_a_1451_);
v___x_1456_ = lean_box(v___x_1455_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1456_);
v___x_1458_ = v___x_1453_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_a_1461_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1450_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1450_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object* v_s_1469_, lean_object* v_opts_1470_, lean_object* v_json_1471_, lean_object* v_severityOverrides_1472_, lean_object* v_a_1473_){
_start:
{
uint8_t v_json_boxed_1474_; lean_object* v_res_1475_; 
v_json_boxed_1474_ = lean_unbox(v_json_1471_);
v_res_1475_ = l_Lean_Language_SnapshotTree_runAndReport(v_s_1469_, v_opts_1470_, v_json_boxed_1474_, v_severityOverrides_1472_);
lean_dec(v_severityOverrides_1472_);
lean_dec_ref(v_opts_1470_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(lean_object* v_s_1476_, lean_object* v_init_1477_){
_start:
{
lean_object* v_element_1478_; lean_object* v_children_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v_element_1478_ = lean_ctor_get(v_s_1476_, 0);
lean_inc_ref(v_element_1478_);
v_children_1479_ = lean_ctor_get(v_s_1476_, 1);
lean_inc_ref(v_children_1479_);
lean_dec_ref(v_s_1476_);
v___x_1480_ = lean_array_push(v_init_1477_, v_element_1478_);
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_array_get_size(v_children_1479_);
v___x_1483_ = lean_nat_dec_lt(v___x_1481_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_dec_ref(v_children_1479_);
return v___x_1480_;
}
else
{
uint8_t v___x_1484_; 
v___x_1484_ = lean_nat_dec_le(v___x_1482_, v___x_1482_);
if (v___x_1484_ == 0)
{
if (v___x_1483_ == 0)
{
lean_dec_ref(v_children_1479_);
return v___x_1480_;
}
else
{
size_t v___x_1485_; size_t v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = ((size_t)0ULL);
v___x_1486_ = lean_usize_of_nat(v___x_1482_);
v___x_1487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_1479_, v___x_1485_, v___x_1486_, v___x_1480_);
lean_dec_ref(v_children_1479_);
return v___x_1487_;
}
}
else
{
size_t v___x_1488_; size_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = lean_usize_of_nat(v___x_1482_);
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_1479_, v___x_1488_, v___x_1489_, v___x_1480_);
lean_dec_ref(v_children_1479_);
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object* v_as_1491_, size_t v_i_1492_, size_t v_stop_1493_, lean_object* v_b_1494_){
_start:
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_usize_dec_eq(v_i_1492_, v_stop_1493_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; size_t v___x_1499_; size_t v___x_1500_; 
v___x_1496_ = lean_array_uget_borrowed(v_as_1491_, v_i_1492_);
lean_inc(v___x_1496_);
v___x_1497_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_1496_);
v___x_1498_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v___x_1497_, v_b_1494_);
v___x_1499_ = ((size_t)1ULL);
v___x_1500_ = lean_usize_add(v_i_1492_, v___x_1499_);
v_i_1492_ = v___x_1500_;
v_b_1494_ = v___x_1498_;
goto _start;
}
else
{
return v_b_1494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object* v_as_1502_, lean_object* v_i_1503_, lean_object* v_stop_1504_, lean_object* v_b_1505_){
_start:
{
size_t v_i_boxed_1506_; size_t v_stop_boxed_1507_; lean_object* v_res_1508_; 
v_i_boxed_1506_ = lean_unbox_usize(v_i_1503_);
lean_dec(v_i_1503_);
v_stop_boxed_1507_ = lean_unbox_usize(v_stop_1504_);
lean_dec(v_stop_1504_);
v_res_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_as_1502_, v_i_boxed_1506_, v_stop_boxed_1507_, v_b_1505_);
lean_dec_ref(v_as_1502_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object* v_s_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_Lean_Language_SnapshotTree_getAll___closed__0));
v___x_1513_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v_s_1511_, v___x_1512_);
return v___x_1513_;
}
}
static lean_object* _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_box(0);
v___x_1515_ = lean_task_pure(v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed(lean_object* v_tail_1516_, lean_object* v_t_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(v_tail_1516_, v_t_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(lean_object* v_a_1520_){
_start:
{
if (lean_obj_tag(v_a_1520_) == 0)
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_obj_once(&l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0, &l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0_once, _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0);
return v___x_1522_;
}
else
{
lean_object* v_head_1523_; lean_object* v_tail_1524_; lean_object* v_task_1525_; lean_object* v___f_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; 
v_head_1523_ = lean_ctor_get(v_a_1520_, 0);
lean_inc(v_head_1523_);
v_tail_1524_ = lean_ctor_get(v_a_1520_, 1);
lean_inc(v_tail_1524_);
lean_dec_ref_known(v_a_1520_, 2);
v_task_1525_ = lean_ctor_get(v_head_1523_, 3);
lean_inc_ref(v_task_1525_);
lean_dec(v_head_1523_);
v___f_1526_ = lean_alloc_closure((void*)(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1526_, 0, v_tail_1524_);
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = 1;
v___x_1529_ = lean_io_bind_task(v_task_1525_, v___f_1526_, v___x_1527_, v___x_1528_);
return v___x_1529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object* v_tail_1530_, lean_object* v_t_1531_){
_start:
{
lean_object* v_children_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_children_1533_ = lean_ctor_get(v_t_1531_, 1);
lean_inc_ref(v_children_1533_);
lean_dec_ref(v_t_1531_);
v___x_1534_ = lean_array_to_list(v_children_1533_);
v___x_1535_ = l_List_appendTR___redArg(v___x_1534_, v_tail_1530_);
v___x_1536_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___boxed(lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v_a_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object* v_x_1540_){
_start:
{
lean_object* v_children_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_children_1542_ = lean_ctor_get(v_x_1540_, 1);
lean_inc_ref(v_children_1542_);
lean_dec_ref(v_x_1540_);
v___x_1543_ = lean_array_to_list(v_children_1542_);
v___x_1544_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll___boxed(lean_object* v_x_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Language_SnapshotTree_waitAll(v_x_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object* v_00_u03b1_1548_, lean_object* v_act_1549_, lean_object* v_ctx_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_apply_2(v_act_1549_, v_ctx_1550_, lean_box(0));
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0___boxed(lean_object* v_00_u03b1_1554_, lean_object* v_act_1555_, lean_object* v_ctx_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(v_00_u03b1_1554_, v_act_1555_, v_ctx_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object* v_msgLog_1561_){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_st_mk_ref(v___x_1563_);
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v_msgLog_1561_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog___boxed(lean_object* v_msgLog_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object* v_msg_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_fileMap_1577_; lean_object* v_source_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_fileMap_1577_ = lean_ctor_get(v_a_1575_, 2);
v_source_1578_ = lean_ctor_get(v_fileMap_1577_, 0);
v___x_1579_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__0));
v___x_1580_ = ((lean_object*)(l_Lean_Language_diagnosticsOfHeaderError___closed__1));
v___x_1581_ = lean_string_utf8_byte_size(v_source_1578_);
lean_inc_ref(v_fileMap_1577_);
v___x_1582_ = l_Lean_FileMap_toPosition(v_fileMap_1577_, v___x_1581_);
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
v___x_1584_ = 0;
v___x_1585_ = 2;
v___x_1586_ = ((lean_object*)(l_Lean_Language_instInhabitedSnapshot___closed__0));
v___x_1587_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_msg_1574_);
v___x_1588_ = l_Lean_MessageData_ofFormat(v___x_1587_);
v___x_1589_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1589_, 0, v___x_1579_);
lean_ctor_set(v___x_1589_, 1, v___x_1580_);
lean_ctor_set(v___x_1589_, 2, v___x_1583_);
lean_ctor_set(v___x_1589_, 3, v___x_1586_);
lean_ctor_set(v___x_1589_, 4, v___x_1588_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*5, v___x_1584_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*5 + 1, v___x_1585_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*5 + 2, v___x_1584_);
v___x_1590_ = l_Lean_MessageLog_empty;
v___x_1591_ = l_Lean_MessageLog_add(v___x_1589_, v___x_1590_);
v___x_1592_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError___boxed(lean_object* v_msg_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Language_diagnosticsOfHeaderError(v_msg_1593_, v_a_1594_);
lean_dec_ref(v_a_1594_);
return v_res_1596_;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2(void){
_start:
{
uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = 1;
v___x_1603_ = ((lean_object*)(l_Lean_Language_withHeaderExceptions___redArg___closed__1));
v___x_1604_ = l_Lean_Name_toString(v___x_1603_, v___x_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object* v_ex_1605_, lean_object* v_act_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v___x_1609_; 
lean_inc_ref(v_a_1607_);
v___x_1609_ = lean_apply_2(v_act_1606_, v_a_1607_, lean_box(0));
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; 
lean_dec(v_ex_1605_);
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
return v_a_1610_;
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_a_1611_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1612_ = lean_io_error_to_string(v_a_1611_);
v___x_1613_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_1612_, v_a_1607_);
v___x_1614_ = lean_obj_once(&l_Lean_Language_withHeaderExceptions___redArg___closed__2, &l_Lean_Language_withHeaderExceptions___redArg___closed__2_once, _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2);
v___x_1615_ = lean_box(0);
v___x_1616_ = lean_obj_once(&l_Lean_Language_instInhabitedSnapshot___closed__3, &l_Lean_Language_instInhabitedSnapshot___closed__3_once, _init_l_Lean_Language_instInhabitedSnapshot___closed__3);
v___x_1617_ = 0;
v___x_1618_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1618_, 0, v___x_1614_);
lean_ctor_set(v___x_1618_, 1, v___x_1613_);
lean_ctor_set(v___x_1618_, 2, v___x_1615_);
lean_ctor_set(v___x_1618_, 3, v___x_1616_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*4, v___x_1617_);
v___x_1619_ = lean_apply_1(v_ex_1605_, v___x_1618_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg___boxed(lean_object* v_ex_1620_, lean_object* v_act_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1620_, v_act_1621_, v_a_1622_);
lean_dec_ref(v_a_1622_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object* v_00_u03b1_1625_, lean_object* v_ex_1626_, lean_object* v_act_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_1626_, v_act_1627_, v_a_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___boxed(lean_object* v_00_u03b1_1631_, lean_object* v_ex_1632_, lean_object* v_act_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Language_withHeaderExceptions(v_00_u03b1_1631_, v_ex_1632_, v_act_1633_, v_a_1634_);
lean_dec_ref(v_a_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object* v_val_1637_, lean_object* v_process_1638_, lean_object* v_ictx_1639_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1641_ = lean_st_ref_get(v_val_1637_);
v___x_1642_ = lean_apply_3(v_process_1638_, v___x_1641_, v_ictx_1639_, lean_box(0));
lean_inc(v___x_1642_);
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
v___x_1644_ = lean_st_ref_set(v_val_1637_, v___x_1643_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object* v_val_1645_, lean_object* v_process_1646_, lean_object* v_ictx_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(v_val_1645_, v_process_1646_, v_ictx_1647_);
lean_dec(v_val_1645_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object* v_process_1650_){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___f_1654_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = lean_st_mk_ref(v___x_1652_);
v___f_1654_ = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1654_, 0, v___x_1653_);
lean_closure_set(v___f_1654_, 1, v_process_1650_);
return v___f_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___boxed(lean_object* v_process_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object* v_InitSnap_1658_, lean_object* v_process_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_1659_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___boxed(lean_object* v_InitSnap_1662_, lean_object* v_process_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Language_mkIncrementalProcessor(v_InitSnap_1662_, v_process_1663_);
return v_res_1665_;
}
}
lean_object* runtime_initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Trace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
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
l_Lean_Language_instInhabitedSnapshotTreeTransform_default = _init_l_Lean_Language_instInhabitedSnapshotTreeTransform_default();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTreeTransform_default);
l_Lean_Language_instInhabitedSnapshotTreeTransform = _init_l_Lean_Language_instInhabitedSnapshotTreeTransform();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTreeTransform);
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
