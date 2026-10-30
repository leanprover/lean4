// Lean compiler output
// Module: Lean.Data.Trie
// Imports: public import Lean.Data.Format public import Init.Data.Option.Coe import Init.Omega
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_ByteArray_toList(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node1_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node1_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Data_Trie_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Data_Trie_empty___redArg___closed__0 = (const lean_object*)&l_Lean_Data_Trie_empty___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Data_Trie_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Data_Trie_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Data_Trie_values___redArg___closed__0 = (const lean_object*)&l_Lean_Data_Trie_values___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__0 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value;
static const lean_string_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__1 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value;
static const lean_string_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__2 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value;
static const lean_string_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__3 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__4 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value;
static const lean_array_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__5 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__5_value;
static const lean_string_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__6 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__7 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value;
static const lean_string_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__8 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__9 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__9_value;
static const lean_string_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__10 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__11 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__12;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__13;
static const lean_string_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__14 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__14_value;
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_0),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_1),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_2),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__15 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_Data_Trie_matchPrefix___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__9_value),((lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__5_value)}};
static const lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__16 = (const lean_object*)&l_Lean_Data_Trie_matchPrefix___auto__1___closed__16_value;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__17;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__18;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__19;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__20;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__21;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__22;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__23;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__24;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__25;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__26;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__27;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__28;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__29;
static lean_once_cell_t l_Lean_Data_Trie_matchPrefix___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_matchPrefix___auto__1___closed__30;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___auto__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0 = (const lean_object*)&l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Data_Trie_instToString___private__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToFormatFormat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_Trie_instToString___private__1___redArg___closed__0 = (const lean_object*)&l_Lean_Data_Trie_instToString___private__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Data_Trie_instToString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_Trie_instToString___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_Trie_instToString___redArg___closed__0 = (const lean_object*)&l_Lean_Data_Trie_instToString___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___redArg();
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Data_Trie_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___impl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Data_Trie_ctorIdx___impl(v_00_u03b1_8_, v_x_9_);
lean_dec_ref(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
switch(lean_obj_tag(v_t_11_))
{
case 0:
{
lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v_t_11_, 1);
v___x_14_ = lean_apply_1(v_k_12_, v_a_13_);
return v___x_14_;
}
case 1:
{
lean_object* v_a_15_; uint8_t v_a_16_; lean_object* v_a_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_a_15_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_15_);
v_a_16_ = lean_ctor_get_uint8(v_t_11_, sizeof(void*)*2);
v_a_17_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_a_17_);
lean_dec_ref_known(v_t_11_, 2);
v___x_18_ = lean_box(v_a_16_);
v___x_19_ = lean_apply_3(v_k_12_, v_a_15_, v___x_18_, v_a_17_);
return v___x_19_;
}
default: 
{
lean_object* v_a_20_; lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v___x_23_; 
v_a_20_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_20_);
v_a_21_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_a_21_);
v_a_22_ = lean_ctor_get(v_t_11_, 2);
lean_inc_ref(v_a_22_);
lean_dec_ref_known(v_t_11_, 3);
v___x_23_ = lean_apply_3(v_k_12_, v_a_20_, v_a_21_, v_a_22_);
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim(lean_object* v_00_u03b1_24_, lean_object* v_motive__1_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_27_, v_k_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim___boxed(lean_object* v_00_u03b1_31_, lean_object* v_motive__1_32_, lean_object* v_ctorIdx_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Data_Trie_ctorElim(v_00_u03b1_31_, v_motive__1_32_, v_ctorIdx_33_, v_t_34_, v_h_35_, v_k_36_);
lean_dec(v_ctorIdx_33_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_leaf_elim___redArg(lean_object* v_t_38_, lean_object* v_leaf_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_38_, v_leaf_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_leaf_elim(lean_object* v_00_u03b1_41_, lean_object* v_motive__1_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_leaf_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_43_, v_leaf_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node1_elim___redArg(lean_object* v_t_47_, lean_object* v_node1_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_47_, v_node1_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node1_elim(lean_object* v_00_u03b1_50_, lean_object* v_motive__1_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_node1_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_52_, v_node1_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node_elim___redArg(lean_object* v_t_56_, lean_object* v_node_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_56_, v_node_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node_elim(lean_object* v_00_u03b1_59_, lean_object* v_motive__1_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_node_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_61_, v_node_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty___redArg(){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = ((lean_object*)(l_Lean_Data_Trie_empty___redArg___closed__0));
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty___redArg___boxed(lean_object* v___dummy_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Data_Trie_empty___redArg();
return v_res_70_;
}
}
static lean_object* _init_l_Lean_Data_Trie_empty___closed__0(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Data_Trie_empty___redArg();
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty(lean_object* v_00_u03b1_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection___redArg___boxed(lean_object* v___dummy_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Data_Trie_instEmptyCollection___redArg();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection(lean_object* v_00_u03b1_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited___redArg(){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited___redArg___boxed(lean_object* v___dummy_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Data_Trie_instInhabited___redArg();
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited(lean_object* v_00_u03b1_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(lean_object* v_s_86_, lean_object* v_f_87_, lean_object* v_i_88_){
_start:
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_string_utf8_byte_size(v_s_86_);
v___x_90_ = lean_nat_dec_lt(v_i_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec(v_i_88_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_apply_1(v_f_87_, v___x_91_);
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
else
{
uint8_t v_c_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_t_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
lean_inc(v_i_88_);
v_c_95_ = lean_string_get_byte_fast(v_s_86_, v_i_88_);
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_nat_add(v_i_88_, v___x_96_);
lean_dec(v_i_88_);
v_t_98_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_86_, v_f_87_, v___x_97_);
v___x_99_ = lean_box(0);
v___x_100_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_t_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*2, v_c_95_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg___boxed(lean_object* v_s_101_, lean_object* v_f_102_, lean_object* v_i_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_101_, v_f_102_, v_i_103_);
lean_dec_ref(v_s_101_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(lean_object* v_00_u03b1_105_, lean_object* v_s_106_, lean_object* v_f_107_, lean_object* v_i_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_106_, v_f_107_, v_i_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___boxed(lean_object* v_00_u03b1_110_, lean_object* v_s_111_, lean_object* v_f_112_, lean_object* v_i_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(v_00_u03b1_110_, v_s_111_, v_f_112_, v_i_113_);
lean_dec_ref(v_s_111_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(uint8_t v_c_115_, lean_object* v_a_116_, lean_object* v_i_117_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_byte_array_size(v_a_116_);
v___x_119_ = lean_nat_dec_lt(v_i_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_dec(v_i_117_);
v___x_120_ = lean_box(0);
return v___x_120_;
}
else
{
uint8_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_byte_array_fget(v_a_116_, v_i_117_);
v___x_122_ = lean_uint8_dec_eq(v___x_121_, v_c_115_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_i_117_, v___x_123_);
lean_dec(v_i_117_);
v_i_117_ = v___x_124_;
goto _start;
}
else
{
lean_object* v___x_126_; 
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v_i_117_);
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0___boxed(lean_object* v_c_127_, lean_object* v_a_128_, lean_object* v_i_129_){
_start:
{
uint8_t v_c_boxed_130_; lean_object* v_res_131_; 
v_c_boxed_130_ = lean_unbox(v_c_127_);
v_res_131_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_boxed_130_, v_a_128_, v_i_129_);
lean_dec_ref(v_a_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(lean_object* v_s_132_, lean_object* v_f_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
switch(lean_obj_tag(v_x_135_))
{
case 0:
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_152_; 
v_a_136_ = lean_ctor_get(v_x_135_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v_x_135_);
if (v_isSharedCheck_152_ == 0)
{
v___x_138_ = v_x_135_;
v_isShared_139_ = v_isSharedCheck_152_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v_x_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_152_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = lean_string_utf8_byte_size(v_s_132_);
v___x_141_ = lean_nat_dec_lt(v_x_134_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
lean_dec(v_x_134_);
v___x_142_ = lean_apply_1(v_f_133_, v_a_136_);
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_143_);
v___x_145_ = v___x_138_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
else
{
uint8_t v_c_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_t_150_; lean_object* v___x_151_; 
lean_del_object(v___x_138_);
lean_inc(v_x_134_);
v_c_147_ = lean_string_get_byte_fast(v_s_132_, v_x_134_);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_x_134_, v___x_148_);
lean_dec(v_x_134_);
v_t_150_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_132_, v_f_133_, v___x_149_);
v___x_151_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_151_, 0, v_a_136_);
lean_ctor_set(v___x_151_, 1, v_t_150_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*2, v_c_147_);
return v___x_151_;
}
}
}
case 1:
{
lean_object* v_a_153_; uint8_t v_a_154_; lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_187_; 
v_a_153_ = lean_ctor_get(v_x_135_, 0);
v_a_154_ = lean_ctor_get_uint8(v_x_135_, sizeof(void*)*2);
v_a_155_ = lean_ctor_get(v_x_135_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_135_);
if (v_isSharedCheck_187_ == 0)
{
v___x_157_ = v_x_135_;
v_isShared_158_ = v_isSharedCheck_187_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_inc(v_a_153_);
lean_dec(v_x_135_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_187_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_string_utf8_byte_size(v_s_132_);
v___x_160_ = lean_nat_dec_lt(v_x_134_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
lean_dec(v_x_134_);
v___x_161_ = lean_apply_1(v_f_133_, v_a_153_);
v___x_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_162_);
v___x_164_ = v___x_157_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_a_155_);
lean_ctor_set_uint8(v_reuseFailAlloc_165_, sizeof(void*)*2, v_a_154_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
else
{
uint8_t v_c_166_; uint8_t v___x_167_; 
lean_inc(v_x_134_);
v_c_166_ = lean_string_get_byte_fast(v_s_132_, v_x_134_);
v___x_167_ = lean_uint8_dec_eq(v_c_166_, v_a_154_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_t_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_del_object(v___x_157_);
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lean_nat_add(v_x_134_, v___x_168_);
lean_dec(v_x_134_);
v_t_170_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_132_, v_f_133_, v___x_169_);
v___x_171_ = lean_unsigned_to_nat(2u);
v___x_172_ = lean_mk_empty_array_with_capacity(v___x_171_);
v___x_173_ = lean_box(v_c_166_);
lean_inc_ref(v___x_172_);
v___x_174_ = lean_array_push(v___x_172_, v___x_173_);
v___x_175_ = lean_box(v_a_154_);
v___x_176_ = lean_array_push(v___x_174_, v___x_175_);
v___x_177_ = lean_byte_array_mk(v___x_176_);
v___x_178_ = lean_array_push(v___x_172_, v_t_170_);
v___x_179_ = lean_array_push(v___x_178_, v_a_155_);
v___x_180_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_180_, 0, v_a_153_);
lean_ctor_set(v___x_180_, 1, v___x_177_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_x_134_, v___x_181_);
lean_dec(v_x_134_);
v___x_183_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_132_, v_f_133_, v___x_182_, v_a_155_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 1, v___x_183_);
v___x_185_ = v___x_157_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_153_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*2, v_a_154_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
default: 
{
lean_object* v_a_188_; lean_object* v_a_189_; lean_object* v_a_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_a_188_ = lean_ctor_get(v_x_135_, 0);
v_a_189_ = lean_ctor_get(v_x_135_, 1);
v_a_190_ = lean_ctor_get(v_x_135_, 2);
v___x_191_ = lean_string_utf8_byte_size(v_s_132_);
v___x_192_ = lean_nat_dec_lt(v_x_134_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_201_; 
lean_inc_ref(v_a_190_);
lean_inc_ref(v_a_189_);
lean_inc(v_a_188_);
lean_dec(v_x_134_);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_135_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_202_ = lean_ctor_get(v_x_135_, 2);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_x_135_, 1);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_x_135_, 0);
lean_dec(v_unused_204_);
v___x_194_ = v_x_135_;
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
else
{
lean_dec(v_x_135_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_196_ = lean_apply_1(v_f_133_, v_a_188_);
v___x_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_197_);
v___x_199_ = v___x_194_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_a_189_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_a_190_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
uint8_t v_c_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
lean_inc(v_x_134_);
v_c_205_ = lean_string_get_byte_fast(v_s_132_, v_x_134_);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_205_, v_a_189_, v___x_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_219_; 
lean_inc_ref(v_a_190_);
lean_inc_ref(v_a_189_);
lean_inc(v_a_188_);
v_isSharedCheck_219_ = !lean_is_exclusive(v_x_135_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; lean_object* v_unused_221_; lean_object* v_unused_222_; 
v_unused_220_ = lean_ctor_get(v_x_135_, 2);
lean_dec(v_unused_220_);
v_unused_221_ = lean_ctor_get(v_x_135_, 1);
lean_dec(v_unused_221_);
v_unused_222_ = lean_ctor_get(v_x_135_, 0);
lean_dec(v_unused_222_);
v___x_209_ = v_x_135_;
v_isShared_210_ = v_isSharedCheck_219_;
goto v_resetjp_208_;
}
else
{
lean_dec(v_x_135_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_219_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_t_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_x_134_, v___x_211_);
lean_dec(v_x_134_);
v_t_213_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_132_, v_f_133_, v___x_212_);
v___x_214_ = lean_byte_array_push(v_a_189_, v_c_205_);
v___x_215_ = lean_array_push(v_a_190_, v_t_213_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 2, v___x_215_);
lean_ctor_set(v___x_209_, 1, v___x_214_);
v___x_217_ = v___x_209_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_188_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v_val_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_val_223_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_207_, 1);
v___x_224_ = lean_array_get_size(v_a_190_);
v___x_225_ = lean_nat_dec_lt(v_val_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_dec(v_val_223_);
lean_dec(v_x_134_);
lean_dec(v_f_133_);
return v_x_135_;
}
else
{
lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_239_; 
lean_inc_ref(v_a_190_);
lean_inc_ref(v_a_189_);
lean_inc(v_a_188_);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_135_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; lean_object* v_unused_241_; lean_object* v_unused_242_; 
v_unused_240_ = lean_ctor_get(v_x_135_, 2);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_x_135_, 1);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v_x_135_, 0);
lean_dec(v_unused_242_);
v___x_227_ = v_x_135_;
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
else
{
lean_dec(v_x_135_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_v_231_; lean_object* v___x_232_; lean_object* v_xs_x27_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = lean_nat_add(v_x_134_, v___x_229_);
lean_dec(v_x_134_);
v_v_231_ = lean_array_fget(v_a_190_, v_val_223_);
v___x_232_ = lean_box(0);
v_xs_x27_233_ = lean_array_fset(v_a_190_, v_val_223_, v___x_232_);
v___x_234_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_132_, v_f_133_, v___x_230_, v_v_231_);
v___x_235_ = lean_array_fset(v_xs_x27_233_, v_val_223_, v___x_234_);
lean_dec(v_val_223_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 2, v___x_235_);
v___x_237_ = v___x_227_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_188_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_a_189_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg___boxed(lean_object* v_s_243_, lean_object* v_f_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_243_, v_f_244_, v_x_245_, v_x_246_);
lean_dec_ref(v_s_243_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(lean_object* v_00_u03b1_248_, lean_object* v_s_249_, lean_object* v_f_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_249_, v_f_250_, v_x_251_, v_x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___boxed(lean_object* v_00_u03b1_254_, lean_object* v_s_255_, lean_object* v_f_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(v_00_u03b1_254_, v_s_255_, v_f_256_, v_x_257_, v_x_258_);
lean_dec_ref(v_s_255_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg(lean_object* v_t_260_, lean_object* v_s_261_, lean_object* v_f_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_261_, v_f_262_, v___x_263_, v_t_260_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg___boxed(lean_object* v_t_265_, lean_object* v_s_266_, lean_object* v_f_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Data_Trie_upsert___redArg(v_t_265_, v_s_266_, v_f_267_);
lean_dec_ref(v_s_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert(lean_object* v_00_u03b1_269_, lean_object* v_t_270_, lean_object* v_s_271_, lean_object* v_f_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Data_Trie_upsert___redArg(v_t_270_, v_s_271_, v_f_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___boxed(lean_object* v_00_u03b1_274_, lean_object* v_t_275_, lean_object* v_s_276_, lean_object* v_f_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Data_Trie_upsert(v_00_u03b1_274_, v_t_275_, v_s_276_, v_f_277_);
lean_dec_ref(v_s_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0(lean_object* v_val_279_, lean_object* v_x_280_){
_start:
{
lean_inc(v_val_279_);
return v_val_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0___boxed(lean_object* v_val_281_, lean_object* v_x_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Data_Trie_insert___redArg___lam__0(v_val_281_, v_x_282_);
lean_dec(v_x_282_);
lean_dec(v_val_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg(lean_object* v_t_284_, lean_object* v_s_285_, lean_object* v_val_286_){
_start:
{
lean_object* v___f_287_; lean_object* v___x_288_; 
v___f_287_ = lean_alloc_closure((void*)(l_Lean_Data_Trie_insert___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_287_, 0, v_val_286_);
v___x_288_ = l_Lean_Data_Trie_upsert___redArg(v_t_284_, v_s_285_, v___f_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___boxed(lean_object* v_t_289_, lean_object* v_s_290_, lean_object* v_val_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Data_Trie_insert___redArg(v_t_289_, v_s_290_, v_val_291_);
lean_dec_ref(v_s_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert(lean_object* v_00_u03b1_293_, lean_object* v_t_294_, lean_object* v_s_295_, lean_object* v_val_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Data_Trie_insert___redArg(v_t_294_, v_s_295_, v_val_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___boxed(lean_object* v_00_u03b1_298_, lean_object* v_t_299_, lean_object* v_s_300_, lean_object* v_val_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Data_Trie_insert(v_00_u03b1_298_, v_t_299_, v_s_300_, v_val_301_);
lean_dec_ref(v_s_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(lean_object* v_s_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
switch(lean_obj_tag(v_x_305_))
{
case 0:
{
lean_object* v_a_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_a_306_ = lean_ctor_get(v_x_305_, 0);
v___x_307_ = lean_string_utf8_byte_size(v_s_303_);
v___x_308_ = lean_nat_dec_lt(v_x_304_, v___x_307_);
lean_dec(v_x_304_);
if (v___x_308_ == 0)
{
lean_inc(v_a_306_);
return v_a_306_;
}
else
{
lean_object* v___x_309_; 
v___x_309_ = lean_box(0);
return v___x_309_;
}
}
case 1:
{
lean_object* v_a_310_; uint8_t v_a_311_; lean_object* v_a_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v_a_310_ = lean_ctor_get(v_x_305_, 0);
v_a_311_ = lean_ctor_get_uint8(v_x_305_, sizeof(void*)*2);
v_a_312_ = lean_ctor_get(v_x_305_, 1);
v___x_313_ = lean_string_utf8_byte_size(v_s_303_);
v___x_314_ = lean_nat_dec_lt(v_x_304_, v___x_313_);
if (v___x_314_ == 0)
{
lean_dec(v_x_304_);
lean_inc(v_a_310_);
return v_a_310_;
}
else
{
uint8_t v_c_315_; uint8_t v___x_316_; 
lean_inc(v_x_304_);
v_c_315_ = lean_string_get_byte_fast(v_s_303_, v_x_304_);
v___x_316_ = lean_uint8_dec_eq(v_c_315_, v_a_311_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec(v_x_304_);
v___x_317_ = lean_box(0);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_add(v_x_304_, v___x_318_);
lean_dec(v_x_304_);
v_x_304_ = v___x_319_;
v_x_305_ = v_a_312_;
goto _start;
}
}
}
default: 
{
lean_object* v_a_321_; lean_object* v_a_322_; lean_object* v_a_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_a_321_ = lean_ctor_get(v_x_305_, 0);
v_a_322_ = lean_ctor_get(v_x_305_, 1);
v_a_323_ = lean_ctor_get(v_x_305_, 2);
v___x_324_ = lean_string_utf8_byte_size(v_s_303_);
v___x_325_ = lean_nat_dec_lt(v_x_304_, v___x_324_);
if (v___x_325_ == 0)
{
lean_dec(v_x_304_);
lean_inc(v_a_321_);
return v_a_321_;
}
else
{
uint8_t v_c_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_inc(v_x_304_);
v_c_326_ = lean_string_get_byte_fast(v_s_303_, v_x_304_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_326_, v_a_322_, v___x_327_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; 
lean_dec(v_x_304_);
v___x_329_ = lean_box(0);
return v___x_329_;
}
else
{
lean_object* v_val_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_val_330_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_val_330_);
lean_dec_ref_known(v___x_328_, 1);
v___x_331_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = lean_nat_add(v_x_304_, v___x_332_);
lean_dec(v_x_304_);
v___x_334_ = lean_array_get_borrowed(v___x_331_, v_a_323_, v_val_330_);
lean_dec(v_val_330_);
v_x_304_ = v___x_333_;
v_x_305_ = v___x_334_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg___boxed(lean_object* v_s_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_336_, v_x_337_, v_x_338_);
lean_dec_ref(v_x_338_);
lean_dec_ref(v_s_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(lean_object* v_00_u03b1_340_, lean_object* v_s_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_341_, v_x_342_, v_x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___boxed(lean_object* v_00_u03b1_345_, lean_object* v_s_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(v_00_u03b1_345_, v_s_346_, v_x_347_, v_x_348_);
lean_dec_ref(v_x_348_);
lean_dec_ref(v_s_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg(lean_object* v_t_350_, lean_object* v_s_351_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_351_, v___x_352_, v_t_350_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg___boxed(lean_object* v_t_354_, lean_object* v_s_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_354_, v_s_355_);
lean_dec_ref(v_s_355_);
lean_dec_ref(v_t_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f(lean_object* v_00_u03b1_357_, lean_object* v_t_358_, lean_object* v_s_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_358_, v_s_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___boxed(lean_object* v_00_u03b1_361_, lean_object* v_t_362_, lean_object* v_s_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Data_Trie_find_x3f(v_00_u03b1_361_, v_t_362_, v_s_363_);
lean_dec_ref(v_s_363_);
lean_dec_ref(v_t_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
switch(lean_obj_tag(v_a_365_))
{
case 0:
{
lean_object* v_a_367_; 
v_a_367_ = lean_ctor_get(v_a_365_, 0);
if (lean_obj_tag(v_a_367_) == 1)
{
lean_object* v_val_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_val_368_ = lean_ctor_get(v_a_367_, 0);
v___x_369_ = lean_box(0);
lean_inc(v_val_368_);
v___x_370_ = lean_array_push(v_a_366_, v_val_368_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_box(0);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v_a_366_);
return v___x_373_;
}
}
case 1:
{
lean_object* v_a_374_; 
v_a_374_ = lean_ctor_get(v_a_365_, 0);
if (lean_obj_tag(v_a_374_) == 1)
{
lean_object* v_a_375_; lean_object* v_val_376_; lean_object* v___x_377_; 
v_a_375_ = lean_ctor_get(v_a_365_, 1);
v_val_376_ = lean_ctor_get(v_a_374_, 0);
lean_inc(v_val_376_);
v___x_377_ = lean_array_push(v_a_366_, v_val_376_);
v_a_365_ = v_a_375_;
v_a_366_ = v___x_377_;
goto _start;
}
else
{
lean_object* v_a_379_; 
v_a_379_ = lean_ctor_get(v_a_365_, 1);
v_a_365_ = v_a_379_;
goto _start;
}
}
default: 
{
lean_object* v_a_381_; lean_object* v_a_382_; lean_object* v___y_384_; 
v_a_381_ = lean_ctor_get(v_a_365_, 0);
v_a_382_ = lean_ctor_get(v_a_365_, 2);
if (lean_obj_tag(v_a_381_) == 1)
{
lean_object* v_val_393_; lean_object* v___x_394_; 
v_val_393_ = lean_ctor_get(v_a_381_, 0);
lean_inc(v_val_393_);
v___x_394_ = lean_array_push(v_a_366_, v_val_393_);
v___y_384_ = v___x_394_;
goto v___jp_383_;
}
else
{
v___y_384_ = v_a_366_;
goto v___jp_383_;
}
v___jp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_array_get_size(v_a_382_);
v___x_387_ = lean_box(0);
v___x_388_ = lean_nat_dec_lt(v___x_385_, v___x_386_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___y_384_);
return v___x_389_;
}
else
{
size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; 
v___x_390_ = ((size_t)0ULL);
v___x_391_ = lean_usize_of_nat(v___x_386_);
v___x_392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_a_382_, v___x_390_, v___x_391_, v___x_387_, v___y_384_);
return v___x_392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(lean_object* v_as_395_, size_t v_i_396_, size_t v_stop_397_, lean_object* v_b_398_, lean_object* v___y_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = lean_usize_dec_eq(v_i_396_, v_stop_397_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_fst_403_; lean_object* v_snd_404_; size_t v___x_405_; size_t v___x_406_; 
v___x_401_ = lean_array_uget_borrowed(v_as_395_, v_i_396_);
v___x_402_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v___x_401_, v___y_399_);
v_fst_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_fst_403_);
v_snd_404_ = lean_ctor_get(v___x_402_, 1);
lean_inc(v_snd_404_);
lean_dec_ref(v___x_402_);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_add(v_i_396_, v___x_405_);
v_i_396_ = v___x_406_;
v_b_398_ = v_fst_403_;
v___y_399_ = v_snd_404_;
goto _start;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_b_398_);
lean_ctor_set(v___x_408_, 1, v___y_399_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg___boxed(lean_object* v_as_409_, lean_object* v_i_410_, lean_object* v_stop_411_, lean_object* v_b_412_, lean_object* v___y_413_){
_start:
{
size_t v_i_boxed_414_; size_t v_stop_boxed_415_; lean_object* v_res_416_; 
v_i_boxed_414_ = lean_unbox_usize(v_i_410_);
lean_dec(v_i_410_);
v_stop_boxed_415_ = lean_unbox_usize(v_stop_411_);
lean_dec(v_stop_411_);
v_res_416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_409_, v_i_boxed_414_, v_stop_boxed_415_, v_b_412_, v___y_413_);
lean_dec_ref(v_as_409_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg___boxed(lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_417_, v_a_418_);
lean_dec_ref(v_a_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(lean_object* v_00_u03b1_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_421_, v_a_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___boxed(lean_object* v_00_u03b1_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(v_00_u03b1_424_, v_a_425_, v_a_426_);
lean_dec_ref(v_a_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(lean_object* v_00_u03b1_428_, lean_object* v_as_429_, size_t v_i_430_, size_t v_stop_431_, lean_object* v_b_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_429_, v_i_430_, v_stop_431_, v_b_432_, v___y_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___boxed(lean_object* v_00_u03b1_435_, lean_object* v_as_436_, lean_object* v_i_437_, lean_object* v_stop_438_, lean_object* v_b_439_, lean_object* v___y_440_){
_start:
{
size_t v_i_boxed_441_; size_t v_stop_boxed_442_; lean_object* v_res_443_; 
v_i_boxed_441_ = lean_unbox_usize(v_i_437_);
lean_dec(v_i_437_);
v_stop_boxed_442_ = lean_unbox_usize(v_stop_438_);
lean_dec(v_stop_438_);
v_res_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(v_00_u03b1_435_, v_as_436_, v_i_boxed_441_, v_stop_boxed_442_, v_b_439_, v___y_440_);
lean_dec_ref(v_as_436_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg(lean_object* v_t_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_snd_449_; 
v___x_447_ = ((lean_object*)(l_Lean_Data_Trie_values___redArg___closed__0));
v___x_448_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_t_446_, v___x_447_);
v_snd_449_ = lean_ctor_get(v___x_448_, 1);
lean_inc(v_snd_449_);
lean_dec_ref(v___x_448_);
return v_snd_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg___boxed(lean_object* v_t_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Data_Trie_values___redArg(v_t_450_);
lean_dec_ref(v_t_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values(lean_object* v_00_u03b1_452_, lean_object* v_t_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Data_Trie_values___redArg(v_t_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___boxed(lean_object* v_00_u03b1_455_, lean_object* v_t_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Data_Trie_values(v_00_u03b1_455_, v_t_456_);
lean_dec_ref(v_t_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(lean_object* v_pre_460_, lean_object* v_t_461_, lean_object* v_i_462_){
_start:
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_string_utf8_byte_size(v_pre_460_);
v___x_464_ = lean_nat_dec_lt(v_i_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; 
lean_dec(v_i_462_);
v___x_465_ = l_Lean_Data_Trie_values___redArg(v_t_461_);
return v___x_465_;
}
else
{
uint8_t v_c_466_; 
lean_inc(v_i_462_);
v_c_466_ = lean_string_get_byte_fast(v_pre_460_, v_i_462_);
switch(lean_obj_tag(v_t_461_))
{
case 0:
{
lean_object* v___x_467_; 
lean_dec(v_i_462_);
v___x_467_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_467_;
}
case 1:
{
uint8_t v_a_468_; lean_object* v_a_469_; uint8_t v___x_470_; 
v_a_468_ = lean_ctor_get_uint8(v_t_461_, sizeof(void*)*2);
v_a_469_ = lean_ctor_get(v_t_461_, 1);
v___x_470_ = lean_uint8_dec_eq(v_c_466_, v_a_468_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
lean_dec(v_i_462_);
v___x_471_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_471_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_add(v_i_462_, v___x_472_);
lean_dec(v_i_462_);
v_t_461_ = v_a_469_;
v_i_462_ = v___x_473_;
goto _start;
}
}
default: 
{
lean_object* v_a_475_; lean_object* v_a_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_a_475_ = lean_ctor_get(v_t_461_, 1);
v_a_476_ = lean_ctor_get(v_t_461_, 2);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_466_, v_a_475_, v___x_477_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v___x_479_; 
lean_dec(v_i_462_);
v___x_479_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_479_;
}
else
{
lean_object* v_val_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_val_480_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_val_480_);
lean_dec_ref_known(v___x_478_, 1);
v___x_481_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
v___x_482_ = lean_array_get_borrowed(v___x_481_, v_a_476_, v_val_480_);
lean_dec(v_val_480_);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_i_462_, v___x_483_);
lean_dec(v_i_462_);
v_t_461_ = v___x_482_;
v_i_462_ = v___x_484_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___boxed(lean_object* v_pre_486_, lean_object* v_t_487_, lean_object* v_i_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_486_, v_t_487_, v_i_488_);
lean_dec_ref(v_t_487_);
lean_dec_ref(v_pre_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(lean_object* v_00_u03b1_490_, lean_object* v_pre_491_, lean_object* v_t_492_, lean_object* v_i_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_491_, v_t_492_, v_i_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___boxed(lean_object* v_00_u03b1_495_, lean_object* v_pre_496_, lean_object* v_t_497_, lean_object* v_i_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(v_00_u03b1_495_, v_pre_496_, v_t_497_, v_i_498_);
lean_dec_ref(v_t_497_);
lean_dec_ref(v_pre_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object* v_t_500_, lean_object* v_pre_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_501_, v_t_500_, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg___boxed(lean_object* v_t_504_, lean_object* v_pre_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_504_, v_pre_505_);
lean_dec_ref(v_pre_505_);
lean_dec_ref(v_t_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix(lean_object* v_00_u03b1_507_, lean_object* v_t_508_, lean_object* v_pre_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_508_, v_pre_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___boxed(lean_object* v_00_u03b1_511_, lean_object* v_t_512_, lean_object* v_pre_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Data_Trie_findPrefix(v_00_u03b1_511_, v_t_512_, v_pre_513_);
lean_dec_ref(v_pre_513_);
lean_dec_ref(v_t_512_);
return v_res_514_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__10));
v___x_542_ = l_Lean_mkAtom(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__12, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__12_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12);
v___x_544_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_545_ = lean_array_push(v___x_544_, v___x_543_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_557_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_558_ = lean_array_push(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_559_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__17, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__17_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17);
v___x_560_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15));
v___x_561_ = lean_box(2);
v___x_562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
lean_ctor_set(v___x_562_, 2, v___x_559_);
return v___x_562_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__18, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__18_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18);
v___x_564_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__13, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__13_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13);
v___x_565_ = lean_array_push(v___x_564_, v___x_563_);
return v___x_565_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_567_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__19, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__19_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19);
v___x_568_ = lean_array_push(v___x_567_, v___x_566_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_570_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__20, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__20_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20);
v___x_571_ = lean_array_push(v___x_570_, v___x_569_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_573_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__21, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__21_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21);
v___x_574_ = lean_array_push(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_576_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__22, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__22_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22);
v___x_577_ = lean_array_push(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__23, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__23_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23);
v___x_579_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11));
v___x_580_ = lean_box(2);
v___x_581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_578_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__24, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__24_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24);
v___x_583_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_584_ = lean_array_push(v___x_583_, v___x_582_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__25, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__25_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25);
v___x_586_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__9));
v___x_587_ = lean_box(2);
v___x_588_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_586_);
lean_ctor_set(v___x_588_, 2, v___x_585_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__26, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__26_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26);
v___x_590_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_591_ = lean_array_push(v___x_590_, v___x_589_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_592_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__27, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__27_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27);
v___x_593_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7));
v___x_594_ = lean_box(2);
v___x_595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
lean_ctor_set(v___x_595_, 2, v___x_592_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__28, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__28_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28);
v___x_597_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_598_ = lean_array_push(v___x_597_, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_599_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__29, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__29_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29);
v___x_600_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4));
v___x_601_ = lean_box(2);
v___x_602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
lean_ctor_set(v___x_602_, 2, v___x_599_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__30, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__30_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(lean_object* v_s_604_, lean_object* v_endByte_605_, lean_object* v_x_606_, lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
switch(lean_obj_tag(v_x_606_))
{
case 0:
{
lean_object* v_a_609_; 
lean_dec(v_x_607_);
v_a_609_ = lean_ctor_get(v_x_606_, 0);
if (lean_obj_tag(v_a_609_) == 0)
{
lean_inc(v_x_608_);
return v_x_608_;
}
else
{
lean_inc_ref(v_a_609_);
return v_a_609_;
}
}
case 1:
{
lean_object* v_a_610_; uint8_t v_a_611_; lean_object* v_a_612_; lean_object* v___y_614_; 
v_a_610_ = lean_ctor_get(v_x_606_, 0);
v_a_611_ = lean_ctor_get_uint8(v_x_606_, sizeof(void*)*2);
v_a_612_ = lean_ctor_get(v_x_606_, 1);
if (lean_obj_tag(v_a_610_) == 0)
{
v___y_614_ = v_x_608_;
goto v___jp_613_;
}
else
{
v___y_614_ = v_a_610_;
goto v___jp_613_;
}
v___jp_613_:
{
uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_lt(v_x_607_, v_endByte_605_);
if (v___x_615_ == 0)
{
lean_dec(v_x_607_);
lean_inc(v___y_614_);
return v___y_614_;
}
else
{
uint8_t v_c_616_; uint8_t v___x_617_; 
lean_inc(v_x_607_);
v_c_616_ = lean_string_get_byte_fast(v_s_604_, v_x_607_);
v___x_617_ = lean_uint8_dec_eq(v_c_616_, v_a_611_);
if (v___x_617_ == 0)
{
lean_dec(v_x_607_);
lean_inc(v___y_614_);
return v___y_614_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_add(v_x_607_, v___x_618_);
lean_dec(v_x_607_);
v_x_606_ = v_a_612_;
v_x_607_ = v___x_619_;
v_x_608_ = v___y_614_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_621_; lean_object* v_a_622_; lean_object* v_a_623_; lean_object* v___x_624_; lean_object* v___y_626_; 
v_a_621_ = lean_ctor_get(v_x_606_, 0);
v_a_622_ = lean_ctor_get(v_x_606_, 1);
v_a_623_ = lean_ctor_get(v_x_606_, 2);
v___x_624_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
if (lean_obj_tag(v_a_621_) == 0)
{
v___y_626_ = v_x_608_;
goto v___jp_625_;
}
else
{
v___y_626_ = v_a_621_;
goto v___jp_625_;
}
v___jp_625_:
{
uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_lt(v_x_607_, v_endByte_605_);
if (v___x_627_ == 0)
{
lean_dec(v_x_607_);
lean_inc(v___y_626_);
return v___y_626_;
}
else
{
uint8_t v_c_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_inc(v_x_607_);
v_c_628_ = lean_string_get_byte_fast(v_s_604_, v_x_607_);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_628_, v_a_622_, v___x_629_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_dec(v_x_607_);
lean_inc(v___y_626_);
return v___y_626_;
}
else
{
lean_object* v_val_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = lean_array_get_borrowed(v___x_624_, v_a_623_, v_val_631_);
lean_dec(v_val_631_);
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = lean_nat_add(v_x_607_, v___x_633_);
lean_dec(v_x_607_);
v_x_606_ = v___x_632_;
v_x_607_ = v___x_634_;
v_x_608_ = v___y_626_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg___boxed(lean_object* v_s_636_, lean_object* v_endByte_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_636_, v_endByte_637_, v_x_638_, v_x_639_, v_x_640_);
lean_dec(v_x_640_);
lean_dec_ref(v_x_638_);
lean_dec(v_endByte_637_);
lean_dec_ref(v_s_636_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(lean_object* v_00_u03b1_642_, lean_object* v_s_643_, lean_object* v_endByte_644_, lean_object* v_endByte__valid_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_643_, v_endByte_644_, v_x_646_, v_x_647_, v_x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___boxed(lean_object* v_00_u03b1_650_, lean_object* v_s_651_, lean_object* v_endByte_652_, lean_object* v_endByte__valid_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(v_00_u03b1_650_, v_s_651_, v_endByte_652_, v_endByte__valid_653_, v_x_654_, v_x_655_, v_x_656_);
lean_dec(v_x_656_);
lean_dec_ref(v_x_654_);
lean_dec(v_endByte_652_);
lean_dec_ref(v_s_651_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg(lean_object* v_s_658_, lean_object* v_t_659_, lean_object* v_i_660_, lean_object* v_endByte_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_box(0);
v___x_663_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_658_, v_endByte_661_, v_t_659_, v_i_660_, v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg___boxed(lean_object* v_s_664_, lean_object* v_t_665_, lean_object* v_i_666_, lean_object* v_endByte_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_664_, v_t_665_, v_i_666_, v_endByte_667_);
lean_dec(v_endByte_667_);
lean_dec_ref(v_t_665_);
lean_dec_ref(v_s_664_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix(lean_object* v_00_u03b1_669_, lean_object* v_s_670_, lean_object* v_t_671_, lean_object* v_i_672_, lean_object* v_endByte_673_, lean_object* v_endByte__valid_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_670_, v_t_671_, v_i_672_, v_endByte_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___boxed(lean_object* v_00_u03b1_676_, lean_object* v_s_677_, lean_object* v_t_678_, lean_object* v_i_679_, lean_object* v_endByte_680_, lean_object* v_endByte__valid_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Data_Trie_matchPrefix(v_00_u03b1_676_, v_s_677_, v_t_678_, v_i_679_, v_endByte_680_, v_endByte__valid_681_);
lean_dec(v_endByte_680_);
lean_dec_ref(v_t_678_);
lean_dec_ref(v_s_677_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
if (lean_obj_tag(v_x_685_) == 0)
{
lean_dec(v_x_683_);
return v_x_684_;
}
else
{
lean_object* v_head_686_; lean_object* v_tail_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_696_; 
v_head_686_ = lean_ctor_get(v_x_685_, 0);
v_tail_687_ = lean_ctor_get(v_x_685_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_685_);
if (v_isSharedCheck_696_ == 0)
{
v___x_689_ = v_x_685_;
v_isShared_690_ = v_isSharedCheck_696_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_tail_687_);
lean_inc(v_head_686_);
lean_dec(v_x_685_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_696_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
lean_inc(v_x_683_);
if (v_isShared_690_ == 0)
{
lean_ctor_set_tag(v___x_689_, 5);
lean_ctor_set(v___x_689_, 1, v_x_683_);
lean_ctor_set(v___x_689_, 0, v_x_684_);
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_x_684_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_x_683_);
v___x_692_ = v_reuseFailAlloc_695_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v_head_686_);
v_x_684_ = v___x_693_;
v_x_685_ = v_tail_687_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
if (lean_obj_tag(v_x_697_) == 0)
{
lean_object* v___x_699_; 
lean_dec(v_x_698_);
v___x_699_ = lean_box(0);
return v___x_699_;
}
else
{
lean_object* v_tail_700_; 
v_tail_700_ = lean_ctor_get(v_x_697_, 1);
if (lean_obj_tag(v_tail_700_) == 0)
{
lean_object* v_head_701_; 
lean_dec(v_x_698_);
v_head_701_ = lean_ctor_get(v_x_697_, 0);
lean_inc(v_head_701_);
lean_dec_ref_known(v_x_697_, 2);
return v_head_701_;
}
else
{
lean_object* v_head_702_; lean_object* v___x_703_; 
lean_inc(v_tail_700_);
v_head_702_ = lean_ctor_get(v_x_697_, 0);
lean_inc(v_head_702_);
lean_dec_ref_known(v_x_697_, 2);
v___x_703_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(v_x_698_, v_head_702_, v_tail_700_);
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
if (lean_obj_tag(v_a_704_) == 0)
{
lean_object* v___x_706_; 
v___x_706_ = lean_array_to_list(v_a_705_);
return v___x_706_;
}
else
{
lean_object* v_head_707_; lean_object* v_tail_708_; lean_object* v___x_709_; 
v_head_707_ = lean_ctor_get(v_a_704_, 0);
lean_inc(v_head_707_);
v_tail_708_ = lean_ctor_get(v_a_704_, 1);
lean_inc(v_tail_708_);
lean_dec_ref_known(v_a_704_, 2);
v___x_709_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_705_, v_head_707_);
v_a_704_ = v_tail_708_;
v_a_705_ = v___x_709_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_unsigned_to_nat(4u);
v___x_712_ = lean_nat_to_int(v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed(lean_object* v_c_713_, lean_object* v_t_714_){
_start:
{
uint8_t v_c_boxed_715_; lean_object* v_res_716_; 
v_c_boxed_715_ = lean_unbox(v_c_713_);
v_res_716_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(v_c_boxed_715_, v_t_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(lean_object* v_x_719_){
_start:
{
switch(lean_obj_tag(v_x_719_))
{
case 0:
{
lean_object* v___x_720_; 
lean_dec_ref_known(v_x_719_, 1);
v___x_720_ = lean_box(0);
return v___x_720_;
}
case 1:
{
uint8_t v_a_721_; lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_a_721_ = lean_ctor_get_uint8(v_x_719_, sizeof(void*)*2);
v_a_722_ = lean_ctor_get(v_x_719_, 1);
lean_inc_ref(v_a_722_);
lean_dec_ref_known(v_x_719_, 2);
v___x_723_ = lean_uint8_to_nat(v_a_721_);
v___x_724_ = l_Nat_reprFast(v___x_723_);
v___x_725_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
v___x_726_ = lean_obj_once(&l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0, &l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once, _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
v___x_727_ = lean_box(1);
v___x_728_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_a_722_);
v___x_729_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_728_, v___x_727_);
v___x_730_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_726_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = 0;
v___x_732_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*1, v___x_731_);
v___x_733_ = lean_box(0);
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_725_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
return v___x_735_;
}
default: 
{
lean_object* v_a_736_; lean_object* v_a_737_; lean_object* v___f_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_a_736_ = lean_ctor_get(v_x_719_, 1);
lean_inc_ref(v_a_736_);
v_a_737_ = lean_ctor_get(v_x_719_, 2);
lean_inc_ref(v_a_737_);
lean_dec_ref_known(v_x_719_, 3);
v___f_738_ = lean_alloc_closure((void*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed), 2, 0);
v___x_739_ = l_ByteArray_toList(v_a_736_);
lean_dec_ref(v_a_736_);
v___x_740_ = lean_array_to_list(v_a_737_);
v___x_741_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0));
v___x_742_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_738_, v___x_739_, v___x_740_, v___x_741_);
v___x_743_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(v___x_742_, v___x_741_);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(uint8_t v_c_744_, lean_object* v_t_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_746_ = lean_uint8_to_nat(v_c_744_);
v___x_747_ = l_Nat_reprFast(v___x_746_);
v___x_748_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
v___x_749_ = lean_obj_once(&l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0, &l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once, _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
v___x_750_ = lean_box(1);
v___x_751_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_745_);
v___x_752_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_751_, v___x_750_);
v___x_753_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_749_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = 0;
v___x_755_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*1, v___x_754_);
v___x_756_ = lean_box(0);
v___x_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_748_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(lean_object* v_00_u03b1_759_, lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1___redArg(lean_object* v_t_763_){
_start:
{
lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___f_764_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_765_ = lean_box(1);
v___x_766_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_763_);
v___x_767_ = l_Std_Format_joinSep___redArg(v___f_764_, v___x_766_, v___x_765_);
v___x_768_ = l_Std_Format_defWidth;
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = l_Std_Format_pretty(v___x_767_, v___x_768_, v___x_769_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1(lean_object* v_00_u03b1_771_, lean_object* v_t_772_){
_start:
{
lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___f_773_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_774_ = lean_box(1);
v___x_775_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_772_);
v___x_776_ = l_Std_Format_joinSep___redArg(v___f_773_, v___x_775_, v___x_774_);
v___x_777_ = l_Std_Format_defWidth;
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = l_Std_Format_pretty(v___x_776_, v___x_777_, v___x_778_, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___redArg___lam__0(lean_object* v_t_780_){
_start:
{
lean_object* v___f_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___f_781_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_782_ = lean_box(1);
v___x_783_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_780_);
v___x_784_ = l_Std_Format_joinSep___redArg(v___f_781_, v___x_783_, v___x_782_);
v___x_785_ = l_Std_Format_defWidth;
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = l_Std_Format_pretty(v___x_784_, v___x_785_, v___x_786_, v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___redArg(){
_start:
{
lean_object* v___f_790_; 
v___f_790_ = ((lean_object*)(l_Lean_Data_Trie_instToString___redArg___closed__0));
return v___f_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___redArg___boxed(lean_object* v___dummy_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Data_Trie_instToString___redArg();
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString(lean_object* v_00_u03b1_793_){
_start:
{
lean_object* v___f_794_; 
v___f_794_ = ((lean_object*)(l_Lean_Data_Trie_instToString___redArg___closed__0));
return v___f_794_;
}
}
lean_object* runtime_initialize_Lean_Data_Format(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Trie(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Trie(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Data_Trie_matchPrefix___auto__1 = _init_l_Lean_Data_Trie_matchPrefix___auto__1();
lean_mark_persistent(l_Lean_Data_Trie_matchPrefix___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Format(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Trie(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Trie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Trie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Trie(builtin);
}
#ifdef __cplusplus
}
#endif
