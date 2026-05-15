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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_ByteArray_toList(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node1_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node1_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Data_Trie_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Data_Trie_empty___closed__0 = (const lean_object*)&l_Lean_Data_Trie_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty(lean_object*);
static lean_once_cell_t l_Lean_Data_Trie_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Data_Trie_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___lam__0(lean_object*);
static const lean_closure_object l_Lean_Data_Trie_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Data_Trie_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Data_Trie_instToString___closed__0 = (const lean_object*)&l_Lean_Data_Trie_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___redArg___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Data_Trie_ctorIdx___redArg(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx(lean_object* v_00_u03b1_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Data_Trie_ctorIdx___redArg(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorIdx___boxed(lean_object* v_00_u03b1_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Data_Trie_ctorIdx(v_00_u03b1_10_, v_x_11_);
lean_dec_ref(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim___redArg(lean_object* v_t_13_, lean_object* v_k_14_){
_start:
{
switch(lean_obj_tag(v_t_13_))
{
case 0:
{
lean_object* v_a_15_; lean_object* v___x_16_; 
v_a_15_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_a_15_);
lean_dec_ref(v_t_13_);
v___x_16_ = lean_apply_1(v_k_14_, v_a_15_);
return v___x_16_;
}
case 1:
{
lean_object* v_a_17_; uint8_t v_a_18_; lean_object* v_a_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_a_17_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_a_17_);
v_a_18_ = lean_ctor_get_uint8(v_t_13_, sizeof(void*)*2);
v_a_19_ = lean_ctor_get(v_t_13_, 1);
lean_inc_ref(v_a_19_);
lean_dec_ref(v_t_13_);
v___x_20_ = lean_box(v_a_18_);
v___x_21_ = lean_apply_3(v_k_14_, v_a_17_, v___x_20_, v_a_19_);
return v___x_21_;
}
default: 
{
lean_object* v_a_22_; lean_object* v_a_23_; lean_object* v_a_24_; lean_object* v___x_25_; 
v_a_22_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_a_22_);
v_a_23_ = lean_ctor_get(v_t_13_, 1);
lean_inc_ref(v_a_23_);
v_a_24_ = lean_ctor_get(v_t_13_, 2);
lean_inc_ref(v_a_24_);
lean_dec_ref(v_t_13_);
v___x_25_ = lean_apply_3(v_k_14_, v_a_22_, v_a_23_, v_a_24_);
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim(lean_object* v_00_u03b1_26_, lean_object* v_motive__1_27_, lean_object* v_ctorIdx_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_29_, v_k_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_ctorElim___boxed(lean_object* v_00_u03b1_33_, lean_object* v_motive__1_34_, lean_object* v_ctorIdx_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_k_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Data_Trie_ctorElim(v_00_u03b1_33_, v_motive__1_34_, v_ctorIdx_35_, v_t_36_, v_h_37_, v_k_38_);
lean_dec(v_ctorIdx_35_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_leaf_elim___redArg(lean_object* v_t_40_, lean_object* v_leaf_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_40_, v_leaf_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_leaf_elim(lean_object* v_00_u03b1_43_, lean_object* v_motive__1_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_leaf_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_45_, v_leaf_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node1_elim___redArg(lean_object* v_t_49_, lean_object* v_node1_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_49_, v_node1_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node1_elim(lean_object* v_00_u03b1_52_, lean_object* v_motive__1_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_node1_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_54_, v_node1_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node_elim___redArg(lean_object* v_t_58_, lean_object* v_node_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_58_, v_node_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_node_elim(lean_object* v_00_u03b1_61_, lean_object* v_motive__1_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_node_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_63_, v_node_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty(lean_object* v_00_u03b1_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = ((lean_object*)(l_Lean_Data_Trie_empty___closed__0));
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Data_Trie_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection(lean_object* v_00_u03b1_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_Lean_Data_Trie_instEmptyCollection___closed__0, &l_Lean_Data_Trie_instEmptyCollection___closed__0_once, _init_l_Lean_Data_Trie_instEmptyCollection___closed__0);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited(lean_object* v_00_u03b1_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&l_Lean_Data_Trie_instEmptyCollection___closed__0, &l_Lean_Data_Trie_instEmptyCollection___closed__0_once, _init_l_Lean_Data_Trie_instEmptyCollection___closed__0);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(lean_object* v_s_76_, lean_object* v_f_77_, lean_object* v_i_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_string_utf8_byte_size(v_s_76_);
v___x_80_ = lean_nat_dec_lt(v_i_78_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v_i_78_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_apply_1(v_f_77_, v___x_81_);
v___x_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
else
{
uint8_t v_c_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v_t_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
lean_inc(v_i_78_);
v_c_85_ = lean_string_get_byte_fast(v_s_76_, v_i_78_);
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_add(v_i_78_, v___x_86_);
lean_dec(v_i_78_);
v_t_88_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_76_, v_f_77_, v___x_87_);
v___x_89_ = lean_box(0);
v___x_90_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v_t_88_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*2, v_c_85_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg___boxed(lean_object* v_s_91_, lean_object* v_f_92_, lean_object* v_i_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_91_, v_f_92_, v_i_93_);
lean_dec_ref(v_s_91_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(lean_object* v_00_u03b1_95_, lean_object* v_s_96_, lean_object* v_f_97_, lean_object* v_i_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_96_, v_f_97_, v_i_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___boxed(lean_object* v_00_u03b1_100_, lean_object* v_s_101_, lean_object* v_f_102_, lean_object* v_i_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(v_00_u03b1_100_, v_s_101_, v_f_102_, v_i_103_);
lean_dec_ref(v_s_101_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(uint8_t v_c_105_, lean_object* v_a_106_, lean_object* v_i_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_byte_array_size(v_a_106_);
v___x_109_ = lean_nat_dec_lt(v_i_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
lean_dec(v_i_107_);
v___x_110_ = lean_box(0);
return v___x_110_;
}
else
{
uint8_t v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_byte_array_fget(v_a_106_, v_i_107_);
v___x_112_ = lean_uint8_dec_eq(v___x_111_, v_c_105_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_add(v_i_107_, v___x_113_);
lean_dec(v_i_107_);
v_i_107_ = v___x_114_;
goto _start;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v_i_107_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0___boxed(lean_object* v_c_117_, lean_object* v_a_118_, lean_object* v_i_119_){
_start:
{
uint8_t v_c_boxed_120_; lean_object* v_res_121_; 
v_c_boxed_120_ = lean_unbox(v_c_117_);
v_res_121_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_boxed_120_, v_a_118_, v_i_119_);
lean_dec_ref(v_a_118_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(lean_object* v_s_122_, lean_object* v_f_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
switch(lean_obj_tag(v_x_125_))
{
case 0:
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_142_; 
v_a_126_ = lean_ctor_get(v_x_125_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_142_ == 0)
{
v___x_128_ = v_x_125_;
v_isShared_129_ = v_isSharedCheck_142_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v_x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_142_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_string_utf8_byte_size(v_s_122_);
v___x_131_ = lean_nat_dec_lt(v_x_124_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
lean_dec(v_x_124_);
v___x_132_ = lean_apply_1(v_f_123_, v_a_126_);
v___x_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_133_);
v___x_135_ = v___x_128_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
else
{
uint8_t v_c_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_t_140_; lean_object* v___x_141_; 
lean_del_object(v___x_128_);
lean_inc(v_x_124_);
v_c_137_ = lean_string_get_byte_fast(v_s_122_, v_x_124_);
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_add(v_x_124_, v___x_138_);
lean_dec(v_x_124_);
v_t_140_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_122_, v_f_123_, v___x_139_);
v___x_141_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_141_, 0, v_a_126_);
lean_ctor_set(v___x_141_, 1, v_t_140_);
lean_ctor_set_uint8(v___x_141_, sizeof(void*)*2, v_c_137_);
return v___x_141_;
}
}
}
case 1:
{
lean_object* v_a_143_; uint8_t v_a_144_; lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_177_; 
v_a_143_ = lean_ctor_get(v_x_125_, 0);
v_a_144_ = lean_ctor_get_uint8(v_x_125_, sizeof(void*)*2);
v_a_145_ = lean_ctor_get(v_x_125_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_177_ == 0)
{
v___x_147_ = v_x_125_;
v_isShared_148_ = v_isSharedCheck_177_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_inc(v_a_143_);
lean_dec(v_x_125_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_177_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_string_utf8_byte_size(v_s_122_);
v___x_150_ = lean_nat_dec_lt(v_x_124_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
lean_dec(v_x_124_);
v___x_151_ = lean_apply_1(v_f_123_, v_a_143_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_152_);
v___x_154_ = v___x_147_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_a_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_155_, sizeof(void*)*2, v_a_144_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
else
{
uint8_t v_c_156_; uint8_t v___x_157_; 
lean_inc(v_x_124_);
v_c_156_ = lean_string_get_byte_fast(v_s_122_, v_x_124_);
v___x_157_ = lean_uint8_dec_eq(v_c_156_, v_a_144_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_t_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
lean_del_object(v___x_147_);
v___x_158_ = lean_unsigned_to_nat(1u);
v___x_159_ = lean_nat_add(v_x_124_, v___x_158_);
lean_dec(v_x_124_);
v_t_160_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_122_, v_f_123_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(2u);
v___x_162_ = lean_mk_empty_array_with_capacity(v___x_161_);
v___x_163_ = lean_box(v_c_156_);
lean_inc_ref(v___x_162_);
v___x_164_ = lean_array_push(v___x_162_, v___x_163_);
v___x_165_ = lean_box(v_a_144_);
v___x_166_ = lean_array_push(v___x_164_, v___x_165_);
v___x_167_ = lean_byte_array_mk(v___x_166_);
v___x_168_ = lean_array_push(v___x_162_, v_t_160_);
v___x_169_ = lean_array_push(v___x_168_, v_a_145_);
v___x_170_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_170_, 0, v_a_143_);
lean_ctor_set(v___x_170_, 1, v___x_167_);
lean_ctor_set(v___x_170_, 2, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_x_124_, v___x_171_);
lean_dec(v_x_124_);
v___x_173_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_122_, v_f_123_, v___x_172_, v_a_145_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v___x_173_);
v___x_175_ = v___x_147_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_143_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_173_);
lean_ctor_set_uint8(v_reuseFailAlloc_176_, sizeof(void*)*2, v_a_144_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
default: 
{
lean_object* v_a_178_; lean_object* v_a_179_; lean_object* v_a_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_a_178_ = lean_ctor_get(v_x_125_, 0);
v_a_179_ = lean_ctor_get(v_x_125_, 1);
v_a_180_ = lean_ctor_get(v_x_125_, 2);
v___x_181_ = lean_string_utf8_byte_size(v_s_122_);
v___x_182_ = lean_nat_dec_lt(v_x_124_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_191_; 
lean_inc_ref(v_a_180_);
lean_inc_ref(v_a_179_);
lean_inc(v_a_178_);
lean_dec(v_x_124_);
v_isSharedCheck_191_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; lean_object* v_unused_193_; lean_object* v_unused_194_; 
v_unused_192_ = lean_ctor_get(v_x_125_, 2);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_x_125_, 1);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_x_125_, 0);
lean_dec(v_unused_194_);
v___x_184_ = v_x_125_;
v_isShared_185_ = v_isSharedCheck_191_;
goto v_resetjp_183_;
}
else
{
lean_dec(v_x_125_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_191_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_186_ = lean_apply_1(v_f_123_, v_a_178_);
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_187_);
v___x_189_ = v___x_184_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_a_179_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_a_180_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
else
{
uint8_t v_c_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
lean_inc(v_x_124_);
v_c_195_ = lean_string_get_byte_fast(v_s_122_, v_x_124_);
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_195_, v_a_179_, v___x_196_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_209_; 
lean_inc_ref(v_a_180_);
lean_inc_ref(v_a_179_);
lean_inc(v_a_178_);
v_isSharedCheck_209_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; lean_object* v_unused_211_; lean_object* v_unused_212_; 
v_unused_210_ = lean_ctor_get(v_x_125_, 2);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_x_125_, 1);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_x_125_, 0);
lean_dec(v_unused_212_);
v___x_199_ = v_x_125_;
v_isShared_200_ = v_isSharedCheck_209_;
goto v_resetjp_198_;
}
else
{
lean_dec(v_x_125_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_209_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_t_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_add(v_x_124_, v___x_201_);
lean_dec(v_x_124_);
v_t_203_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_122_, v_f_123_, v___x_202_);
v___x_204_ = lean_byte_array_push(v_a_179_, v_c_195_);
v___x_205_ = lean_array_push(v_a_180_, v_t_203_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 2, v___x_205_);
lean_ctor_set(v___x_199_, 1, v___x_204_);
v___x_207_ = v___x_199_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_178_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
else
{
lean_object* v_val_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_val_213_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_val_213_);
lean_dec_ref(v___x_197_);
v___x_214_ = lean_array_get_size(v_a_180_);
v___x_215_ = lean_nat_dec_lt(v_val_213_, v___x_214_);
if (v___x_215_ == 0)
{
lean_dec(v_val_213_);
lean_dec(v_x_124_);
lean_dec(v_f_123_);
return v_x_125_;
}
else
{
lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_229_; 
lean_inc_ref(v_a_180_);
lean_inc_ref(v_a_179_);
lean_inc(v_a_178_);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; 
v_unused_230_ = lean_ctor_get(v_x_125_, 2);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_x_125_, 1);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_x_125_, 0);
lean_dec(v_unused_232_);
v___x_217_ = v_x_125_;
v_isShared_218_ = v_isSharedCheck_229_;
goto v_resetjp_216_;
}
else
{
lean_dec(v_x_125_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_229_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_v_221_; lean_object* v___x_222_; lean_object* v_xs_x27_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_add(v_x_124_, v___x_219_);
lean_dec(v_x_124_);
v_v_221_ = lean_array_fget(v_a_180_, v_val_213_);
v___x_222_ = lean_box(0);
v_xs_x27_223_ = lean_array_fset(v_a_180_, v_val_213_, v___x_222_);
v___x_224_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_122_, v_f_123_, v___x_220_, v_v_221_);
v___x_225_ = lean_array_fset(v_xs_x27_223_, v_val_213_, v___x_224_);
lean_dec(v_val_213_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 2, v___x_225_);
v___x_227_ = v___x_217_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_178_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_a_179_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg___boxed(lean_object* v_s_233_, lean_object* v_f_234_, lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_233_, v_f_234_, v_x_235_, v_x_236_);
lean_dec_ref(v_s_233_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(lean_object* v_00_u03b1_238_, lean_object* v_s_239_, lean_object* v_f_240_, lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_239_, v_f_240_, v_x_241_, v_x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___boxed(lean_object* v_00_u03b1_244_, lean_object* v_s_245_, lean_object* v_f_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(v_00_u03b1_244_, v_s_245_, v_f_246_, v_x_247_, v_x_248_);
lean_dec_ref(v_s_245_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg(lean_object* v_t_250_, lean_object* v_s_251_, lean_object* v_f_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_251_, v_f_252_, v___x_253_, v_t_250_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg___boxed(lean_object* v_t_255_, lean_object* v_s_256_, lean_object* v_f_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Data_Trie_upsert___redArg(v_t_255_, v_s_256_, v_f_257_);
lean_dec_ref(v_s_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert(lean_object* v_00_u03b1_259_, lean_object* v_t_260_, lean_object* v_s_261_, lean_object* v_f_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Data_Trie_upsert___redArg(v_t_260_, v_s_261_, v_f_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___boxed(lean_object* v_00_u03b1_264_, lean_object* v_t_265_, lean_object* v_s_266_, lean_object* v_f_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Data_Trie_upsert(v_00_u03b1_264_, v_t_265_, v_s_266_, v_f_267_);
lean_dec_ref(v_s_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0(lean_object* v_val_269_, lean_object* v_x_270_){
_start:
{
lean_inc(v_val_269_);
return v_val_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0___boxed(lean_object* v_val_271_, lean_object* v_x_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Data_Trie_insert___redArg___lam__0(v_val_271_, v_x_272_);
lean_dec(v_x_272_);
lean_dec(v_val_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg(lean_object* v_t_274_, lean_object* v_s_275_, lean_object* v_val_276_){
_start:
{
lean_object* v___f_277_; lean_object* v___x_278_; 
v___f_277_ = lean_alloc_closure((void*)(l_Lean_Data_Trie_insert___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_277_, 0, v_val_276_);
v___x_278_ = l_Lean_Data_Trie_upsert___redArg(v_t_274_, v_s_275_, v___f_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___boxed(lean_object* v_t_279_, lean_object* v_s_280_, lean_object* v_val_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Data_Trie_insert___redArg(v_t_279_, v_s_280_, v_val_281_);
lean_dec_ref(v_s_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert(lean_object* v_00_u03b1_283_, lean_object* v_t_284_, lean_object* v_s_285_, lean_object* v_val_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Data_Trie_insert___redArg(v_t_284_, v_s_285_, v_val_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___boxed(lean_object* v_00_u03b1_288_, lean_object* v_t_289_, lean_object* v_s_290_, lean_object* v_val_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Data_Trie_insert(v_00_u03b1_288_, v_t_289_, v_s_290_, v_val_291_);
lean_dec_ref(v_s_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(lean_object* v_s_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
switch(lean_obj_tag(v_x_295_))
{
case 0:
{
lean_object* v_a_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_a_296_ = lean_ctor_get(v_x_295_, 0);
v___x_297_ = lean_string_utf8_byte_size(v_s_293_);
v___x_298_ = lean_nat_dec_lt(v_x_294_, v___x_297_);
lean_dec(v_x_294_);
if (v___x_298_ == 0)
{
lean_inc(v_a_296_);
return v_a_296_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = lean_box(0);
return v___x_299_;
}
}
case 1:
{
lean_object* v_a_300_; uint8_t v_a_301_; lean_object* v_a_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_a_300_ = lean_ctor_get(v_x_295_, 0);
v_a_301_ = lean_ctor_get_uint8(v_x_295_, sizeof(void*)*2);
v_a_302_ = lean_ctor_get(v_x_295_, 1);
v___x_303_ = lean_string_utf8_byte_size(v_s_293_);
v___x_304_ = lean_nat_dec_lt(v_x_294_, v___x_303_);
if (v___x_304_ == 0)
{
lean_dec(v_x_294_);
lean_inc(v_a_300_);
return v_a_300_;
}
else
{
uint8_t v_c_305_; uint8_t v___x_306_; 
lean_inc(v_x_294_);
v_c_305_ = lean_string_get_byte_fast(v_s_293_, v_x_294_);
v___x_306_ = lean_uint8_dec_eq(v_c_305_, v_a_301_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; 
lean_dec(v_x_294_);
v___x_307_ = lean_box(0);
return v___x_307_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_x_294_, v___x_308_);
lean_dec(v_x_294_);
v_x_294_ = v___x_309_;
v_x_295_ = v_a_302_;
goto _start;
}
}
}
default: 
{
lean_object* v_a_311_; lean_object* v_a_312_; lean_object* v_a_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_a_311_ = lean_ctor_get(v_x_295_, 0);
v_a_312_ = lean_ctor_get(v_x_295_, 1);
v_a_313_ = lean_ctor_get(v_x_295_, 2);
v___x_314_ = lean_string_utf8_byte_size(v_s_293_);
v___x_315_ = lean_nat_dec_lt(v_x_294_, v___x_314_);
if (v___x_315_ == 0)
{
lean_dec(v_x_294_);
lean_inc(v_a_311_);
return v_a_311_;
}
else
{
uint8_t v_c_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_inc(v_x_294_);
v_c_316_ = lean_string_get_byte_fast(v_s_293_, v_x_294_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_316_, v_a_312_, v___x_317_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v___x_319_; 
lean_dec(v_x_294_);
v___x_319_ = lean_box(0);
return v___x_319_;
}
else
{
lean_object* v_val_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_val_320_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_val_320_);
lean_dec_ref(v___x_318_);
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_add(v_x_294_, v___x_321_);
lean_dec(v_x_294_);
v___x_323_ = lean_obj_once(&l_Lean_Data_Trie_instEmptyCollection___closed__0, &l_Lean_Data_Trie_instEmptyCollection___closed__0_once, _init_l_Lean_Data_Trie_instEmptyCollection___closed__0);
v___x_324_ = lean_array_get_borrowed(v___x_323_, v_a_313_, v_val_320_);
lean_dec(v_val_320_);
v_x_294_ = v___x_322_;
v_x_295_ = v___x_324_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg___boxed(lean_object* v_s_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_326_, v_x_327_, v_x_328_);
lean_dec_ref(v_x_328_);
lean_dec_ref(v_s_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(lean_object* v_00_u03b1_330_, lean_object* v_s_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_331_, v_x_332_, v_x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___boxed(lean_object* v_00_u03b1_335_, lean_object* v_s_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(v_00_u03b1_335_, v_s_336_, v_x_337_, v_x_338_);
lean_dec_ref(v_x_338_);
lean_dec_ref(v_s_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg(lean_object* v_t_340_, lean_object* v_s_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_341_, v___x_342_, v_t_340_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg___boxed(lean_object* v_t_344_, lean_object* v_s_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_344_, v_s_345_);
lean_dec_ref(v_s_345_);
lean_dec_ref(v_t_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f(lean_object* v_00_u03b1_347_, lean_object* v_t_348_, lean_object* v_s_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_348_, v_s_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___boxed(lean_object* v_00_u03b1_351_, lean_object* v_t_352_, lean_object* v_s_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Data_Trie_find_x3f(v_00_u03b1_351_, v_t_352_, v_s_353_);
lean_dec_ref(v_s_353_);
lean_dec_ref(v_t_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
switch(lean_obj_tag(v_a_355_))
{
case 0:
{
lean_object* v_a_357_; 
v_a_357_ = lean_ctor_get(v_a_355_, 0);
if (lean_obj_tag(v_a_357_) == 1)
{
lean_object* v_val_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_val_358_ = lean_ctor_get(v_a_357_, 0);
v___x_359_ = lean_box(0);
lean_inc(v_val_358_);
v___x_360_ = lean_array_push(v_a_356_, v_val_358_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_box(0);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v_a_356_);
return v___x_363_;
}
}
case 1:
{
lean_object* v_a_364_; 
v_a_364_ = lean_ctor_get(v_a_355_, 0);
if (lean_obj_tag(v_a_364_) == 1)
{
lean_object* v_a_365_; lean_object* v_val_366_; lean_object* v___x_367_; 
v_a_365_ = lean_ctor_get(v_a_355_, 1);
v_val_366_ = lean_ctor_get(v_a_364_, 0);
lean_inc(v_val_366_);
v___x_367_ = lean_array_push(v_a_356_, v_val_366_);
v_a_355_ = v_a_365_;
v_a_356_ = v___x_367_;
goto _start;
}
else
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v_a_355_, 1);
v_a_355_ = v_a_369_;
goto _start;
}
}
default: 
{
lean_object* v_a_371_; lean_object* v_a_372_; lean_object* v___y_374_; 
v_a_371_ = lean_ctor_get(v_a_355_, 0);
v_a_372_ = lean_ctor_get(v_a_355_, 2);
if (lean_obj_tag(v_a_371_) == 1)
{
lean_object* v_val_388_; lean_object* v___x_389_; 
v_val_388_ = lean_ctor_get(v_a_371_, 0);
lean_inc(v_val_388_);
v___x_389_ = lean_array_push(v_a_356_, v_val_388_);
v___y_374_ = v___x_389_;
goto v___jp_373_;
}
else
{
v___y_374_ = v_a_356_;
goto v___jp_373_;
}
v___jp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_array_get_size(v_a_372_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_nat_dec_lt(v___x_375_, v___x_376_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___y_374_);
return v___x_379_;
}
else
{
uint8_t v___x_380_; 
v___x_380_ = lean_nat_dec_le(v___x_376_, v___x_376_);
if (v___x_380_ == 0)
{
if (v___x_378_ == 0)
{
lean_object* v___x_381_; 
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_377_);
lean_ctor_set(v___x_381_, 1, v___y_374_);
return v___x_381_;
}
else
{
size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; 
v___x_382_ = ((size_t)0ULL);
v___x_383_ = lean_usize_of_nat(v___x_376_);
v___x_384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_a_372_, v___x_382_, v___x_383_, v___x_377_, v___y_374_);
return v___x_384_;
}
}
else
{
size_t v___x_385_; size_t v___x_386_; lean_object* v___x_387_; 
v___x_385_ = ((size_t)0ULL);
v___x_386_ = lean_usize_of_nat(v___x_376_);
v___x_387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_a_372_, v___x_385_, v___x_386_, v___x_377_, v___y_374_);
return v___x_387_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(lean_object* v_as_390_, size_t v_i_391_, size_t v_stop_392_, lean_object* v_b_393_, lean_object* v___y_394_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_eq(v_i_391_, v_stop_392_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_fst_398_; lean_object* v_snd_399_; size_t v___x_400_; size_t v___x_401_; 
v___x_396_ = lean_array_uget_borrowed(v_as_390_, v_i_391_);
v___x_397_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v___x_396_, v___y_394_);
v_fst_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_fst_398_);
v_snd_399_ = lean_ctor_get(v___x_397_, 1);
lean_inc(v_snd_399_);
lean_dec_ref(v___x_397_);
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_add(v_i_391_, v___x_400_);
v_i_391_ = v___x_401_;
v_b_393_ = v_fst_398_;
v___y_394_ = v_snd_399_;
goto _start;
}
else
{
lean_object* v___x_403_; 
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_b_393_);
lean_ctor_set(v___x_403_, 1, v___y_394_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg___boxed(lean_object* v_as_404_, lean_object* v_i_405_, lean_object* v_stop_406_, lean_object* v_b_407_, lean_object* v___y_408_){
_start:
{
size_t v_i_boxed_409_; size_t v_stop_boxed_410_; lean_object* v_res_411_; 
v_i_boxed_409_ = lean_unbox_usize(v_i_405_);
lean_dec(v_i_405_);
v_stop_boxed_410_ = lean_unbox_usize(v_stop_406_);
lean_dec(v_stop_406_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_404_, v_i_boxed_409_, v_stop_boxed_410_, v_b_407_, v___y_408_);
lean_dec_ref(v_as_404_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg___boxed(lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_412_, v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(lean_object* v_00_u03b1_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_416_, v_a_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___boxed(lean_object* v_00_u03b1_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(v_00_u03b1_419_, v_a_420_, v_a_421_);
lean_dec_ref(v_a_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(lean_object* v_00_u03b1_423_, lean_object* v_as_424_, size_t v_i_425_, size_t v_stop_426_, lean_object* v_b_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_424_, v_i_425_, v_stop_426_, v_b_427_, v___y_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___boxed(lean_object* v_00_u03b1_430_, lean_object* v_as_431_, lean_object* v_i_432_, lean_object* v_stop_433_, lean_object* v_b_434_, lean_object* v___y_435_){
_start:
{
size_t v_i_boxed_436_; size_t v_stop_boxed_437_; lean_object* v_res_438_; 
v_i_boxed_436_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_stop_boxed_437_ = lean_unbox_usize(v_stop_433_);
lean_dec(v_stop_433_);
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(v_00_u03b1_430_, v_as_431_, v_i_boxed_436_, v_stop_boxed_437_, v_b_434_, v___y_435_);
lean_dec_ref(v_as_431_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg(lean_object* v_t_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_snd_444_; 
v___x_442_ = ((lean_object*)(l_Lean_Data_Trie_values___redArg___closed__0));
v___x_443_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_t_441_, v___x_442_);
v_snd_444_ = lean_ctor_get(v___x_443_, 1);
lean_inc(v_snd_444_);
lean_dec_ref(v___x_443_);
return v_snd_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg___boxed(lean_object* v_t_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Data_Trie_values___redArg(v_t_445_);
lean_dec_ref(v_t_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values(lean_object* v_00_u03b1_447_, lean_object* v_t_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Data_Trie_values___redArg(v_t_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___boxed(lean_object* v_00_u03b1_450_, lean_object* v_t_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Data_Trie_values(v_00_u03b1_450_, v_t_451_);
lean_dec_ref(v_t_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(lean_object* v_pre_455_, lean_object* v_t_456_, lean_object* v_i_457_){
_start:
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_string_utf8_byte_size(v_pre_455_);
v___x_459_ = lean_nat_dec_lt(v_i_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v_i_457_);
v___x_460_ = l_Lean_Data_Trie_values___redArg(v_t_456_);
return v___x_460_;
}
else
{
uint8_t v_c_461_; 
lean_inc(v_i_457_);
v_c_461_ = lean_string_get_byte_fast(v_pre_455_, v_i_457_);
switch(lean_obj_tag(v_t_456_))
{
case 0:
{
lean_object* v___x_462_; 
lean_dec(v_i_457_);
v___x_462_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_462_;
}
case 1:
{
uint8_t v_a_463_; lean_object* v_a_464_; uint8_t v___x_465_; 
v_a_463_ = lean_ctor_get_uint8(v_t_456_, sizeof(void*)*2);
v_a_464_ = lean_ctor_get(v_t_456_, 1);
v___x_465_ = lean_uint8_dec_eq(v_c_461_, v_a_463_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
lean_dec(v_i_457_);
v___x_466_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_466_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_add(v_i_457_, v___x_467_);
lean_dec(v_i_457_);
v_t_456_ = v_a_464_;
v_i_457_ = v___x_468_;
goto _start;
}
}
default: 
{
lean_object* v_a_470_; lean_object* v_a_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_a_470_ = lean_ctor_get(v_t_456_, 1);
v_a_471_ = lean_ctor_get(v_t_456_, 2);
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_461_, v_a_470_, v___x_472_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v___x_474_; 
lean_dec(v_i_457_);
v___x_474_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_474_;
}
else
{
lean_object* v_val_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_val_475_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_val_475_);
lean_dec_ref(v___x_473_);
v___x_476_ = lean_obj_once(&l_Lean_Data_Trie_instEmptyCollection___closed__0, &l_Lean_Data_Trie_instEmptyCollection___closed__0_once, _init_l_Lean_Data_Trie_instEmptyCollection___closed__0);
v___x_477_ = lean_array_get_borrowed(v___x_476_, v_a_471_, v_val_475_);
lean_dec(v_val_475_);
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_nat_add(v_i_457_, v___x_478_);
lean_dec(v_i_457_);
v_t_456_ = v___x_477_;
v_i_457_ = v___x_479_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___boxed(lean_object* v_pre_481_, lean_object* v_t_482_, lean_object* v_i_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_481_, v_t_482_, v_i_483_);
lean_dec_ref(v_t_482_);
lean_dec_ref(v_pre_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(lean_object* v_00_u03b1_485_, lean_object* v_pre_486_, lean_object* v_t_487_, lean_object* v_i_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_486_, v_t_487_, v_i_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___boxed(lean_object* v_00_u03b1_490_, lean_object* v_pre_491_, lean_object* v_t_492_, lean_object* v_i_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(v_00_u03b1_490_, v_pre_491_, v_t_492_, v_i_493_);
lean_dec_ref(v_t_492_);
lean_dec_ref(v_pre_491_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object* v_t_495_, lean_object* v_pre_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_496_, v_t_495_, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg___boxed(lean_object* v_t_499_, lean_object* v_pre_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_499_, v_pre_500_);
lean_dec_ref(v_pre_500_);
lean_dec_ref(v_t_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix(lean_object* v_00_u03b1_502_, lean_object* v_t_503_, lean_object* v_pre_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_503_, v_pre_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___boxed(lean_object* v_00_u03b1_506_, lean_object* v_t_507_, lean_object* v_pre_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Data_Trie_findPrefix(v_00_u03b1_506_, v_t_507_, v_pre_508_);
lean_dec_ref(v_pre_508_);
lean_dec_ref(v_t_507_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__10));
v___x_537_ = l_Lean_mkAtom(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__12, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__12_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12);
v___x_539_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_540_ = lean_array_push(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_552_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_553_ = lean_array_push(v___x_552_, v___x_551_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_554_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__17, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__17_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17);
v___x_555_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15));
v___x_556_ = lean_box(2);
v___x_557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v___x_555_);
lean_ctor_set(v___x_557_, 2, v___x_554_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__18, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__18_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18);
v___x_559_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__13, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__13_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13);
v___x_560_ = lean_array_push(v___x_559_, v___x_558_);
return v___x_560_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_562_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__19, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__19_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19);
v___x_563_ = lean_array_push(v___x_562_, v___x_561_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_565_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__20, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__20_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20);
v___x_566_ = lean_array_push(v___x_565_, v___x_564_);
return v___x_566_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_568_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__21, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__21_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21);
v___x_569_ = lean_array_push(v___x_568_, v___x_567_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_571_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__22, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__22_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22);
v___x_572_ = lean_array_push(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__23, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__23_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23);
v___x_574_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11));
v___x_575_ = lean_box(2);
v___x_576_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_574_);
lean_ctor_set(v___x_576_, 2, v___x_573_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__24, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__24_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24);
v___x_578_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_579_ = lean_array_push(v___x_578_, v___x_577_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_580_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__25, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__25_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25);
v___x_581_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__9));
v___x_582_ = lean_box(2);
v___x_583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
lean_ctor_set(v___x_583_, 2, v___x_580_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__26, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__26_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26);
v___x_585_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_586_ = lean_array_push(v___x_585_, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__27, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__27_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27);
v___x_588_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7));
v___x_589_ = lean_box(2);
v___x_590_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
lean_ctor_set(v___x_590_, 2, v___x_587_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__28, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__28_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28);
v___x_592_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_593_ = lean_array_push(v___x_592_, v___x_591_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_594_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__29, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__29_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29);
v___x_595_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4));
v___x_596_ = lean_box(2);
v___x_597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_595_);
lean_ctor_set(v___x_597_, 2, v___x_594_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1(void){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__30, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__30_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(lean_object* v_s_599_, lean_object* v_endByte_600_, lean_object* v_x_601_, lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
switch(lean_obj_tag(v_x_601_))
{
case 0:
{
lean_object* v_a_604_; 
lean_dec(v_x_602_);
v_a_604_ = lean_ctor_get(v_x_601_, 0);
if (lean_obj_tag(v_a_604_) == 0)
{
lean_inc(v_x_603_);
return v_x_603_;
}
else
{
lean_inc_ref(v_a_604_);
return v_a_604_;
}
}
case 1:
{
lean_object* v_a_605_; uint8_t v_a_606_; lean_object* v_a_607_; uint8_t v___y_609_; lean_object* v___y_610_; 
v_a_605_ = lean_ctor_get(v_x_601_, 0);
v_a_606_ = lean_ctor_get_uint8(v_x_601_, sizeof(void*)*2);
v_a_607_ = lean_ctor_get(v_x_601_, 1);
if (lean_obj_tag(v_a_605_) == 0)
{
uint8_t v___x_616_; 
v___x_616_ = lean_nat_dec_lt(v_x_602_, v_endByte_600_);
v___y_609_ = v___x_616_;
v___y_610_ = v_x_603_;
goto v___jp_608_;
}
else
{
uint8_t v___x_617_; 
v___x_617_ = lean_nat_dec_lt(v_x_602_, v_endByte_600_);
v___y_609_ = v___x_617_;
v___y_610_ = v_a_605_;
goto v___jp_608_;
}
v___jp_608_:
{
if (v___y_609_ == 0)
{
lean_dec(v_x_602_);
lean_inc(v___y_610_);
return v___y_610_;
}
else
{
uint8_t v_c_611_; uint8_t v___x_612_; 
lean_inc(v_x_602_);
v_c_611_ = lean_string_get_byte_fast(v_s_599_, v_x_602_);
v___x_612_ = lean_uint8_dec_eq(v_c_611_, v_a_606_);
if (v___x_612_ == 0)
{
lean_dec(v_x_602_);
lean_inc(v___y_610_);
return v___y_610_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_add(v_x_602_, v___x_613_);
lean_dec(v_x_602_);
v_x_601_ = v_a_607_;
v_x_602_ = v___x_614_;
v_x_603_ = v___y_610_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_618_; lean_object* v_a_619_; lean_object* v_a_620_; uint8_t v___y_622_; lean_object* v___y_623_; 
v_a_618_ = lean_ctor_get(v_x_601_, 0);
v_a_619_ = lean_ctor_get(v_x_601_, 1);
v_a_620_ = lean_ctor_get(v_x_601_, 2);
if (lean_obj_tag(v_a_618_) == 0)
{
uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_lt(v_x_602_, v_endByte_600_);
v___y_622_ = v___x_633_;
v___y_623_ = v_x_603_;
goto v___jp_621_;
}
else
{
uint8_t v___x_634_; 
v___x_634_ = lean_nat_dec_lt(v_x_602_, v_endByte_600_);
v___y_622_ = v___x_634_;
v___y_623_ = v_a_618_;
goto v___jp_621_;
}
v___jp_621_:
{
if (v___y_622_ == 0)
{
lean_dec(v_x_602_);
lean_inc(v___y_623_);
return v___y_623_;
}
else
{
uint8_t v_c_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_inc(v_x_602_);
v_c_624_ = lean_string_get_byte_fast(v_s_599_, v_x_602_);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_624_, v_a_619_, v___x_625_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_dec(v_x_602_);
lean_inc(v___y_623_);
return v___y_623_;
}
else
{
lean_object* v_val_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_val_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_val_627_);
lean_dec_ref(v___x_626_);
v___x_628_ = lean_obj_once(&l_Lean_Data_Trie_instEmptyCollection___closed__0, &l_Lean_Data_Trie_instEmptyCollection___closed__0_once, _init_l_Lean_Data_Trie_instEmptyCollection___closed__0);
v___x_629_ = lean_array_get_borrowed(v___x_628_, v_a_620_, v_val_627_);
lean_dec(v_val_627_);
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_add(v_x_602_, v___x_630_);
lean_dec(v_x_602_);
v_x_601_ = v___x_629_;
v_x_602_ = v___x_631_;
v_x_603_ = v___y_623_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg___boxed(lean_object* v_s_635_, lean_object* v_endByte_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_635_, v_endByte_636_, v_x_637_, v_x_638_, v_x_639_);
lean_dec(v_x_639_);
lean_dec_ref(v_x_637_);
lean_dec(v_endByte_636_);
lean_dec_ref(v_s_635_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(lean_object* v_00_u03b1_641_, lean_object* v_s_642_, lean_object* v_endByte_643_, lean_object* v_endByte__valid_644_, lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_642_, v_endByte_643_, v_x_645_, v_x_646_, v_x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___boxed(lean_object* v_00_u03b1_649_, lean_object* v_s_650_, lean_object* v_endByte_651_, lean_object* v_endByte__valid_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(v_00_u03b1_649_, v_s_650_, v_endByte_651_, v_endByte__valid_652_, v_x_653_, v_x_654_, v_x_655_);
lean_dec(v_x_655_);
lean_dec_ref(v_x_653_);
lean_dec(v_endByte_651_);
lean_dec_ref(v_s_650_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg(lean_object* v_s_657_, lean_object* v_t_658_, lean_object* v_i_659_, lean_object* v_endByte_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_box(0);
v___x_662_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_657_, v_endByte_660_, v_t_658_, v_i_659_, v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg___boxed(lean_object* v_s_663_, lean_object* v_t_664_, lean_object* v_i_665_, lean_object* v_endByte_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_663_, v_t_664_, v_i_665_, v_endByte_666_);
lean_dec(v_endByte_666_);
lean_dec_ref(v_t_664_);
lean_dec_ref(v_s_663_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix(lean_object* v_00_u03b1_668_, lean_object* v_s_669_, lean_object* v_t_670_, lean_object* v_i_671_, lean_object* v_endByte_672_, lean_object* v_endByte__valid_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_669_, v_t_670_, v_i_671_, v_endByte_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___boxed(lean_object* v_00_u03b1_675_, lean_object* v_s_676_, lean_object* v_t_677_, lean_object* v_i_678_, lean_object* v_endByte_679_, lean_object* v_endByte__valid_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Data_Trie_matchPrefix(v_00_u03b1_675_, v_s_676_, v_t_677_, v_i_678_, v_endByte_679_, v_endByte__valid_680_);
lean_dec(v_endByte_679_);
lean_dec_ref(v_t_677_);
lean_dec_ref(v_s_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(lean_object* v_x_682_, lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
if (lean_obj_tag(v_x_684_) == 0)
{
lean_dec(v_x_682_);
return v_x_683_;
}
else
{
lean_object* v_head_685_; lean_object* v_tail_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v_head_685_ = lean_ctor_get(v_x_684_, 0);
v_tail_686_ = lean_ctor_get(v_x_684_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_x_684_);
if (v_isSharedCheck_695_ == 0)
{
v___x_688_ = v_x_684_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_tail_686_);
lean_inc(v_head_685_);
lean_dec(v_x_684_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
lean_inc(v_x_682_);
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 5);
lean_ctor_set(v___x_688_, 1, v_x_682_);
lean_ctor_set(v___x_688_, 0, v_x_683_);
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_x_683_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_x_682_);
v___x_691_ = v_reuseFailAlloc_694_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; 
v___x_692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v_head_685_);
v_x_683_ = v___x_692_;
v_x_684_ = v_tail_686_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
if (lean_obj_tag(v_x_696_) == 0)
{
lean_object* v___x_698_; 
lean_dec(v_x_697_);
v___x_698_ = lean_box(0);
return v___x_698_;
}
else
{
lean_object* v_tail_699_; 
v_tail_699_ = lean_ctor_get(v_x_696_, 1);
if (lean_obj_tag(v_tail_699_) == 0)
{
lean_object* v_head_700_; 
lean_dec(v_x_697_);
v_head_700_ = lean_ctor_get(v_x_696_, 0);
lean_inc(v_head_700_);
lean_dec_ref(v_x_696_);
return v_head_700_;
}
else
{
lean_object* v_head_701_; lean_object* v___x_702_; 
lean_inc(v_tail_699_);
v_head_701_ = lean_ctor_get(v_x_696_, 0);
lean_inc(v_head_701_);
lean_dec_ref(v_x_696_);
v___x_702_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(v_x_697_, v_head_701_, v_tail_699_);
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
if (lean_obj_tag(v_a_703_) == 0)
{
lean_object* v___x_705_; 
v___x_705_ = lean_array_to_list(v_a_704_);
return v___x_705_;
}
else
{
lean_object* v_head_706_; lean_object* v_tail_707_; lean_object* v___x_708_; 
v_head_706_ = lean_ctor_get(v_a_703_, 0);
lean_inc(v_head_706_);
v_tail_707_ = lean_ctor_get(v_a_703_, 1);
lean_inc(v_tail_707_);
lean_dec_ref(v_a_703_);
v___x_708_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_704_, v_head_706_);
v_a_703_ = v_tail_707_;
v_a_704_ = v___x_708_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(4u);
v___x_711_ = lean_nat_to_int(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed(lean_object* v_c_712_, lean_object* v_t_713_){
_start:
{
uint8_t v_c_boxed_714_; lean_object* v_res_715_; 
v_c_boxed_714_ = lean_unbox(v_c_712_);
v_res_715_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(v_c_boxed_714_, v_t_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(lean_object* v_x_718_){
_start:
{
switch(lean_obj_tag(v_x_718_))
{
case 0:
{
lean_object* v___x_719_; 
lean_dec_ref(v_x_718_);
v___x_719_ = lean_box(0);
return v___x_719_;
}
case 1:
{
uint8_t v_a_720_; lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_a_720_ = lean_ctor_get_uint8(v_x_718_, sizeof(void*)*2);
v_a_721_ = lean_ctor_get(v_x_718_, 1);
lean_inc_ref(v_a_721_);
lean_dec_ref(v_x_718_);
v___x_722_ = lean_uint8_to_nat(v_a_720_);
v___x_723_ = l_Nat_reprFast(v___x_722_);
v___x_724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
v___x_725_ = lean_obj_once(&l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0, &l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once, _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
v___x_726_ = lean_box(1);
v___x_727_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_a_721_);
v___x_728_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_727_, v___x_726_);
v___x_729_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_725_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = 0;
v___x_731_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*1, v___x_730_);
v___x_732_ = lean_box(0);
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_724_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
return v___x_734_;
}
default: 
{
lean_object* v_a_735_; lean_object* v_a_736_; lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_a_735_ = lean_ctor_get(v_x_718_, 1);
lean_inc_ref(v_a_735_);
v_a_736_ = lean_ctor_get(v_x_718_, 2);
lean_inc_ref(v_a_736_);
lean_dec_ref(v_x_718_);
v___f_737_ = lean_alloc_closure((void*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed), 2, 0);
v___x_738_ = l_ByteArray_toList(v_a_735_);
lean_dec_ref(v_a_735_);
v___x_739_ = lean_array_to_list(v_a_736_);
v___x_740_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0));
v___x_741_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_737_, v___x_738_, v___x_739_, v___x_740_);
v___x_742_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(v___x_741_, v___x_740_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(uint8_t v_c_743_, lean_object* v_t_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_745_ = lean_uint8_to_nat(v_c_743_);
v___x_746_ = l_Nat_reprFast(v___x_745_);
v___x_747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
v___x_748_ = lean_obj_once(&l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0, &l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once, _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
v___x_749_ = lean_box(1);
v___x_750_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_744_);
v___x_751_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_750_, v___x_749_);
v___x_752_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_748_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = 0;
v___x_754_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*1, v___x_753_);
v___x_755_ = lean_box(0);
v___x_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_747_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(lean_object* v_00_u03b1_758_, lean_object* v_x_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1___redArg(lean_object* v_t_762_){
_start:
{
lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___f_763_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_764_ = lean_box(1);
v___x_765_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_762_);
v___x_766_ = l_Std_Format_joinSep___redArg(v___f_763_, v___x_765_, v___x_764_);
v___x_767_ = l_Std_Format_defWidth;
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = l_Std_Format_pretty(v___x_766_, v___x_767_, v___x_768_, v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1(lean_object* v_00_u03b1_770_, lean_object* v_t_771_){
_start:
{
lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___f_772_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_773_ = lean_box(1);
v___x_774_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_771_);
v___x_775_ = l_Std_Format_joinSep___redArg(v___f_772_, v___x_774_, v___x_773_);
v___x_776_ = l_Std_Format_defWidth;
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = l_Std_Format_pretty(v___x_775_, v___x_776_, v___x_777_, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___lam__0(lean_object* v_t_779_){
_start:
{
lean_object* v___f_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___f_780_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_781_ = lean_box(1);
v___x_782_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_779_);
v___x_783_ = l_Std_Format_joinSep___redArg(v___f_780_, v___x_782_, v___x_781_);
v___x_784_ = l_Std_Format_defWidth;
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = l_Std_Format_pretty(v___x_783_, v___x_784_, v___x_785_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString(lean_object* v_00_u03b1_788_){
_start:
{
lean_object* v___f_789_; 
v___f_789_ = ((lean_object*)(l_Lean_Data_Trie_instToString___closed__0));
return v___f_789_;
}
}
lean_object* runtime_initialize_Lean_Data_Format(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Trie(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
