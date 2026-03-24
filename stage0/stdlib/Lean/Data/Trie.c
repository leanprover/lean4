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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Data_Trie_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Data_Trie_values___redArg___closed__0 = (const lean_object*)&l_Lean_Data_Trie_values___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values(lean_object*, lean_object*);
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
lean_inc(v_a_296_);
lean_dec_ref(v_x_295_);
v___x_297_ = lean_string_utf8_byte_size(v_s_293_);
v___x_298_ = lean_nat_dec_lt(v_x_294_, v___x_297_);
lean_dec(v_x_294_);
if (v___x_298_ == 0)
{
return v_a_296_;
}
else
{
lean_object* v___x_299_; 
lean_dec(v_a_296_);
v___x_299_ = lean_box(0);
return v___x_299_;
}
}
case 1:
{
lean_object* v_a_300_; uint8_t v_a_301_; lean_object* v_a_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_a_300_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_a_300_);
v_a_301_ = lean_ctor_get_uint8(v_x_295_, sizeof(void*)*2);
v_a_302_ = lean_ctor_get(v_x_295_, 1);
lean_inc_ref(v_a_302_);
lean_dec_ref(v_x_295_);
v___x_303_ = lean_string_utf8_byte_size(v_s_293_);
v___x_304_ = lean_nat_dec_lt(v_x_294_, v___x_303_);
if (v___x_304_ == 0)
{
lean_dec_ref(v_a_302_);
lean_dec(v_x_294_);
return v_a_300_;
}
else
{
uint8_t v_c_305_; uint8_t v___x_306_; 
lean_dec(v_a_300_);
lean_inc(v_x_294_);
v_c_305_ = lean_string_get_byte_fast(v_s_293_, v_x_294_);
v___x_306_ = lean_uint8_dec_eq(v_c_305_, v_a_301_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; 
lean_dec_ref(v_a_302_);
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
lean_inc(v_a_311_);
v_a_312_ = lean_ctor_get(v_x_295_, 1);
lean_inc_ref(v_a_312_);
v_a_313_ = lean_ctor_get(v_x_295_, 2);
lean_inc_ref(v_a_313_);
lean_dec_ref(v_x_295_);
v___x_314_ = lean_string_utf8_byte_size(v_s_293_);
v___x_315_ = lean_nat_dec_lt(v_x_294_, v___x_314_);
if (v___x_315_ == 0)
{
lean_dec_ref(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_x_294_);
return v_a_311_;
}
else
{
uint8_t v_c_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_a_311_);
lean_inc(v_x_294_);
v_c_316_ = lean_string_get_byte_fast(v_s_293_, v_x_294_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_316_, v_a_312_, v___x_317_);
lean_dec_ref(v_a_312_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v___x_319_; 
lean_dec_ref(v_a_313_);
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
v___x_324_ = lean_array_get(v___x_323_, v_a_313_, v_val_320_);
lean_dec(v_val_320_);
lean_dec_ref(v_a_313_);
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
lean_inc(v_a_357_);
lean_dec_ref(v_a_355_);
if (lean_obj_tag(v_a_357_) == 1)
{
lean_object* v_val_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_val_358_ = lean_ctor_get(v_a_357_, 0);
lean_inc(v_val_358_);
lean_dec_ref(v_a_357_);
v___x_359_ = lean_box(0);
v___x_360_ = lean_array_push(v_a_356_, v_val_358_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec(v_a_357_);
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
lean_inc_ref(v_a_364_);
v_a_365_ = lean_ctor_get(v_a_355_, 1);
lean_inc_ref(v_a_365_);
lean_dec_ref(v_a_355_);
v_val_366_ = lean_ctor_get(v_a_364_, 0);
lean_inc(v_val_366_);
lean_dec_ref(v_a_364_);
v___x_367_ = lean_array_push(v_a_356_, v_val_366_);
v_a_355_ = v_a_365_;
v_a_356_ = v___x_367_;
goto _start;
}
else
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v_a_355_, 1);
lean_inc_ref(v_a_369_);
lean_dec_ref(v_a_355_);
v_a_355_ = v_a_369_;
goto _start;
}
}
default: 
{
lean_object* v_a_371_; lean_object* v_a_372_; lean_object* v___y_374_; 
v_a_371_ = lean_ctor_get(v_a_355_, 0);
lean_inc(v_a_371_);
v_a_372_ = lean_ctor_get(v_a_355_, 2);
lean_inc_ref(v_a_372_);
lean_dec_ref(v_a_355_);
if (lean_obj_tag(v_a_371_) == 1)
{
lean_object* v_val_388_; lean_object* v___x_389_; 
v_val_388_ = lean_ctor_get(v_a_371_, 0);
lean_inc(v_val_388_);
lean_dec_ref(v_a_371_);
v___x_389_ = lean_array_push(v_a_356_, v_val_388_);
v___y_374_ = v___x_389_;
goto v___jp_373_;
}
else
{
lean_dec(v_a_371_);
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
lean_dec_ref(v_a_372_);
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
lean_dec_ref(v_a_372_);
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
lean_dec_ref(v_a_372_);
return v___x_384_;
}
}
else
{
size_t v___x_385_; size_t v___x_386_; lean_object* v___x_387_; 
v___x_385_ = ((size_t)0ULL);
v___x_386_ = lean_usize_of_nat(v___x_376_);
v___x_387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_a_372_, v___x_385_, v___x_386_, v___x_377_, v___y_374_);
lean_dec_ref(v_a_372_);
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
lean_inc(v___x_396_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(lean_object* v_00_u03b1_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_413_, v_a_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(lean_object* v_00_u03b1_416_, lean_object* v_as_417_, size_t v_i_418_, size_t v_stop_419_, lean_object* v_b_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_417_, v_i_418_, v_stop_419_, v_b_420_, v___y_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___boxed(lean_object* v_00_u03b1_423_, lean_object* v_as_424_, lean_object* v_i_425_, lean_object* v_stop_426_, lean_object* v_b_427_, lean_object* v___y_428_){
_start:
{
size_t v_i_boxed_429_; size_t v_stop_boxed_430_; lean_object* v_res_431_; 
v_i_boxed_429_ = lean_unbox_usize(v_i_425_);
lean_dec(v_i_425_);
v_stop_boxed_430_ = lean_unbox_usize(v_stop_426_);
lean_dec(v_stop_426_);
v_res_431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(v_00_u03b1_423_, v_as_424_, v_i_boxed_429_, v_stop_boxed_430_, v_b_427_, v___y_428_);
lean_dec_ref(v_as_424_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg(lean_object* v_t_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_snd_437_; 
v___x_435_ = ((lean_object*)(l_Lean_Data_Trie_values___redArg___closed__0));
v___x_436_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_t_434_, v___x_435_);
v_snd_437_ = lean_ctor_get(v___x_436_, 1);
lean_inc(v_snd_437_);
lean_dec_ref(v___x_436_);
return v_snd_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values(lean_object* v_00_u03b1_438_, lean_object* v_t_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Data_Trie_values___redArg(v_t_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(lean_object* v_pre_443_, lean_object* v_t_444_, lean_object* v_i_445_){
_start:
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_string_utf8_byte_size(v_pre_443_);
v___x_447_ = lean_nat_dec_lt(v_i_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
lean_dec(v_i_445_);
v___x_448_ = l_Lean_Data_Trie_values___redArg(v_t_444_);
return v___x_448_;
}
else
{
uint8_t v_c_449_; 
lean_inc(v_i_445_);
v_c_449_ = lean_string_get_byte_fast(v_pre_443_, v_i_445_);
switch(lean_obj_tag(v_t_444_))
{
case 0:
{
lean_object* v___x_450_; 
lean_dec_ref(v_t_444_);
lean_dec(v_i_445_);
v___x_450_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_450_;
}
case 1:
{
uint8_t v_a_451_; lean_object* v_a_452_; uint8_t v___x_453_; 
v_a_451_ = lean_ctor_get_uint8(v_t_444_, sizeof(void*)*2);
v_a_452_ = lean_ctor_get(v_t_444_, 1);
lean_inc_ref(v_a_452_);
lean_dec_ref(v_t_444_);
v___x_453_ = lean_uint8_dec_eq(v_c_449_, v_a_451_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_dec_ref(v_a_452_);
lean_dec(v_i_445_);
v___x_454_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_454_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_add(v_i_445_, v___x_455_);
lean_dec(v_i_445_);
v_t_444_ = v_a_452_;
v_i_445_ = v___x_456_;
goto _start;
}
}
default: 
{
lean_object* v_a_458_; lean_object* v_a_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_a_458_ = lean_ctor_get(v_t_444_, 1);
lean_inc_ref(v_a_458_);
v_a_459_ = lean_ctor_get(v_t_444_, 2);
lean_inc_ref(v_a_459_);
lean_dec_ref(v_t_444_);
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_449_, v_a_458_, v___x_460_);
lean_dec_ref(v_a_458_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_462_; 
lean_dec_ref(v_a_459_);
lean_dec(v_i_445_);
v___x_462_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_462_;
}
else
{
lean_object* v_val_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_val_463_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_val_463_);
lean_dec_ref(v___x_461_);
v___x_464_ = lean_obj_once(&l_Lean_Data_Trie_instEmptyCollection___closed__0, &l_Lean_Data_Trie_instEmptyCollection___closed__0_once, _init_l_Lean_Data_Trie_instEmptyCollection___closed__0);
v___x_465_ = lean_array_get(v___x_464_, v_a_459_, v_val_463_);
lean_dec(v_val_463_);
lean_dec_ref(v_a_459_);
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v_i_445_, v___x_466_);
lean_dec(v_i_445_);
v_t_444_ = v___x_465_;
v_i_445_ = v___x_467_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___boxed(lean_object* v_pre_469_, lean_object* v_t_470_, lean_object* v_i_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_469_, v_t_470_, v_i_471_);
lean_dec_ref(v_pre_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(lean_object* v_00_u03b1_473_, lean_object* v_pre_474_, lean_object* v_t_475_, lean_object* v_i_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_474_, v_t_475_, v_i_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___boxed(lean_object* v_00_u03b1_478_, lean_object* v_pre_479_, lean_object* v_t_480_, lean_object* v_i_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(v_00_u03b1_478_, v_pre_479_, v_t_480_, v_i_481_);
lean_dec_ref(v_pre_479_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object* v_t_483_, lean_object* v_pre_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_484_, v_t_483_, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg___boxed(lean_object* v_t_487_, lean_object* v_pre_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_487_, v_pre_488_);
lean_dec_ref(v_pre_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix(lean_object* v_00_u03b1_490_, lean_object* v_t_491_, lean_object* v_pre_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_491_, v_pre_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___boxed(lean_object* v_00_u03b1_494_, lean_object* v_t_495_, lean_object* v_pre_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Data_Trie_findPrefix(v_00_u03b1_494_, v_t_495_, v_pre_496_);
lean_dec_ref(v_pre_496_);
return v_res_497_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__10));
v___x_525_ = l_Lean_mkAtom(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__12, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__12_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12);
v___x_527_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_528_ = lean_array_push(v___x_527_, v___x_526_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_540_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_541_ = lean_array_push(v___x_540_, v___x_539_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__17, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__17_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17);
v___x_543_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15));
v___x_544_ = lean_box(2);
v___x_545_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___x_543_);
lean_ctor_set(v___x_545_, 2, v___x_542_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__18, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__18_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18);
v___x_547_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__13, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__13_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13);
v___x_548_ = lean_array_push(v___x_547_, v___x_546_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_550_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__19, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__19_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19);
v___x_551_ = lean_array_push(v___x_550_, v___x_549_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_553_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__20, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__20_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20);
v___x_554_ = lean_array_push(v___x_553_, v___x_552_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_556_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__21, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__21_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21);
v___x_557_ = lean_array_push(v___x_556_, v___x_555_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_559_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__22, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__22_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22);
v___x_560_ = lean_array_push(v___x_559_, v___x_558_);
return v___x_560_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_561_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__23, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__23_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23);
v___x_562_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11));
v___x_563_ = lean_box(2);
v___x_564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
lean_ctor_set(v___x_564_, 2, v___x_561_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__24, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__24_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24);
v___x_566_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_567_ = lean_array_push(v___x_566_, v___x_565_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_568_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__25, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__25_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25);
v___x_569_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__9));
v___x_570_ = lean_box(2);
v___x_571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v___x_569_);
lean_ctor_set(v___x_571_, 2, v___x_568_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__26, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__26_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26);
v___x_573_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_574_ = lean_array_push(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__27, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__27_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27);
v___x_576_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7));
v___x_577_ = lean_box(2);
v___x_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
lean_ctor_set(v___x_578_, 2, v___x_575_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__28, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__28_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28);
v___x_580_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_581_ = lean_array_push(v___x_580_, v___x_579_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__29, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__29_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29);
v___x_583_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4));
v___x_584_ = lean_box(2);
v___x_585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
lean_ctor_set(v___x_585_, 2, v___x_582_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1(void){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__30, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__30_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(lean_object* v_s_587_, lean_object* v_endByte_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
switch(lean_obj_tag(v_x_589_))
{
case 0:
{
lean_object* v_a_592_; 
lean_dec(v_x_590_);
v_a_592_ = lean_ctor_get(v_x_589_, 0);
lean_inc(v_a_592_);
lean_dec_ref(v_x_589_);
if (lean_obj_tag(v_a_592_) == 0)
{
return v_x_591_;
}
else
{
lean_dec(v_x_591_);
return v_a_592_;
}
}
case 1:
{
lean_object* v_a_593_; uint8_t v_a_594_; lean_object* v_a_595_; uint8_t v___y_597_; lean_object* v___y_598_; 
v_a_593_ = lean_ctor_get(v_x_589_, 0);
lean_inc(v_a_593_);
v_a_594_ = lean_ctor_get_uint8(v_x_589_, sizeof(void*)*2);
v_a_595_ = lean_ctor_get(v_x_589_, 1);
lean_inc_ref(v_a_595_);
lean_dec_ref(v_x_589_);
if (lean_obj_tag(v_a_593_) == 0)
{
uint8_t v___x_604_; 
v___x_604_ = lean_nat_dec_lt(v_x_590_, v_endByte_588_);
v___y_597_ = v___x_604_;
v___y_598_ = v_x_591_;
goto v___jp_596_;
}
else
{
uint8_t v___x_605_; 
lean_dec(v_x_591_);
v___x_605_ = lean_nat_dec_lt(v_x_590_, v_endByte_588_);
v___y_597_ = v___x_605_;
v___y_598_ = v_a_593_;
goto v___jp_596_;
}
v___jp_596_:
{
if (v___y_597_ == 0)
{
lean_dec_ref(v_a_595_);
lean_dec(v_x_590_);
return v___y_598_;
}
else
{
uint8_t v_c_599_; uint8_t v___x_600_; 
lean_inc(v_x_590_);
v_c_599_ = lean_string_get_byte_fast(v_s_587_, v_x_590_);
v___x_600_ = lean_uint8_dec_eq(v_c_599_, v_a_594_);
if (v___x_600_ == 0)
{
lean_dec_ref(v_a_595_);
lean_dec(v_x_590_);
return v___y_598_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_nat_add(v_x_590_, v___x_601_);
lean_dec(v_x_590_);
v_x_589_ = v_a_595_;
v_x_590_ = v___x_602_;
v_x_591_ = v___y_598_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_606_; lean_object* v_a_607_; lean_object* v_a_608_; uint8_t v___y_610_; lean_object* v___y_611_; 
v_a_606_ = lean_ctor_get(v_x_589_, 0);
lean_inc(v_a_606_);
v_a_607_ = lean_ctor_get(v_x_589_, 1);
lean_inc_ref(v_a_607_);
v_a_608_ = lean_ctor_get(v_x_589_, 2);
lean_inc_ref(v_a_608_);
lean_dec_ref(v_x_589_);
if (lean_obj_tag(v_a_606_) == 0)
{
uint8_t v___x_621_; 
v___x_621_ = lean_nat_dec_lt(v_x_590_, v_endByte_588_);
v___y_610_ = v___x_621_;
v___y_611_ = v_x_591_;
goto v___jp_609_;
}
else
{
uint8_t v___x_622_; 
lean_dec(v_x_591_);
v___x_622_ = lean_nat_dec_lt(v_x_590_, v_endByte_588_);
v___y_610_ = v___x_622_;
v___y_611_ = v_a_606_;
goto v___jp_609_;
}
v___jp_609_:
{
if (v___y_610_ == 0)
{
lean_dec_ref(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_x_590_);
return v___y_611_;
}
else
{
uint8_t v_c_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_inc(v_x_590_);
v_c_612_ = lean_string_get_byte_fast(v_s_587_, v_x_590_);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_612_, v_a_607_, v___x_613_);
lean_dec_ref(v_a_607_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_dec_ref(v_a_608_);
lean_dec(v_x_590_);
return v___y_611_;
}
else
{
lean_object* v_val_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_val_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_val_615_);
lean_dec_ref(v___x_614_);
v___x_616_ = lean_obj_once(&l_Lean_Data_Trie_instEmptyCollection___closed__0, &l_Lean_Data_Trie_instEmptyCollection___closed__0_once, _init_l_Lean_Data_Trie_instEmptyCollection___closed__0);
v___x_617_ = lean_array_get(v___x_616_, v_a_608_, v_val_615_);
lean_dec(v_val_615_);
lean_dec_ref(v_a_608_);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_add(v_x_590_, v___x_618_);
lean_dec(v_x_590_);
v_x_589_ = v___x_617_;
v_x_590_ = v___x_619_;
v_x_591_ = v___y_611_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg___boxed(lean_object* v_s_623_, lean_object* v_endByte_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_623_, v_endByte_624_, v_x_625_, v_x_626_, v_x_627_);
lean_dec(v_endByte_624_);
lean_dec_ref(v_s_623_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(lean_object* v_00_u03b1_629_, lean_object* v_s_630_, lean_object* v_endByte_631_, lean_object* v_endByte__valid_632_, lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_630_, v_endByte_631_, v_x_633_, v_x_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___boxed(lean_object* v_00_u03b1_637_, lean_object* v_s_638_, lean_object* v_endByte_639_, lean_object* v_endByte__valid_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(v_00_u03b1_637_, v_s_638_, v_endByte_639_, v_endByte__valid_640_, v_x_641_, v_x_642_, v_x_643_);
lean_dec(v_endByte_639_);
lean_dec_ref(v_s_638_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg(lean_object* v_s_645_, lean_object* v_t_646_, lean_object* v_i_647_, lean_object* v_endByte_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_box(0);
v___x_650_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_645_, v_endByte_648_, v_t_646_, v_i_647_, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg___boxed(lean_object* v_s_651_, lean_object* v_t_652_, lean_object* v_i_653_, lean_object* v_endByte_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_651_, v_t_652_, v_i_653_, v_endByte_654_);
lean_dec(v_endByte_654_);
lean_dec_ref(v_s_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix(lean_object* v_00_u03b1_656_, lean_object* v_s_657_, lean_object* v_t_658_, lean_object* v_i_659_, lean_object* v_endByte_660_, lean_object* v_endByte__valid_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_657_, v_t_658_, v_i_659_, v_endByte_660_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___boxed(lean_object* v_00_u03b1_663_, lean_object* v_s_664_, lean_object* v_t_665_, lean_object* v_i_666_, lean_object* v_endByte_667_, lean_object* v_endByte__valid_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Data_Trie_matchPrefix(v_00_u03b1_663_, v_s_664_, v_t_665_, v_i_666_, v_endByte_667_, v_endByte__valid_668_);
lean_dec(v_endByte_667_);
lean_dec_ref(v_s_664_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
if (lean_obj_tag(v_x_672_) == 0)
{
lean_dec(v_x_670_);
return v_x_671_;
}
else
{
lean_object* v_head_673_; lean_object* v_tail_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_683_; 
v_head_673_ = lean_ctor_get(v_x_672_, 0);
v_tail_674_ = lean_ctor_get(v_x_672_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_672_);
if (v_isSharedCheck_683_ == 0)
{
v___x_676_ = v_x_672_;
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_tail_674_);
lean_inc(v_head_673_);
lean_dec(v_x_672_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
lean_inc(v_x_670_);
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 5);
lean_ctor_set(v___x_676_, 1, v_x_670_);
lean_ctor_set(v___x_676_, 0, v_x_671_);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_x_671_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_x_670_);
v___x_679_ = v_reuseFailAlloc_682_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; 
v___x_680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v_head_673_);
v_x_671_ = v___x_680_;
v_x_672_ = v_tail_674_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
if (lean_obj_tag(v_x_684_) == 0)
{
lean_object* v___x_686_; 
lean_dec(v_x_685_);
v___x_686_ = lean_box(0);
return v___x_686_;
}
else
{
lean_object* v_tail_687_; 
v_tail_687_ = lean_ctor_get(v_x_684_, 1);
if (lean_obj_tag(v_tail_687_) == 0)
{
lean_object* v_head_688_; 
lean_dec(v_x_685_);
v_head_688_ = lean_ctor_get(v_x_684_, 0);
lean_inc(v_head_688_);
lean_dec_ref(v_x_684_);
return v_head_688_;
}
else
{
lean_object* v_head_689_; lean_object* v___x_690_; 
lean_inc(v_tail_687_);
v_head_689_ = lean_ctor_get(v_x_684_, 0);
lean_inc(v_head_689_);
lean_dec_ref(v_x_684_);
v___x_690_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(v_x_685_, v_head_689_, v_tail_687_);
return v___x_690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
if (lean_obj_tag(v_a_691_) == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_array_to_list(v_a_692_);
return v___x_693_;
}
else
{
lean_object* v_head_694_; lean_object* v_tail_695_; lean_object* v___x_696_; 
v_head_694_ = lean_ctor_get(v_a_691_, 0);
lean_inc(v_head_694_);
v_tail_695_ = lean_ctor_get(v_a_691_, 1);
lean_inc(v_tail_695_);
lean_dec_ref(v_a_691_);
v___x_696_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_692_, v_head_694_);
v_a_691_ = v_tail_695_;
v_a_692_ = v___x_696_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_unsigned_to_nat(4u);
v___x_699_ = lean_nat_to_int(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed(lean_object* v_c_700_, lean_object* v_t_701_){
_start:
{
uint8_t v_c_boxed_702_; lean_object* v_res_703_; 
v_c_boxed_702_ = lean_unbox(v_c_700_);
v_res_703_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(v_c_boxed_702_, v_t_701_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(lean_object* v_x_706_){
_start:
{
switch(lean_obj_tag(v_x_706_))
{
case 0:
{
lean_object* v___x_707_; 
lean_dec_ref(v_x_706_);
v___x_707_ = lean_box(0);
return v___x_707_;
}
case 1:
{
uint8_t v_a_708_; lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_a_708_ = lean_ctor_get_uint8(v_x_706_, sizeof(void*)*2);
v_a_709_ = lean_ctor_get(v_x_706_, 1);
lean_inc_ref(v_a_709_);
lean_dec_ref(v_x_706_);
v___x_710_ = lean_uint8_to_nat(v_a_708_);
v___x_711_ = l_Nat_reprFast(v___x_710_);
v___x_712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
v___x_713_ = lean_obj_once(&l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0, &l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once, _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
v___x_714_ = lean_box(1);
v___x_715_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_a_709_);
v___x_716_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_715_, v___x_714_);
v___x_717_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_713_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = 0;
v___x_719_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*1, v___x_718_);
v___x_720_ = lean_box(0);
v___x_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_712_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
return v___x_722_;
}
default: 
{
lean_object* v_a_723_; lean_object* v_a_724_; lean_object* v___f_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_a_723_ = lean_ctor_get(v_x_706_, 1);
lean_inc_ref(v_a_723_);
v_a_724_ = lean_ctor_get(v_x_706_, 2);
lean_inc_ref(v_a_724_);
lean_dec_ref(v_x_706_);
v___f_725_ = lean_alloc_closure((void*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed), 2, 0);
v___x_726_ = l_ByteArray_toList(v_a_723_);
lean_dec_ref(v_a_723_);
v___x_727_ = lean_array_to_list(v_a_724_);
v___x_728_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0));
v___x_729_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_725_, v___x_726_, v___x_727_, v___x_728_);
v___x_730_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(v___x_729_, v___x_728_);
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(uint8_t v_c_731_, lean_object* v_t_732_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_733_ = lean_uint8_to_nat(v_c_731_);
v___x_734_ = l_Nat_reprFast(v___x_733_);
v___x_735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
v___x_736_ = lean_obj_once(&l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0, &l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once, _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
v___x_737_ = lean_box(1);
v___x_738_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_732_);
v___x_739_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_738_, v___x_737_);
v___x_740_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_736_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = 0;
v___x_742_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set_uint8(v___x_742_, sizeof(void*)*1, v___x_741_);
v___x_743_ = lean_box(0);
v___x_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_735_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(lean_object* v_00_u03b1_746_, lean_object* v_x_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1___redArg(lean_object* v_t_750_){
_start:
{
lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___f_751_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_752_ = lean_box(1);
v___x_753_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_750_);
v___x_754_ = l_Std_Format_joinSep___redArg(v___f_751_, v___x_753_, v___x_752_);
v___x_755_ = l_Std_Format_defWidth;
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = l_Std_Format_pretty(v___x_754_, v___x_755_, v___x_756_, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1(lean_object* v_00_u03b1_758_, lean_object* v_t_759_){
_start:
{
lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___f_760_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_761_ = lean_box(1);
v___x_762_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_759_);
v___x_763_ = l_Std_Format_joinSep___redArg(v___f_760_, v___x_762_, v___x_761_);
v___x_764_ = l_Std_Format_defWidth;
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = l_Std_Format_pretty(v___x_763_, v___x_764_, v___x_765_, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___lam__0(lean_object* v_t_767_){
_start:
{
lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___f_768_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_769_ = lean_box(1);
v___x_770_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_767_);
v___x_771_ = l_Std_Format_joinSep___redArg(v___f_768_, v___x_770_, v___x_769_);
v___x_772_ = l_Std_Format_defWidth;
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = l_Std_Format_pretty(v___x_771_, v___x_772_, v___x_773_, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString(lean_object* v_00_u03b1_776_){
_start:
{
lean_object* v___f_777_; 
v___f_777_ = ((lean_object*)(l_Lean_Data_Trie_instToString___closed__0));
return v___f_777_;
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
