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
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_ByteArray_toList(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_t_13_, 1);
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
lean_dec_ref_known(v_t_13_, 2);
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
lean_dec_ref_known(v_t_13_, 3);
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
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty___redArg(){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = ((lean_object*)(l_Lean_Data_Trie_empty___redArg___closed__0));
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty___redArg___boxed(lean_object* v___dummy_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Data_Trie_empty___redArg();
return v_res_72_;
}
}
static lean_object* _init_l_Lean_Data_Trie_empty___closed__0(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Data_Trie_empty___redArg();
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty(lean_object* v_00_u03b1_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection___redArg___boxed(lean_object* v___dummy_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Data_Trie_instEmptyCollection___redArg();
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection(lean_object* v_00_u03b1_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited___redArg(){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited___redArg___boxed(lean_object* v___dummy_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Data_Trie_instInhabited___redArg();
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited(lean_object* v_00_u03b1_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(lean_object* v_s_88_, lean_object* v_f_89_, lean_object* v_i_90_){
_start:
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = lean_string_utf8_byte_size(v_s_88_);
v___x_92_ = lean_nat_dec_lt(v_i_90_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec(v_i_90_);
v___x_93_ = lean_box(0);
v___x_94_ = lean_apply_1(v_f_89_, v___x_93_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
else
{
uint8_t v_c_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_t_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_inc(v_i_90_);
v_c_97_ = lean_string_get_byte_fast(v_s_88_, v_i_90_);
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_nat_add(v_i_90_, v___x_98_);
lean_dec(v_i_90_);
v_t_100_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_88_, v_f_89_, v___x_99_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v_t_100_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*2, v_c_97_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg___boxed(lean_object* v_s_103_, lean_object* v_f_104_, lean_object* v_i_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_103_, v_f_104_, v_i_105_);
lean_dec_ref(v_s_103_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(lean_object* v_00_u03b1_107_, lean_object* v_s_108_, lean_object* v_f_109_, lean_object* v_i_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_108_, v_f_109_, v_i_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___boxed(lean_object* v_00_u03b1_112_, lean_object* v_s_113_, lean_object* v_f_114_, lean_object* v_i_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(v_00_u03b1_112_, v_s_113_, v_f_114_, v_i_115_);
lean_dec_ref(v_s_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(uint8_t v_c_117_, lean_object* v_a_118_, lean_object* v_i_119_){
_start:
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_byte_array_size(v_a_118_);
v___x_121_ = lean_nat_dec_lt(v_i_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
lean_dec(v_i_119_);
v___x_122_ = lean_box(0);
return v___x_122_;
}
else
{
uint8_t v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_byte_array_fget(v_a_118_, v_i_119_);
v___x_124_ = lean_uint8_dec_eq(v___x_123_, v_c_117_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = lean_nat_add(v_i_119_, v___x_125_);
lean_dec(v_i_119_);
v_i_119_ = v___x_126_;
goto _start;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_128_, 0, v_i_119_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0___boxed(lean_object* v_c_129_, lean_object* v_a_130_, lean_object* v_i_131_){
_start:
{
uint8_t v_c_boxed_132_; lean_object* v_res_133_; 
v_c_boxed_132_ = lean_unbox(v_c_129_);
v_res_133_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_boxed_132_, v_a_130_, v_i_131_);
lean_dec_ref(v_a_130_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(lean_object* v_s_134_, lean_object* v_f_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
switch(lean_obj_tag(v_x_137_))
{
case 0:
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_154_; 
v_a_138_ = lean_ctor_get(v_x_137_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_154_ == 0)
{
v___x_140_ = v_x_137_;
v_isShared_141_ = v_isSharedCheck_154_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v_x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_154_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_string_utf8_byte_size(v_s_134_);
v___x_143_ = lean_nat_dec_lt(v_x_136_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
lean_dec(v_x_136_);
v___x_144_ = lean_apply_1(v_f_135_, v_a_138_);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_145_);
v___x_147_ = v___x_140_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
else
{
uint8_t v_c_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_t_152_; lean_object* v___x_153_; 
lean_del_object(v___x_140_);
lean_inc(v_x_136_);
v_c_149_ = lean_string_get_byte_fast(v_s_134_, v_x_136_);
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_add(v_x_136_, v___x_150_);
lean_dec(v_x_136_);
v_t_152_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_134_, v_f_135_, v___x_151_);
v___x_153_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_153_, 0, v_a_138_);
lean_ctor_set(v___x_153_, 1, v_t_152_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*2, v_c_149_);
return v___x_153_;
}
}
}
case 1:
{
lean_object* v_a_155_; uint8_t v_a_156_; lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_189_; 
v_a_155_ = lean_ctor_get(v_x_137_, 0);
v_a_156_ = lean_ctor_get_uint8(v_x_137_, sizeof(void*)*2);
v_a_157_ = lean_ctor_get(v_x_137_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_189_ == 0)
{
v___x_159_ = v_x_137_;
v_isShared_160_ = v_isSharedCheck_189_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_inc(v_a_155_);
lean_dec(v_x_137_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_189_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_string_utf8_byte_size(v_s_134_);
v___x_162_ = lean_nat_dec_lt(v_x_136_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec(v_x_136_);
v___x_163_ = lean_apply_1(v_f_135_, v_a_155_);
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_164_);
v___x_166_ = v___x_159_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_a_157_);
lean_ctor_set_uint8(v_reuseFailAlloc_167_, sizeof(void*)*2, v_a_156_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
else
{
uint8_t v_c_168_; uint8_t v___x_169_; 
lean_inc(v_x_136_);
v_c_168_ = lean_string_get_byte_fast(v_s_134_, v_x_136_);
v___x_169_ = lean_uint8_dec_eq(v_c_168_, v_a_156_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_t_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_del_object(v___x_159_);
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_nat_add(v_x_136_, v___x_170_);
lean_dec(v_x_136_);
v_t_172_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_134_, v_f_135_, v___x_171_);
v___x_173_ = lean_unsigned_to_nat(2u);
v___x_174_ = lean_mk_empty_array_with_capacity(v___x_173_);
v___x_175_ = lean_box(v_c_168_);
lean_inc_ref(v___x_174_);
v___x_176_ = lean_array_push(v___x_174_, v___x_175_);
v___x_177_ = lean_box(v_a_156_);
v___x_178_ = lean_array_push(v___x_176_, v___x_177_);
v___x_179_ = lean_byte_array_mk(v___x_178_);
v___x_180_ = lean_array_push(v___x_174_, v_t_172_);
v___x_181_ = lean_array_push(v___x_180_, v_a_157_);
v___x_182_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_182_, 0, v_a_155_);
lean_ctor_set(v___x_182_, 1, v___x_179_);
lean_ctor_set(v___x_182_, 2, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v_x_136_, v___x_183_);
lean_dec(v_x_136_);
v___x_185_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_134_, v_f_135_, v___x_184_, v_a_157_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___x_185_);
v___x_187_ = v___x_159_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_155_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_188_, sizeof(void*)*2, v_a_156_);
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
default: 
{
lean_object* v_a_190_; lean_object* v_a_191_; lean_object* v_a_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_a_190_ = lean_ctor_get(v_x_137_, 0);
v_a_191_ = lean_ctor_get(v_x_137_, 1);
v_a_192_ = lean_ctor_get(v_x_137_, 2);
v___x_193_ = lean_string_utf8_byte_size(v_s_134_);
v___x_194_ = lean_nat_dec_lt(v_x_136_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_203_; 
lean_inc_ref(v_a_192_);
lean_inc_ref(v_a_191_);
lean_inc(v_a_190_);
lean_dec(v_x_136_);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; lean_object* v_unused_205_; lean_object* v_unused_206_; 
v_unused_204_ = lean_ctor_get(v_x_137_, 2);
lean_dec(v_unused_204_);
v_unused_205_ = lean_ctor_get(v_x_137_, 1);
lean_dec(v_unused_205_);
v_unused_206_ = lean_ctor_get(v_x_137_, 0);
lean_dec(v_unused_206_);
v___x_196_ = v_x_137_;
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
else
{
lean_dec(v_x_137_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_198_ = lean_apply_1(v_f_135_, v_a_190_);
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_199_);
v___x_201_ = v___x_196_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_a_191_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_a_192_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
uint8_t v_c_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_inc(v_x_136_);
v_c_207_ = lean_string_get_byte_fast(v_s_134_, v_x_136_);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_207_, v_a_191_, v___x_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_221_; 
lean_inc_ref(v_a_192_);
lean_inc_ref(v_a_191_);
lean_inc(v_a_190_);
v_isSharedCheck_221_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; lean_object* v_unused_223_; lean_object* v_unused_224_; 
v_unused_222_ = lean_ctor_get(v_x_137_, 2);
lean_dec(v_unused_222_);
v_unused_223_ = lean_ctor_get(v_x_137_, 1);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_x_137_, 0);
lean_dec(v_unused_224_);
v___x_211_ = v_x_137_;
v_isShared_212_ = v_isSharedCheck_221_;
goto v_resetjp_210_;
}
else
{
lean_dec(v_x_137_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_221_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_t_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_add(v_x_136_, v___x_213_);
lean_dec(v_x_136_);
v_t_215_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_134_, v_f_135_, v___x_214_);
v___x_216_ = lean_byte_array_push(v_a_191_, v_c_207_);
v___x_217_ = lean_array_push(v_a_192_, v_t_215_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 2, v___x_217_);
lean_ctor_set(v___x_211_, 1, v___x_216_);
v___x_219_ = v___x_211_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_190_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_val_225_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_209_, 1);
v___x_226_ = lean_array_get_size(v_a_192_);
v___x_227_ = lean_nat_dec_lt(v_val_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_dec(v_val_225_);
lean_dec(v_x_136_);
lean_dec(v_f_135_);
return v_x_137_;
}
else
{
lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_241_; 
lean_inc_ref(v_a_192_);
lean_inc_ref(v_a_191_);
lean_inc(v_a_190_);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; lean_object* v_unused_243_; lean_object* v_unused_244_; 
v_unused_242_ = lean_ctor_get(v_x_137_, 2);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_x_137_, 1);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_x_137_, 0);
lean_dec(v_unused_244_);
v___x_229_ = v_x_137_;
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
else
{
lean_dec(v_x_137_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_v_233_; lean_object* v___x_234_; lean_object* v_xs_x27_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v_x_136_, v___x_231_);
lean_dec(v_x_136_);
v_v_233_ = lean_array_fget(v_a_192_, v_val_225_);
v___x_234_ = lean_box(0);
v_xs_x27_235_ = lean_array_fset(v_a_192_, v_val_225_, v___x_234_);
v___x_236_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_134_, v_f_135_, v___x_232_, v_v_233_);
v___x_237_ = lean_array_fset(v_xs_x27_235_, v_val_225_, v___x_236_);
lean_dec(v_val_225_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 2, v___x_237_);
v___x_239_ = v___x_229_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_190_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_a_191_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg___boxed(lean_object* v_s_245_, lean_object* v_f_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_245_, v_f_246_, v_x_247_, v_x_248_);
lean_dec_ref(v_s_245_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(lean_object* v_00_u03b1_250_, lean_object* v_s_251_, lean_object* v_f_252_, lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_251_, v_f_252_, v_x_253_, v_x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___boxed(lean_object* v_00_u03b1_256_, lean_object* v_s_257_, lean_object* v_f_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(v_00_u03b1_256_, v_s_257_, v_f_258_, v_x_259_, v_x_260_);
lean_dec_ref(v_s_257_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg(lean_object* v_t_262_, lean_object* v_s_263_, lean_object* v_f_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_263_, v_f_264_, v___x_265_, v_t_262_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg___boxed(lean_object* v_t_267_, lean_object* v_s_268_, lean_object* v_f_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Data_Trie_upsert___redArg(v_t_267_, v_s_268_, v_f_269_);
lean_dec_ref(v_s_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert(lean_object* v_00_u03b1_271_, lean_object* v_t_272_, lean_object* v_s_273_, lean_object* v_f_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Data_Trie_upsert___redArg(v_t_272_, v_s_273_, v_f_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___boxed(lean_object* v_00_u03b1_276_, lean_object* v_t_277_, lean_object* v_s_278_, lean_object* v_f_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Data_Trie_upsert(v_00_u03b1_276_, v_t_277_, v_s_278_, v_f_279_);
lean_dec_ref(v_s_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0(lean_object* v_val_281_, lean_object* v_x_282_){
_start:
{
lean_inc(v_val_281_);
return v_val_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0___boxed(lean_object* v_val_283_, lean_object* v_x_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Data_Trie_insert___redArg___lam__0(v_val_283_, v_x_284_);
lean_dec(v_x_284_);
lean_dec(v_val_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg(lean_object* v_t_286_, lean_object* v_s_287_, lean_object* v_val_288_){
_start:
{
lean_object* v___f_289_; lean_object* v___x_290_; 
v___f_289_ = lean_alloc_closure((void*)(l_Lean_Data_Trie_insert___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_289_, 0, v_val_288_);
v___x_290_ = l_Lean_Data_Trie_upsert___redArg(v_t_286_, v_s_287_, v___f_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___boxed(lean_object* v_t_291_, lean_object* v_s_292_, lean_object* v_val_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Data_Trie_insert___redArg(v_t_291_, v_s_292_, v_val_293_);
lean_dec_ref(v_s_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert(lean_object* v_00_u03b1_295_, lean_object* v_t_296_, lean_object* v_s_297_, lean_object* v_val_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Data_Trie_insert___redArg(v_t_296_, v_s_297_, v_val_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___boxed(lean_object* v_00_u03b1_300_, lean_object* v_t_301_, lean_object* v_s_302_, lean_object* v_val_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Data_Trie_insert(v_00_u03b1_300_, v_t_301_, v_s_302_, v_val_303_);
lean_dec_ref(v_s_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(lean_object* v_s_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
switch(lean_obj_tag(v_x_307_))
{
case 0:
{
lean_object* v_a_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_a_308_ = lean_ctor_get(v_x_307_, 0);
v___x_309_ = lean_string_utf8_byte_size(v_s_305_);
v___x_310_ = lean_nat_dec_lt(v_x_306_, v___x_309_);
lean_dec(v_x_306_);
if (v___x_310_ == 0)
{
lean_inc(v_a_308_);
return v_a_308_;
}
else
{
lean_object* v___x_311_; 
v___x_311_ = lean_box(0);
return v___x_311_;
}
}
case 1:
{
lean_object* v_a_312_; uint8_t v_a_313_; lean_object* v_a_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_a_312_ = lean_ctor_get(v_x_307_, 0);
v_a_313_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*2);
v_a_314_ = lean_ctor_get(v_x_307_, 1);
v___x_315_ = lean_string_utf8_byte_size(v_s_305_);
v___x_316_ = lean_nat_dec_lt(v_x_306_, v___x_315_);
if (v___x_316_ == 0)
{
lean_dec(v_x_306_);
lean_inc(v_a_312_);
return v_a_312_;
}
else
{
uint8_t v_c_317_; uint8_t v___x_318_; 
lean_inc(v_x_306_);
v_c_317_ = lean_string_get_byte_fast(v_s_305_, v_x_306_);
v___x_318_ = lean_uint8_dec_eq(v_c_317_, v_a_313_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; 
lean_dec(v_x_306_);
v___x_319_ = lean_box(0);
return v___x_319_;
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_add(v_x_306_, v___x_320_);
lean_dec(v_x_306_);
v_x_306_ = v___x_321_;
v_x_307_ = v_a_314_;
goto _start;
}
}
}
default: 
{
lean_object* v_a_323_; lean_object* v_a_324_; lean_object* v_a_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_a_323_ = lean_ctor_get(v_x_307_, 0);
v_a_324_ = lean_ctor_get(v_x_307_, 1);
v_a_325_ = lean_ctor_get(v_x_307_, 2);
v___x_326_ = lean_string_utf8_byte_size(v_s_305_);
v___x_327_ = lean_nat_dec_lt(v_x_306_, v___x_326_);
if (v___x_327_ == 0)
{
lean_dec(v_x_306_);
lean_inc(v_a_323_);
return v_a_323_;
}
else
{
uint8_t v_c_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_inc(v_x_306_);
v_c_328_ = lean_string_get_byte_fast(v_s_305_, v_x_306_);
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_328_, v_a_324_, v___x_329_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_331_; 
lean_dec(v_x_306_);
v___x_331_ = lean_box(0);
return v___x_331_;
}
else
{
lean_object* v_val_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_val_332_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v___x_330_, 1);
v___x_333_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_add(v_x_306_, v___x_334_);
lean_dec(v_x_306_);
v___x_336_ = lean_array_get_borrowed(v___x_333_, v_a_325_, v_val_332_);
lean_dec(v_val_332_);
v_x_306_ = v___x_335_;
v_x_307_ = v___x_336_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg___boxed(lean_object* v_s_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_338_, v_x_339_, v_x_340_);
lean_dec_ref(v_x_340_);
lean_dec_ref(v_s_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(lean_object* v_00_u03b1_342_, lean_object* v_s_343_, lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_343_, v_x_344_, v_x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___boxed(lean_object* v_00_u03b1_347_, lean_object* v_s_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(v_00_u03b1_347_, v_s_348_, v_x_349_, v_x_350_);
lean_dec_ref(v_x_350_);
lean_dec_ref(v_s_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg(lean_object* v_t_352_, lean_object* v_s_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_353_, v___x_354_, v_t_352_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg___boxed(lean_object* v_t_356_, lean_object* v_s_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_356_, v_s_357_);
lean_dec_ref(v_s_357_);
lean_dec_ref(v_t_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f(lean_object* v_00_u03b1_359_, lean_object* v_t_360_, lean_object* v_s_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_360_, v_s_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___boxed(lean_object* v_00_u03b1_363_, lean_object* v_t_364_, lean_object* v_s_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Data_Trie_find_x3f(v_00_u03b1_363_, v_t_364_, v_s_365_);
lean_dec_ref(v_s_365_);
lean_dec_ref(v_t_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
switch(lean_obj_tag(v_a_367_))
{
case 0:
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v_a_367_, 0);
if (lean_obj_tag(v_a_369_) == 1)
{
lean_object* v_val_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_val_370_ = lean_ctor_get(v_a_369_, 0);
v___x_371_ = lean_box(0);
lean_inc(v_val_370_);
v___x_372_ = lean_array_push(v_a_368_, v_val_370_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_box(0);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v_a_368_);
return v___x_375_;
}
}
case 1:
{
lean_object* v_a_376_; 
v_a_376_ = lean_ctor_get(v_a_367_, 0);
if (lean_obj_tag(v_a_376_) == 1)
{
lean_object* v_a_377_; lean_object* v_val_378_; lean_object* v___x_379_; 
v_a_377_ = lean_ctor_get(v_a_367_, 1);
v_val_378_ = lean_ctor_get(v_a_376_, 0);
lean_inc(v_val_378_);
v___x_379_ = lean_array_push(v_a_368_, v_val_378_);
v_a_367_ = v_a_377_;
v_a_368_ = v___x_379_;
goto _start;
}
else
{
lean_object* v_a_381_; 
v_a_381_ = lean_ctor_get(v_a_367_, 1);
v_a_367_ = v_a_381_;
goto _start;
}
}
default: 
{
lean_object* v_a_383_; lean_object* v_a_384_; lean_object* v___y_386_; 
v_a_383_ = lean_ctor_get(v_a_367_, 0);
v_a_384_ = lean_ctor_get(v_a_367_, 2);
if (lean_obj_tag(v_a_383_) == 1)
{
lean_object* v_val_400_; lean_object* v___x_401_; 
v_val_400_ = lean_ctor_get(v_a_383_, 0);
lean_inc(v_val_400_);
v___x_401_ = lean_array_push(v_a_368_, v_val_400_);
v___y_386_ = v___x_401_;
goto v___jp_385_;
}
else
{
v___y_386_ = v_a_368_;
goto v___jp_385_;
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_array_get_size(v_a_384_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_nat_dec_lt(v___x_387_, v___x_388_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___y_386_);
return v___x_391_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = lean_nat_dec_le(v___x_388_, v___x_388_);
if (v___x_392_ == 0)
{
if (v___x_390_ == 0)
{
lean_object* v___x_393_; 
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_389_);
lean_ctor_set(v___x_393_, 1, v___y_386_);
return v___x_393_;
}
else
{
size_t v___x_394_; size_t v___x_395_; lean_object* v___x_396_; 
v___x_394_ = ((size_t)0ULL);
v___x_395_ = lean_usize_of_nat(v___x_388_);
v___x_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_a_384_, v___x_394_, v___x_395_, v___x_389_, v___y_386_);
return v___x_396_;
}
}
else
{
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_388_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_a_384_, v___x_397_, v___x_398_, v___x_389_, v___y_386_);
return v___x_399_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(lean_object* v_as_402_, size_t v_i_403_, size_t v_stop_404_, lean_object* v_b_405_, lean_object* v___y_406_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = lean_usize_dec_eq(v_i_403_, v_stop_404_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_fst_410_; lean_object* v_snd_411_; size_t v___x_412_; size_t v___x_413_; 
v___x_408_ = lean_array_uget_borrowed(v_as_402_, v_i_403_);
v___x_409_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v___x_408_, v___y_406_);
v_fst_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_fst_410_);
v_snd_411_ = lean_ctor_get(v___x_409_, 1);
lean_inc(v_snd_411_);
lean_dec_ref(v___x_409_);
v___x_412_ = ((size_t)1ULL);
v___x_413_ = lean_usize_add(v_i_403_, v___x_412_);
v_i_403_ = v___x_413_;
v_b_405_ = v_fst_410_;
v___y_406_ = v_snd_411_;
goto _start;
}
else
{
lean_object* v___x_415_; 
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v_b_405_);
lean_ctor_set(v___x_415_, 1, v___y_406_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg___boxed(lean_object* v_as_416_, lean_object* v_i_417_, lean_object* v_stop_418_, lean_object* v_b_419_, lean_object* v___y_420_){
_start:
{
size_t v_i_boxed_421_; size_t v_stop_boxed_422_; lean_object* v_res_423_; 
v_i_boxed_421_ = lean_unbox_usize(v_i_417_);
lean_dec(v_i_417_);
v_stop_boxed_422_ = lean_unbox_usize(v_stop_418_);
lean_dec(v_stop_418_);
v_res_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_416_, v_i_boxed_421_, v_stop_boxed_422_, v_b_419_, v___y_420_);
lean_dec_ref(v_as_416_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg___boxed(lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_424_, v_a_425_);
lean_dec_ref(v_a_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(lean_object* v_00_u03b1_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_428_, v_a_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___boxed(lean_object* v_00_u03b1_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(v_00_u03b1_431_, v_a_432_, v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(lean_object* v_00_u03b1_435_, lean_object* v_as_436_, size_t v_i_437_, size_t v_stop_438_, lean_object* v_b_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_436_, v_i_437_, v_stop_438_, v_b_439_, v___y_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___boxed(lean_object* v_00_u03b1_442_, lean_object* v_as_443_, lean_object* v_i_444_, lean_object* v_stop_445_, lean_object* v_b_446_, lean_object* v___y_447_){
_start:
{
size_t v_i_boxed_448_; size_t v_stop_boxed_449_; lean_object* v_res_450_; 
v_i_boxed_448_ = lean_unbox_usize(v_i_444_);
lean_dec(v_i_444_);
v_stop_boxed_449_ = lean_unbox_usize(v_stop_445_);
lean_dec(v_stop_445_);
v_res_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(v_00_u03b1_442_, v_as_443_, v_i_boxed_448_, v_stop_boxed_449_, v_b_446_, v___y_447_);
lean_dec_ref(v_as_443_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg(lean_object* v_t_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v_snd_456_; 
v___x_454_ = ((lean_object*)(l_Lean_Data_Trie_values___redArg___closed__0));
v___x_455_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_t_453_, v___x_454_);
v_snd_456_ = lean_ctor_get(v___x_455_, 1);
lean_inc(v_snd_456_);
lean_dec_ref(v___x_455_);
return v_snd_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg___boxed(lean_object* v_t_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Data_Trie_values___redArg(v_t_457_);
lean_dec_ref(v_t_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values(lean_object* v_00_u03b1_459_, lean_object* v_t_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Data_Trie_values___redArg(v_t_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___boxed(lean_object* v_00_u03b1_462_, lean_object* v_t_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Data_Trie_values(v_00_u03b1_462_, v_t_463_);
lean_dec_ref(v_t_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(lean_object* v_pre_467_, lean_object* v_t_468_, lean_object* v_i_469_){
_start:
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_string_utf8_byte_size(v_pre_467_);
v___x_471_ = lean_nat_dec_lt(v_i_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
lean_dec(v_i_469_);
v___x_472_ = l_Lean_Data_Trie_values___redArg(v_t_468_);
return v___x_472_;
}
else
{
uint8_t v_c_473_; 
lean_inc(v_i_469_);
v_c_473_ = lean_string_get_byte_fast(v_pre_467_, v_i_469_);
switch(lean_obj_tag(v_t_468_))
{
case 0:
{
lean_object* v___x_474_; 
lean_dec(v_i_469_);
v___x_474_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_474_;
}
case 1:
{
uint8_t v_a_475_; lean_object* v_a_476_; uint8_t v___x_477_; 
v_a_475_ = lean_ctor_get_uint8(v_t_468_, sizeof(void*)*2);
v_a_476_ = lean_ctor_get(v_t_468_, 1);
v___x_477_ = lean_uint8_dec_eq(v_c_473_, v_a_475_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec(v_i_469_);
v___x_478_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_add(v_i_469_, v___x_479_);
lean_dec(v_i_469_);
v_t_468_ = v_a_476_;
v_i_469_ = v___x_480_;
goto _start;
}
}
default: 
{
lean_object* v_a_482_; lean_object* v_a_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_a_482_ = lean_ctor_get(v_t_468_, 1);
v_a_483_ = lean_ctor_get(v_t_468_, 2);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_473_, v_a_482_, v___x_484_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v___x_486_; 
lean_dec(v_i_469_);
v___x_486_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_486_;
}
else
{
lean_object* v_val_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_val_487_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v___x_485_, 1);
v___x_488_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
v___x_489_ = lean_array_get_borrowed(v___x_488_, v_a_483_, v_val_487_);
lean_dec(v_val_487_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_i_469_, v___x_490_);
lean_dec(v_i_469_);
v_t_468_ = v___x_489_;
v_i_469_ = v___x_491_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___boxed(lean_object* v_pre_493_, lean_object* v_t_494_, lean_object* v_i_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_493_, v_t_494_, v_i_495_);
lean_dec_ref(v_t_494_);
lean_dec_ref(v_pre_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(lean_object* v_00_u03b1_497_, lean_object* v_pre_498_, lean_object* v_t_499_, lean_object* v_i_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_498_, v_t_499_, v_i_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___boxed(lean_object* v_00_u03b1_502_, lean_object* v_pre_503_, lean_object* v_t_504_, lean_object* v_i_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(v_00_u03b1_502_, v_pre_503_, v_t_504_, v_i_505_);
lean_dec_ref(v_t_504_);
lean_dec_ref(v_pre_503_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object* v_t_507_, lean_object* v_pre_508_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_508_, v_t_507_, v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg___boxed(lean_object* v_t_511_, lean_object* v_pre_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_511_, v_pre_512_);
lean_dec_ref(v_pre_512_);
lean_dec_ref(v_t_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix(lean_object* v_00_u03b1_514_, lean_object* v_t_515_, lean_object* v_pre_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_515_, v_pre_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___boxed(lean_object* v_00_u03b1_518_, lean_object* v_t_519_, lean_object* v_pre_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Data_Trie_findPrefix(v_00_u03b1_518_, v_t_519_, v_pre_520_);
lean_dec_ref(v_pre_520_);
lean_dec_ref(v_t_519_);
return v_res_521_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__10));
v___x_549_ = l_Lean_mkAtom(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__12, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__12_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12);
v___x_551_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_552_ = lean_array_push(v___x_551_, v___x_550_);
return v___x_552_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_564_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_565_ = lean_array_push(v___x_564_, v___x_563_);
return v___x_565_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_566_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__17, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__17_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17);
v___x_567_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15));
v___x_568_ = lean_box(2);
v___x_569_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
lean_ctor_set(v___x_569_, 2, v___x_566_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__18, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__18_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18);
v___x_571_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__13, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__13_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13);
v___x_572_ = lean_array_push(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_574_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__19, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__19_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19);
v___x_575_ = lean_array_push(v___x_574_, v___x_573_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_577_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__20, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__20_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20);
v___x_578_ = lean_array_push(v___x_577_, v___x_576_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_580_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__21, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__21_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21);
v___x_581_ = lean_array_push(v___x_580_, v___x_579_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_583_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__22, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__22_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22);
v___x_584_ = lean_array_push(v___x_583_, v___x_582_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__23, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__23_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23);
v___x_586_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11));
v___x_587_ = lean_box(2);
v___x_588_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_586_);
lean_ctor_set(v___x_588_, 2, v___x_585_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__24, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__24_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24);
v___x_590_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_591_ = lean_array_push(v___x_590_, v___x_589_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_592_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__25, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__25_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25);
v___x_593_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__9));
v___x_594_ = lean_box(2);
v___x_595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
lean_ctor_set(v___x_595_, 2, v___x_592_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__26, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__26_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26);
v___x_597_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_598_ = lean_array_push(v___x_597_, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_599_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__27, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__27_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27);
v___x_600_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7));
v___x_601_ = lean_box(2);
v___x_602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
lean_ctor_set(v___x_602_, 2, v___x_599_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__28, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__28_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28);
v___x_604_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_605_ = lean_array_push(v___x_604_, v___x_603_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_606_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__29, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__29_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29);
v___x_607_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4));
v___x_608_ = lean_box(2);
v___x_609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
lean_ctor_set(v___x_609_, 2, v___x_606_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1(void){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__30, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__30_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(lean_object* v_s_611_, lean_object* v_endByte_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
switch(lean_obj_tag(v_x_613_))
{
case 0:
{
lean_object* v_a_616_; 
lean_dec(v_x_614_);
v_a_616_ = lean_ctor_get(v_x_613_, 0);
if (lean_obj_tag(v_a_616_) == 0)
{
lean_inc(v_x_615_);
return v_x_615_;
}
else
{
lean_inc_ref(v_a_616_);
return v_a_616_;
}
}
case 1:
{
lean_object* v_a_617_; uint8_t v_a_618_; lean_object* v_a_619_; uint8_t v___y_621_; lean_object* v___y_622_; 
v_a_617_ = lean_ctor_get(v_x_613_, 0);
v_a_618_ = lean_ctor_get_uint8(v_x_613_, sizeof(void*)*2);
v_a_619_ = lean_ctor_get(v_x_613_, 1);
if (lean_obj_tag(v_a_617_) == 0)
{
uint8_t v___x_628_; 
v___x_628_ = lean_nat_dec_lt(v_x_614_, v_endByte_612_);
v___y_621_ = v___x_628_;
v___y_622_ = v_x_615_;
goto v___jp_620_;
}
else
{
uint8_t v___x_629_; 
v___x_629_ = lean_nat_dec_lt(v_x_614_, v_endByte_612_);
v___y_621_ = v___x_629_;
v___y_622_ = v_a_617_;
goto v___jp_620_;
}
v___jp_620_:
{
if (v___y_621_ == 0)
{
lean_dec(v_x_614_);
lean_inc(v___y_622_);
return v___y_622_;
}
else
{
uint8_t v_c_623_; uint8_t v___x_624_; 
lean_inc(v_x_614_);
v_c_623_ = lean_string_get_byte_fast(v_s_611_, v_x_614_);
v___x_624_ = lean_uint8_dec_eq(v_c_623_, v_a_618_);
if (v___x_624_ == 0)
{
lean_dec(v_x_614_);
lean_inc(v___y_622_);
return v___y_622_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_add(v_x_614_, v___x_625_);
lean_dec(v_x_614_);
v_x_613_ = v_a_619_;
v_x_614_ = v___x_626_;
v_x_615_ = v___y_622_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_630_; lean_object* v_a_631_; lean_object* v_a_632_; lean_object* v___x_633_; uint8_t v___y_635_; lean_object* v___y_636_; 
v_a_630_ = lean_ctor_get(v_x_613_, 0);
v_a_631_ = lean_ctor_get(v_x_613_, 1);
v_a_632_ = lean_ctor_get(v_x_613_, 2);
v___x_633_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
if (lean_obj_tag(v_a_630_) == 0)
{
uint8_t v___x_645_; 
v___x_645_ = lean_nat_dec_lt(v_x_614_, v_endByte_612_);
v___y_635_ = v___x_645_;
v___y_636_ = v_x_615_;
goto v___jp_634_;
}
else
{
uint8_t v___x_646_; 
v___x_646_ = lean_nat_dec_lt(v_x_614_, v_endByte_612_);
v___y_635_ = v___x_646_;
v___y_636_ = v_a_630_;
goto v___jp_634_;
}
v___jp_634_:
{
if (v___y_635_ == 0)
{
lean_dec(v_x_614_);
lean_inc(v___y_636_);
return v___y_636_;
}
else
{
uint8_t v_c_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
lean_inc(v_x_614_);
v_c_637_ = lean_string_get_byte_fast(v_s_611_, v_x_614_);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_637_, v_a_631_, v___x_638_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec(v_x_614_);
lean_inc(v___y_636_);
return v___y_636_;
}
else
{
lean_object* v_val_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = lean_array_get_borrowed(v___x_633_, v_a_632_, v_val_640_);
lean_dec(v_val_640_);
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_add(v_x_614_, v___x_642_);
lean_dec(v_x_614_);
v_x_613_ = v___x_641_;
v_x_614_ = v___x_643_;
v_x_615_ = v___y_636_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg___boxed(lean_object* v_s_647_, lean_object* v_endByte_648_, lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_647_, v_endByte_648_, v_x_649_, v_x_650_, v_x_651_);
lean_dec(v_x_651_);
lean_dec_ref(v_x_649_);
lean_dec(v_endByte_648_);
lean_dec_ref(v_s_647_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(lean_object* v_00_u03b1_653_, lean_object* v_s_654_, lean_object* v_endByte_655_, lean_object* v_endByte__valid_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_654_, v_endByte_655_, v_x_657_, v_x_658_, v_x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___boxed(lean_object* v_00_u03b1_661_, lean_object* v_s_662_, lean_object* v_endByte_663_, lean_object* v_endByte__valid_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(v_00_u03b1_661_, v_s_662_, v_endByte_663_, v_endByte__valid_664_, v_x_665_, v_x_666_, v_x_667_);
lean_dec(v_x_667_);
lean_dec_ref(v_x_665_);
lean_dec(v_endByte_663_);
lean_dec_ref(v_s_662_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg(lean_object* v_s_669_, lean_object* v_t_670_, lean_object* v_i_671_, lean_object* v_endByte_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_box(0);
v___x_674_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(v_s_669_, v_endByte_672_, v_t_670_, v_i_671_, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg___boxed(lean_object* v_s_675_, lean_object* v_t_676_, lean_object* v_i_677_, lean_object* v_endByte_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_675_, v_t_676_, v_i_677_, v_endByte_678_);
lean_dec(v_endByte_678_);
lean_dec_ref(v_t_676_);
lean_dec_ref(v_s_675_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix(lean_object* v_00_u03b1_680_, lean_object* v_s_681_, lean_object* v_t_682_, lean_object* v_i_683_, lean_object* v_endByte_684_, lean_object* v_endByte__valid_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_681_, v_t_682_, v_i_683_, v_endByte_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___boxed(lean_object* v_00_u03b1_687_, lean_object* v_s_688_, lean_object* v_t_689_, lean_object* v_i_690_, lean_object* v_endByte_691_, lean_object* v_endByte__valid_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Data_Trie_matchPrefix(v_00_u03b1_687_, v_s_688_, v_t_689_, v_i_690_, v_endByte_691_, v_endByte__valid_692_);
lean_dec(v_endByte_691_);
lean_dec_ref(v_t_689_);
lean_dec_ref(v_s_688_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_696_) == 0)
{
lean_dec(v_x_694_);
return v_x_695_;
}
else
{
lean_object* v_head_697_; lean_object* v_tail_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_707_; 
v_head_697_ = lean_ctor_get(v_x_696_, 0);
v_tail_698_ = lean_ctor_get(v_x_696_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_696_);
if (v_isSharedCheck_707_ == 0)
{
v___x_700_ = v_x_696_;
v_isShared_701_ = v_isSharedCheck_707_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_tail_698_);
lean_inc(v_head_697_);
lean_dec(v_x_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_707_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
lean_inc(v_x_694_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 5);
lean_ctor_set(v___x_700_, 1, v_x_694_);
lean_ctor_set(v___x_700_, 0, v_x_695_);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_x_695_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_x_694_);
v___x_703_ = v_reuseFailAlloc_706_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_head_697_);
v_x_695_ = v___x_704_;
v_x_696_ = v_tail_698_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(lean_object* v_x_708_, lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_708_) == 0)
{
lean_object* v___x_710_; 
lean_dec(v_x_709_);
v___x_710_ = lean_box(0);
return v___x_710_;
}
else
{
lean_object* v_tail_711_; 
v_tail_711_ = lean_ctor_get(v_x_708_, 1);
if (lean_obj_tag(v_tail_711_) == 0)
{
lean_object* v_head_712_; 
lean_dec(v_x_709_);
v_head_712_ = lean_ctor_get(v_x_708_, 0);
lean_inc(v_head_712_);
lean_dec_ref_known(v_x_708_, 2);
return v_head_712_;
}
else
{
lean_object* v_head_713_; lean_object* v___x_714_; 
lean_inc(v_tail_711_);
v_head_713_ = lean_ctor_get(v_x_708_, 0);
lean_inc(v_head_713_);
lean_dec_ref_known(v_x_708_, 2);
v___x_714_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(v_x_709_, v_head_713_, v_tail_711_);
return v___x_714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
if (lean_obj_tag(v_a_715_) == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_array_to_list(v_a_716_);
return v___x_717_;
}
else
{
lean_object* v_head_718_; lean_object* v_tail_719_; lean_object* v___x_720_; 
v_head_718_ = lean_ctor_get(v_a_715_, 0);
lean_inc(v_head_718_);
v_tail_719_ = lean_ctor_get(v_a_715_, 1);
lean_inc(v_tail_719_);
lean_dec_ref_known(v_a_715_, 2);
v___x_720_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_716_, v_head_718_);
v_a_715_ = v_tail_719_;
v_a_716_ = v___x_720_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_unsigned_to_nat(4u);
v___x_723_ = lean_nat_to_int(v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed(lean_object* v_c_724_, lean_object* v_t_725_){
_start:
{
uint8_t v_c_boxed_726_; lean_object* v_res_727_; 
v_c_boxed_726_ = lean_unbox(v_c_724_);
v_res_727_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(v_c_boxed_726_, v_t_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(lean_object* v_x_730_){
_start:
{
switch(lean_obj_tag(v_x_730_))
{
case 0:
{
lean_object* v___x_731_; 
lean_dec_ref_known(v_x_730_, 1);
v___x_731_ = lean_box(0);
return v___x_731_;
}
case 1:
{
uint8_t v_a_732_; lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_a_732_ = lean_ctor_get_uint8(v_x_730_, sizeof(void*)*2);
v_a_733_ = lean_ctor_get(v_x_730_, 1);
lean_inc_ref(v_a_733_);
lean_dec_ref_known(v_x_730_, 2);
v___x_734_ = lean_uint8_to_nat(v_a_732_);
v___x_735_ = l_Nat_reprFast(v___x_734_);
v___x_736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
v___x_737_ = lean_obj_once(&l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0, &l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once, _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
v___x_738_ = lean_box(1);
v___x_739_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_a_733_);
v___x_740_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_739_, v___x_738_);
v___x_741_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_737_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = 0;
v___x_743_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*1, v___x_742_);
v___x_744_ = lean_box(0);
v___x_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_736_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
return v___x_746_;
}
default: 
{
lean_object* v_a_747_; lean_object* v_a_748_; lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_a_747_ = lean_ctor_get(v_x_730_, 1);
lean_inc_ref(v_a_747_);
v_a_748_ = lean_ctor_get(v_x_730_, 2);
lean_inc_ref(v_a_748_);
lean_dec_ref_known(v_x_730_, 3);
v___f_749_ = lean_alloc_closure((void*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed), 2, 0);
v___x_750_ = l_ByteArray_toList(v_a_747_);
lean_dec_ref(v_a_747_);
v___x_751_ = lean_array_to_list(v_a_748_);
v___x_752_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0));
v___x_753_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_749_, v___x_750_, v___x_751_, v___x_752_);
v___x_754_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(v___x_753_, v___x_752_);
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(uint8_t v_c_755_, lean_object* v_t_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_757_ = lean_uint8_to_nat(v_c_755_);
v___x_758_ = l_Nat_reprFast(v___x_757_);
v___x_759_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
v___x_760_ = lean_obj_once(&l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0, &l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once, _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
v___x_761_ = lean_box(1);
v___x_762_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_756_);
v___x_763_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_762_, v___x_761_);
v___x_764_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_760_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = 0;
v___x_766_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*1, v___x_765_);
v___x_767_ = lean_box(0);
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_759_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(lean_object* v_00_u03b1_770_, lean_object* v_x_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1___redArg(lean_object* v_t_774_){
_start:
{
lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___f_775_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_776_ = lean_box(1);
v___x_777_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_774_);
v___x_778_ = l_Std_Format_joinSep___redArg(v___f_775_, v___x_777_, v___x_776_);
v___x_779_ = l_Std_Format_defWidth;
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = l_Std_Format_pretty(v___x_778_, v___x_779_, v___x_780_, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1(lean_object* v_00_u03b1_782_, lean_object* v_t_783_){
_start:
{
lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___f_784_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_785_ = lean_box(1);
v___x_786_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_783_);
v___x_787_ = l_Std_Format_joinSep___redArg(v___f_784_, v___x_786_, v___x_785_);
v___x_788_ = l_Std_Format_defWidth;
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = l_Std_Format_pretty(v___x_787_, v___x_788_, v___x_789_, v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___redArg___lam__0(lean_object* v_t_791_){
_start:
{
lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___f_792_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_793_ = lean_box(1);
v___x_794_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_791_);
v___x_795_ = l_Std_Format_joinSep___redArg(v___f_792_, v___x_794_, v___x_793_);
v___x_796_ = l_Std_Format_defWidth;
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = l_Std_Format_pretty(v___x_795_, v___x_796_, v___x_797_, v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___redArg(){
_start:
{
lean_object* v___f_801_; 
v___f_801_ = ((lean_object*)(l_Lean_Data_Trie_instToString___redArg___closed__0));
return v___f_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___redArg___boxed(lean_object* v___dummy_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Data_Trie_instToString___redArg();
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString(lean_object* v_00_u03b1_804_){
_start:
{
lean_object* v___f_805_; 
v___f_805_ = ((lean_object*)(l_Lean_Data_Trie_instToString___redArg___closed__0));
return v___f_805_;
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
