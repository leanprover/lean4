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
lean_object* l_Lean_Data_Trie_empty___redArg(){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = ((lean_object*)(l_Lean_Data_Trie_empty___redArg___closed__0));
return v___x_68_;
}
}
LEAN_EXPORT void l_Lean_Data_Trie_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_69_;
v_res_69_ = l_Lean_Data_Trie_empty___redArg();
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty___redArg___boxed(lean_object* v___dummy_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Data_Trie_empty___redArg();
return v_res_71_;
}
}
static lean_object* _init_l_Lean_Data_Trie_empty___closed__0(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Data_Trie_empty___redArg();
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty(lean_object* v_00_u03b1_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_74_;
}
}
lean_object* l_Lean_Data_Trie_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_76_;
}
}
LEAN_EXPORT void l_Lean_Data_Trie_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_77_;
v_res_77_ = l_Lean_Data_Trie_instEmptyCollection___redArg();
stack->m_obj
 = v_res_77_;
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
lean_object* l_Lean_Data_Trie_instInhabited___redArg(){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_83_;
}
}
LEAN_EXPORT void l_Lean_Data_Trie_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_84_;
v_res_84_ = l_Lean_Data_Trie_instInhabited___redArg();
stack->m_obj
 = v_res_84_;
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited___redArg___boxed(lean_object* v___dummy_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Data_Trie_instInhabited___redArg();
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited(lean_object* v_00_u03b1_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(lean_object* v_s_89_, lean_object* v_f_90_, lean_object* v_i_91_){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = lean_string_utf8_byte_size(v_s_89_);
v___x_93_ = lean_nat_dec_lt(v_i_91_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v_i_91_);
v___x_94_ = lean_box(0);
v___x_95_ = lean_apply_1(v_f_90_, v___x_94_);
v___x_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
else
{
uint8_t v_c_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v_t_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
lean_inc(v_i_91_);
v_c_98_ = lean_string_get_byte_fast(v_s_89_, v_i_91_);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_i_91_, v___x_99_);
lean_dec(v_i_91_);
v_t_101_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_89_, v_f_90_, v___x_100_);
v___x_102_ = lean_box(0);
v___x_103_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_t_101_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*2, v_c_98_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg___boxed(lean_object* v_s_104_, lean_object* v_f_105_, lean_object* v_i_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_104_, v_f_105_, v_i_106_);
lean_dec_ref(v_s_104_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(lean_object* v_00_u03b1_108_, lean_object* v_s_109_, lean_object* v_f_110_, lean_object* v_i_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_109_, v_f_110_, v_i_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___boxed(lean_object* v_00_u03b1_113_, lean_object* v_s_114_, lean_object* v_f_115_, lean_object* v_i_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(v_00_u03b1_113_, v_s_114_, v_f_115_, v_i_116_);
lean_dec_ref(v_s_114_);
return v_res_117_;
}
}
lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(uint8_t v_c_118_, lean_object* v_a_119_, lean_object* v_i_120_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_byte_array_size(v_a_119_);
v___x_122_ = lean_nat_dec_lt(v_i_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
lean_dec(v_i_120_);
v___x_123_ = lean_box(0);
return v___x_123_;
}
else
{
uint8_t v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_byte_array_fget(v_a_119_, v_i_120_);
v___x_125_ = lean_uint8_dec_eq(v___x_124_, v_c_118_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_add(v_i_120_, v___x_126_);
lean_dec(v_i_120_);
v_i_120_ = v___x_127_;
goto _start;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v_i_120_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT void l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_118_ = stack[0].m_num;
lean_object* v_a_119_ = stack[1].m_obj;
lean_object* v_i_120_ = stack[2].m_obj;
lean_object* v_res_130_;
v_res_130_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_118_, v_a_119_, v_i_120_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0___boxed(lean_object* v_c_131_, lean_object* v_a_132_, lean_object* v_i_133_){
_start:
{
uint8_t v_c_boxed_134_; lean_object* v_res_135_; 
v_c_boxed_134_ = lean_unbox(v_c_131_);
v_res_135_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_boxed_134_, v_a_132_, v_i_133_);
lean_dec_ref(v_a_132_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(lean_object* v_s_136_, lean_object* v_f_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
switch(lean_obj_tag(v_x_139_))
{
case 0:
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_156_; 
v_a_140_ = lean_ctor_get(v_x_139_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_139_);
if (v_isSharedCheck_156_ == 0)
{
v___x_142_ = v_x_139_;
v_isShared_143_ = v_isSharedCheck_156_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v_x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_156_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lean_string_utf8_byte_size(v_s_136_);
v___x_145_ = lean_nat_dec_lt(v_x_138_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec(v_x_138_);
v___x_146_ = lean_apply_1(v_f_137_, v_a_140_);
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_147_);
v___x_149_ = v___x_142_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
uint8_t v_c_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_t_154_; lean_object* v___x_155_; 
lean_del_object(v___x_142_);
lean_inc(v_x_138_);
v_c_151_ = lean_string_get_byte_fast(v_s_136_, v_x_138_);
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_nat_add(v_x_138_, v___x_152_);
lean_dec(v_x_138_);
v_t_154_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_136_, v_f_137_, v___x_153_);
v___x_155_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_155_, 0, v_a_140_);
lean_ctor_set(v___x_155_, 1, v_t_154_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*2, v_c_151_);
return v___x_155_;
}
}
}
case 1:
{
lean_object* v_a_157_; uint8_t v_a_158_; lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_191_; 
v_a_157_ = lean_ctor_get(v_x_139_, 0);
v_a_158_ = lean_ctor_get_uint8(v_x_139_, sizeof(void*)*2);
v_a_159_ = lean_ctor_get(v_x_139_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_x_139_);
if (v_isSharedCheck_191_ == 0)
{
v___x_161_ = v_x_139_;
v_isShared_162_ = v_isSharedCheck_191_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_inc(v_a_157_);
lean_dec(v_x_139_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_191_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_string_utf8_byte_size(v_s_136_);
v___x_164_ = lean_nat_dec_lt(v_x_138_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
lean_dec(v_x_138_);
v___x_165_ = lean_apply_1(v_f_137_, v_a_157_);
v___x_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_166_);
v___x_168_ = v___x_161_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_a_159_);
lean_ctor_set_uint8(v_reuseFailAlloc_169_, sizeof(void*)*2, v_a_158_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
else
{
uint8_t v_c_170_; uint8_t v___x_171_; 
lean_inc(v_x_138_);
v_c_170_ = lean_string_get_byte_fast(v_s_136_, v_x_138_);
v___x_171_ = lean_uint8_dec_eq(v_c_170_, v_a_158_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_t_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_del_object(v___x_161_);
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_nat_add(v_x_138_, v___x_172_);
lean_dec(v_x_138_);
v_t_174_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_136_, v_f_137_, v___x_173_);
v___x_175_ = lean_unsigned_to_nat(2u);
v___x_176_ = lean_mk_empty_array_with_capacity(v___x_175_);
v___x_177_ = lean_box(v_c_170_);
lean_inc_ref(v___x_176_);
v___x_178_ = lean_array_push(v___x_176_, v___x_177_);
v___x_179_ = lean_box(v_a_158_);
v___x_180_ = lean_array_push(v___x_178_, v___x_179_);
v___x_181_ = lean_byte_array_mk(v___x_180_);
v___x_182_ = lean_array_push(v___x_176_, v_t_174_);
v___x_183_ = lean_array_push(v___x_182_, v_a_159_);
v___x_184_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_184_, 0, v_a_157_);
lean_ctor_set(v___x_184_, 1, v___x_181_);
lean_ctor_set(v___x_184_, 2, v___x_183_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_add(v_x_138_, v___x_185_);
lean_dec(v_x_138_);
v___x_187_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_136_, v_f_137_, v___x_186_, v_a_159_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_187_);
v___x_189_ = v___x_161_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_157_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_190_, sizeof(void*)*2, v_a_158_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
default: 
{
lean_object* v_a_192_; lean_object* v_a_193_; lean_object* v_a_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_a_192_ = lean_ctor_get(v_x_139_, 0);
v_a_193_ = lean_ctor_get(v_x_139_, 1);
v_a_194_ = lean_ctor_get(v_x_139_, 2);
v___x_195_ = lean_string_utf8_byte_size(v_s_136_);
v___x_196_ = lean_nat_dec_lt(v_x_138_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_205_; 
lean_inc_ref(v_a_194_);
lean_inc_ref(v_a_193_);
lean_inc(v_a_192_);
lean_dec(v_x_138_);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_139_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; lean_object* v_unused_207_; lean_object* v_unused_208_; 
v_unused_206_ = lean_ctor_get(v_x_139_, 2);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_x_139_, 1);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_x_139_, 0);
lean_dec(v_unused_208_);
v___x_198_ = v_x_139_;
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
else
{
lean_dec(v_x_139_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_200_ = lean_apply_1(v_f_137_, v_a_192_);
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_201_);
v___x_203_ = v___x_198_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_a_193_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_a_194_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
uint8_t v_c_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
lean_inc(v_x_138_);
v_c_209_ = lean_string_get_byte_fast(v_s_136_, v_x_138_);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_209_, v_a_193_, v___x_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_223_; 
lean_inc_ref(v_a_194_);
lean_inc_ref(v_a_193_);
lean_inc(v_a_192_);
v_isSharedCheck_223_ = !lean_is_exclusive(v_x_139_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; lean_object* v_unused_225_; lean_object* v_unused_226_; 
v_unused_224_ = lean_ctor_get(v_x_139_, 2);
lean_dec(v_unused_224_);
v_unused_225_ = lean_ctor_get(v_x_139_, 1);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_x_139_, 0);
lean_dec(v_unused_226_);
v___x_213_ = v_x_139_;
v_isShared_214_ = v_isSharedCheck_223_;
goto v_resetjp_212_;
}
else
{
lean_dec(v_x_139_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_223_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_t_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_x_138_, v___x_215_);
lean_dec(v_x_138_);
v_t_217_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_136_, v_f_137_, v___x_216_);
v___x_218_ = lean_byte_array_push(v_a_193_, v_c_209_);
v___x_219_ = lean_array_push(v_a_194_, v_t_217_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 2, v___x_219_);
lean_ctor_set(v___x_213_, 1, v___x_218_);
v___x_221_ = v___x_213_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_192_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v_val_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_val_227_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_211_, 1);
v___x_228_ = lean_array_get_size(v_a_194_);
v___x_229_ = lean_nat_dec_lt(v_val_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_dec(v_val_227_);
lean_dec(v_x_138_);
lean_dec(v_f_137_);
return v_x_139_;
}
else
{
lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_243_; 
lean_inc_ref(v_a_194_);
lean_inc_ref(v_a_193_);
lean_inc(v_a_192_);
v_isSharedCheck_243_ = !lean_is_exclusive(v_x_139_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; lean_object* v_unused_245_; lean_object* v_unused_246_; 
v_unused_244_ = lean_ctor_get(v_x_139_, 2);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_x_139_, 1);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_x_139_, 0);
lean_dec(v_unused_246_);
v___x_231_ = v_x_139_;
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
else
{
lean_dec(v_x_139_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_v_235_; lean_object* v___x_236_; lean_object* v_xs_x27_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_x_138_, v___x_233_);
lean_dec(v_x_138_);
v_v_235_ = lean_array_fget(v_a_194_, v_val_227_);
v___x_236_ = lean_box(0);
v_xs_x27_237_ = lean_array_fset(v_a_194_, v_val_227_, v___x_236_);
v___x_238_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_136_, v_f_137_, v___x_234_, v_v_235_);
v___x_239_ = lean_array_fset(v_xs_x27_237_, v_val_227_, v___x_238_);
lean_dec(v_val_227_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 2, v___x_239_);
v___x_241_ = v___x_231_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_192_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_a_193_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg___boxed(lean_object* v_s_247_, lean_object* v_f_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_247_, v_f_248_, v_x_249_, v_x_250_);
lean_dec_ref(v_s_247_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(lean_object* v_00_u03b1_252_, lean_object* v_s_253_, lean_object* v_f_254_, lean_object* v_x_255_, lean_object* v_x_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_253_, v_f_254_, v_x_255_, v_x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___boxed(lean_object* v_00_u03b1_258_, lean_object* v_s_259_, lean_object* v_f_260_, lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(v_00_u03b1_258_, v_s_259_, v_f_260_, v_x_261_, v_x_262_);
lean_dec_ref(v_s_259_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg(lean_object* v_t_264_, lean_object* v_s_265_, lean_object* v_f_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(v_s_265_, v_f_266_, v___x_267_, v_t_264_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg___boxed(lean_object* v_t_269_, lean_object* v_s_270_, lean_object* v_f_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Data_Trie_upsert___redArg(v_t_269_, v_s_270_, v_f_271_);
lean_dec_ref(v_s_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert(lean_object* v_00_u03b1_273_, lean_object* v_t_274_, lean_object* v_s_275_, lean_object* v_f_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Data_Trie_upsert___redArg(v_t_274_, v_s_275_, v_f_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___boxed(lean_object* v_00_u03b1_278_, lean_object* v_t_279_, lean_object* v_s_280_, lean_object* v_f_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Data_Trie_upsert(v_00_u03b1_278_, v_t_279_, v_s_280_, v_f_281_);
lean_dec_ref(v_s_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0(lean_object* v_val_283_, lean_object* v_x_284_){
_start:
{
lean_inc(v_val_283_);
return v_val_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0___boxed(lean_object* v_val_285_, lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Data_Trie_insert___redArg___lam__0(v_val_285_, v_x_286_);
lean_dec(v_x_286_);
lean_dec(v_val_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg(lean_object* v_t_288_, lean_object* v_s_289_, lean_object* v_val_290_){
_start:
{
lean_object* v___f_291_; lean_object* v___x_292_; 
v___f_291_ = lean_alloc_closure((void*)(l_Lean_Data_Trie_insert___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_291_, 0, v_val_290_);
v___x_292_ = l_Lean_Data_Trie_upsert___redArg(v_t_288_, v_s_289_, v___f_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___boxed(lean_object* v_t_293_, lean_object* v_s_294_, lean_object* v_val_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Data_Trie_insert___redArg(v_t_293_, v_s_294_, v_val_295_);
lean_dec_ref(v_s_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert(lean_object* v_00_u03b1_297_, lean_object* v_t_298_, lean_object* v_s_299_, lean_object* v_val_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Data_Trie_insert___redArg(v_t_298_, v_s_299_, v_val_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___boxed(lean_object* v_00_u03b1_302_, lean_object* v_t_303_, lean_object* v_s_304_, lean_object* v_val_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Data_Trie_insert(v_00_u03b1_302_, v_t_303_, v_s_304_, v_val_305_);
lean_dec_ref(v_s_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(lean_object* v_s_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
switch(lean_obj_tag(v_x_309_))
{
case 0:
{
lean_object* v_a_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_a_310_ = lean_ctor_get(v_x_309_, 0);
v___x_311_ = lean_string_utf8_byte_size(v_s_307_);
v___x_312_ = lean_nat_dec_lt(v_x_308_, v___x_311_);
lean_dec(v_x_308_);
if (v___x_312_ == 0)
{
lean_inc(v_a_310_);
return v_a_310_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = lean_box(0);
return v___x_313_;
}
}
case 1:
{
lean_object* v_a_314_; uint8_t v_a_315_; lean_object* v_a_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_a_314_ = lean_ctor_get(v_x_309_, 0);
v_a_315_ = lean_ctor_get_uint8(v_x_309_, sizeof(void*)*2);
v_a_316_ = lean_ctor_get(v_x_309_, 1);
v___x_317_ = lean_string_utf8_byte_size(v_s_307_);
v___x_318_ = lean_nat_dec_lt(v_x_308_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v_x_308_);
lean_inc(v_a_314_);
return v_a_314_;
}
else
{
uint8_t v_c_319_; uint8_t v___x_320_; 
lean_inc(v_x_308_);
v_c_319_ = lean_string_get_byte_fast(v_s_307_, v_x_308_);
v___x_320_ = lean_uint8_dec_eq(v_c_319_, v_a_315_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
lean_dec(v_x_308_);
v___x_321_ = lean_box(0);
return v___x_321_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_x_308_, v___x_322_);
lean_dec(v_x_308_);
v_x_308_ = v___x_323_;
v_x_309_ = v_a_316_;
goto _start;
}
}
}
default: 
{
lean_object* v_a_325_; lean_object* v_a_326_; lean_object* v_a_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_a_325_ = lean_ctor_get(v_x_309_, 0);
v_a_326_ = lean_ctor_get(v_x_309_, 1);
v_a_327_ = lean_ctor_get(v_x_309_, 2);
v___x_328_ = lean_string_utf8_byte_size(v_s_307_);
v___x_329_ = lean_nat_dec_lt(v_x_308_, v___x_328_);
if (v___x_329_ == 0)
{
lean_dec(v_x_308_);
lean_inc(v_a_325_);
return v_a_325_;
}
else
{
uint8_t v_c_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_inc(v_x_308_);
v_c_330_ = lean_string_get_byte_fast(v_s_307_, v_x_308_);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_330_, v_a_326_, v___x_331_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v___x_333_; 
lean_dec(v_x_308_);
v___x_333_ = lean_box(0);
return v___x_333_;
}
else
{
lean_object* v_val_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_val_334_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v___x_332_, 1);
v___x_335_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_add(v_x_308_, v___x_336_);
lean_dec(v_x_308_);
v___x_338_ = lean_array_get_borrowed(v___x_335_, v_a_327_, v_val_334_);
lean_dec(v_val_334_);
v_x_308_ = v___x_337_;
v_x_309_ = v___x_338_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg___boxed(lean_object* v_s_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_340_, v_x_341_, v_x_342_);
lean_dec_ref(v_x_342_);
lean_dec_ref(v_s_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(lean_object* v_00_u03b1_344_, lean_object* v_s_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_345_, v_x_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___boxed(lean_object* v_00_u03b1_349_, lean_object* v_s_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(v_00_u03b1_349_, v_s_350_, v_x_351_, v_x_352_);
lean_dec_ref(v_x_352_);
lean_dec_ref(v_s_350_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg(lean_object* v_t_354_, lean_object* v_s_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(v_s_355_, v___x_356_, v_t_354_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg___boxed(lean_object* v_t_358_, lean_object* v_s_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_358_, v_s_359_);
lean_dec_ref(v_s_359_);
lean_dec_ref(v_t_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f(lean_object* v_00_u03b1_361_, lean_object* v_t_362_, lean_object* v_s_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_362_, v_s_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___boxed(lean_object* v_00_u03b1_365_, lean_object* v_t_366_, lean_object* v_s_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Data_Trie_find_x3f(v_00_u03b1_365_, v_t_366_, v_s_367_);
lean_dec_ref(v_s_367_);
lean_dec_ref(v_t_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
switch(lean_obj_tag(v_a_369_))
{
case 0:
{
lean_object* v_a_371_; 
v_a_371_ = lean_ctor_get(v_a_369_, 0);
if (lean_obj_tag(v_a_371_) == 1)
{
lean_object* v_val_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_val_372_ = lean_ctor_get(v_a_371_, 0);
v___x_373_ = lean_box(0);
lean_inc(v_val_372_);
v___x_374_ = lean_array_push(v_a_370_, v_val_372_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_box(0);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v_a_370_);
return v___x_377_;
}
}
case 1:
{
lean_object* v_a_378_; 
v_a_378_ = lean_ctor_get(v_a_369_, 0);
if (lean_obj_tag(v_a_378_) == 1)
{
lean_object* v_a_379_; lean_object* v_val_380_; lean_object* v___x_381_; 
v_a_379_ = lean_ctor_get(v_a_369_, 1);
v_val_380_ = lean_ctor_get(v_a_378_, 0);
lean_inc(v_val_380_);
v___x_381_ = lean_array_push(v_a_370_, v_val_380_);
v_a_369_ = v_a_379_;
v_a_370_ = v___x_381_;
goto _start;
}
else
{
lean_object* v_a_383_; 
v_a_383_ = lean_ctor_get(v_a_369_, 1);
v_a_369_ = v_a_383_;
goto _start;
}
}
default: 
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v___y_388_; 
v_a_385_ = lean_ctor_get(v_a_369_, 0);
v_a_386_ = lean_ctor_get(v_a_369_, 2);
if (lean_obj_tag(v_a_385_) == 1)
{
lean_object* v_val_402_; lean_object* v___x_403_; 
v_val_402_ = lean_ctor_get(v_a_385_, 0);
lean_inc(v_val_402_);
v___x_403_ = lean_array_push(v_a_370_, v_val_402_);
v___y_388_ = v___x_403_;
goto v___jp_387_;
}
else
{
v___y_388_ = v_a_370_;
goto v___jp_387_;
}
v___jp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = lean_array_get_size(v_a_386_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_nat_dec_lt(v___x_389_, v___x_390_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_391_);
lean_ctor_set(v___x_393_, 1, v___y_388_);
return v___x_393_;
}
else
{
uint8_t v___x_394_; 
v___x_394_ = lean_nat_dec_le(v___x_390_, v___x_390_);
if (v___x_394_ == 0)
{
if (v___x_392_ == 0)
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_391_);
lean_ctor_set(v___x_395_, 1, v___y_388_);
return v___x_395_;
}
else
{
size_t v___x_396_; size_t v___x_397_; lean_object* v___x_398_; 
v___x_396_ = ((size_t)0ULL);
v___x_397_ = lean_usize_of_nat(v___x_390_);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_a_386_, v___x_396_, v___x_397_, v___x_391_, v___y_388_);
return v___x_398_;
}
}
else
{
size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; 
v___x_399_ = ((size_t)0ULL);
v___x_400_ = lean_usize_of_nat(v___x_390_);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_a_386_, v___x_399_, v___x_400_, v___x_391_, v___y_388_);
return v___x_401_;
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(lean_object* v_as_404_, size_t v_i_405_, size_t v_stop_406_, lean_object* v_b_407_, lean_object* v___y_408_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = lean_usize_dec_eq(v_i_405_, v_stop_406_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_fst_412_; lean_object* v_snd_413_; size_t v___x_414_; size_t v___x_415_; 
v___x_410_ = lean_array_uget_borrowed(v_as_404_, v_i_405_);
v___x_411_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v___x_410_, v___y_408_);
v_fst_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_fst_412_);
v_snd_413_ = lean_ctor_get(v___x_411_, 1);
lean_inc(v_snd_413_);
lean_dec_ref(v___x_411_);
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_405_, v___x_414_);
v_i_405_ = v___x_415_;
v_b_407_ = v_fst_412_;
v___y_408_ = v_snd_413_;
goto _start;
}
else
{
lean_object* v___x_417_; 
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_b_407_);
lean_ctor_set(v___x_417_, 1, v___y_408_);
return v___x_417_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_404_ = stack[0].m_obj;
size_t v_i_405_ = stack[1].m_num;
size_t v_stop_406_ = stack[2].m_num;
lean_object* v_b_407_ = stack[3].m_obj;
lean_object* v___y_408_ = stack[4].m_obj;
lean_object* v_res_418_;
v_res_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_404_, v_i_405_, v_stop_406_, v_b_407_, v___y_408_);
stack->m_obj
 = v_res_418_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg___boxed(lean_object* v_as_419_, lean_object* v_i_420_, lean_object* v_stop_421_, lean_object* v_b_422_, lean_object* v___y_423_){
_start:
{
size_t v_i_boxed_424_; size_t v_stop_boxed_425_; lean_object* v_res_426_; 
v_i_boxed_424_ = lean_unbox_usize(v_i_420_);
lean_dec(v_i_420_);
v_stop_boxed_425_ = lean_unbox_usize(v_stop_421_);
lean_dec(v_stop_421_);
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_419_, v_i_boxed_424_, v_stop_boxed_425_, v_b_422_, v___y_423_);
lean_dec_ref(v_as_419_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg___boxed(lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_427_, v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(lean_object* v_00_u03b1_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_431_, v_a_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___boxed(lean_object* v_00_u03b1_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(v_00_u03b1_434_, v_a_435_, v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_437_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(lean_object* v_00_u03b1_438_, lean_object* v_as_439_, size_t v_i_440_, size_t v_stop_441_, lean_object* v_b_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_439_, v_i_440_, v_stop_441_, v_b_442_, v___y_443_);
return v___x_444_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_439_ = stack[1].m_obj;
size_t v_i_440_ = stack[2].m_num;
size_t v_stop_441_ = stack[3].m_num;
lean_object* v_b_442_ = stack[4].m_obj;
lean_object* v___y_443_ = stack[5].m_obj;
lean_object* v_res_445_;
v_res_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(lean_box(0), v_as_439_, v_i_440_, v_stop_441_, v_b_442_, v___y_443_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___boxed(lean_object* v_00_u03b1_446_, lean_object* v_as_447_, lean_object* v_i_448_, lean_object* v_stop_449_, lean_object* v_b_450_, lean_object* v___y_451_){
_start:
{
size_t v_i_boxed_452_; size_t v_stop_boxed_453_; lean_object* v_res_454_; 
v_i_boxed_452_ = lean_unbox_usize(v_i_448_);
lean_dec(v_i_448_);
v_stop_boxed_453_ = lean_unbox_usize(v_stop_449_);
lean_dec(v_stop_449_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(v_00_u03b1_446_, v_as_447_, v_i_boxed_452_, v_stop_boxed_453_, v_b_450_, v___y_451_);
lean_dec_ref(v_as_447_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg(lean_object* v_t_457_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v_snd_460_; 
v___x_458_ = ((lean_object*)(l_Lean_Data_Trie_values___redArg___closed__0));
v___x_459_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_t_457_, v___x_458_);
v_snd_460_ = lean_ctor_get(v___x_459_, 1);
lean_inc(v_snd_460_);
lean_dec_ref(v___x_459_);
return v_snd_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg___boxed(lean_object* v_t_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Data_Trie_values___redArg(v_t_461_);
lean_dec_ref(v_t_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values(lean_object* v_00_u03b1_463_, lean_object* v_t_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Data_Trie_values___redArg(v_t_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___boxed(lean_object* v_00_u03b1_466_, lean_object* v_t_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Data_Trie_values(v_00_u03b1_466_, v_t_467_);
lean_dec_ref(v_t_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(lean_object* v_pre_471_, lean_object* v_t_472_, lean_object* v_i_473_){
_start:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_string_utf8_byte_size(v_pre_471_);
v___x_475_ = lean_nat_dec_lt(v_i_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_dec(v_i_473_);
v___x_476_ = l_Lean_Data_Trie_values___redArg(v_t_472_);
return v___x_476_;
}
else
{
uint8_t v_c_477_; 
lean_inc(v_i_473_);
v_c_477_ = lean_string_get_byte_fast(v_pre_471_, v_i_473_);
switch(lean_obj_tag(v_t_472_))
{
case 0:
{
lean_object* v___x_478_; 
lean_dec(v_i_473_);
v___x_478_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_478_;
}
case 1:
{
uint8_t v_a_479_; lean_object* v_a_480_; uint8_t v___x_481_; 
v_a_479_ = lean_ctor_get_uint8(v_t_472_, sizeof(void*)*2);
v_a_480_ = lean_ctor_get(v_t_472_, 1);
v___x_481_ = lean_uint8_dec_eq(v_c_477_, v_a_479_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
lean_dec(v_i_473_);
v___x_482_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_482_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_i_473_, v___x_483_);
lean_dec(v_i_473_);
v_t_472_ = v_a_480_;
v_i_473_ = v___x_484_;
goto _start;
}
}
default: 
{
lean_object* v_a_486_; lean_object* v_a_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_a_486_ = lean_ctor_get(v_t_472_, 1);
v_a_487_ = lean_ctor_get(v_t_472_, 2);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_477_, v_a_486_, v___x_488_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v___x_490_; 
lean_dec(v_i_473_);
v___x_490_ = ((lean_object*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0));
return v___x_490_;
}
else
{
lean_object* v_val_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_val_491_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_val_491_);
lean_dec_ref_known(v___x_489_, 1);
v___x_492_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
v___x_493_ = lean_array_get_borrowed(v___x_492_, v_a_487_, v_val_491_);
lean_dec(v_val_491_);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_add(v_i_473_, v___x_494_);
lean_dec(v_i_473_);
v_t_472_ = v___x_493_;
v_i_473_ = v___x_495_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___boxed(lean_object* v_pre_497_, lean_object* v_t_498_, lean_object* v_i_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_497_, v_t_498_, v_i_499_);
lean_dec_ref(v_t_498_);
lean_dec_ref(v_pre_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(lean_object* v_00_u03b1_501_, lean_object* v_pre_502_, lean_object* v_t_503_, lean_object* v_i_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_502_, v_t_503_, v_i_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___boxed(lean_object* v_00_u03b1_506_, lean_object* v_pre_507_, lean_object* v_t_508_, lean_object* v_i_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(v_00_u03b1_506_, v_pre_507_, v_t_508_, v_i_509_);
lean_dec_ref(v_t_508_);
lean_dec_ref(v_pre_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object* v_t_511_, lean_object* v_pre_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(v_pre_512_, v_t_511_, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg___boxed(lean_object* v_t_515_, lean_object* v_pre_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_515_, v_pre_516_);
lean_dec_ref(v_pre_516_);
lean_dec_ref(v_t_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix(lean_object* v_00_u03b1_518_, lean_object* v_t_519_, lean_object* v_pre_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_519_, v_pre_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___boxed(lean_object* v_00_u03b1_522_, lean_object* v_t_523_, lean_object* v_pre_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Data_Trie_findPrefix(v_00_u03b1_522_, v_t_523_, v_pre_524_);
lean_dec_ref(v_pre_524_);
lean_dec_ref(v_t_523_);
return v_res_525_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__10));
v___x_553_ = l_Lean_mkAtom(v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__12, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__12_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12);
v___x_555_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_556_ = lean_array_push(v___x_555_, v___x_554_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_568_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_569_ = lean_array_push(v___x_568_, v___x_567_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__17, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__17_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17);
v___x_571_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15));
v___x_572_ = lean_box(2);
v___x_573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_571_);
lean_ctor_set(v___x_573_, 2, v___x_570_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__18, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__18_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18);
v___x_575_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__13, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__13_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13);
v___x_576_ = lean_array_push(v___x_575_, v___x_574_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_578_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__19, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__19_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19);
v___x_579_ = lean_array_push(v___x_578_, v___x_577_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_581_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__20, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__20_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20);
v___x_582_ = lean_array_push(v___x_581_, v___x_580_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_584_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__21, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__21_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21);
v___x_585_ = lean_array_push(v___x_584_, v___x_583_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16));
v___x_587_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__22, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__22_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22);
v___x_588_ = lean_array_push(v___x_587_, v___x_586_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_589_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__23, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__23_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23);
v___x_590_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11));
v___x_591_ = lean_box(2);
v___x_592_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_590_);
lean_ctor_set(v___x_592_, 2, v___x_589_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__24, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__24_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24);
v___x_594_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_595_ = lean_array_push(v___x_594_, v___x_593_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_596_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__25, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__25_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25);
v___x_597_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__9));
v___x_598_ = lean_box(2);
v___x_599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___x_597_);
lean_ctor_set(v___x_599_, 2, v___x_596_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__26, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__26_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26);
v___x_601_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_602_ = lean_array_push(v___x_601_, v___x_600_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_603_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__27, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__27_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27);
v___x_604_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7));
v___x_605_ = lean_box(2);
v___x_606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
lean_ctor_set(v___x_606_, 2, v___x_603_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__28, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__28_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28);
v___x_608_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5));
v___x_609_ = lean_array_push(v___x_608_, v___x_607_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_610_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__29, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__29_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29);
v___x_611_ = ((lean_object*)(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4));
v___x_612_ = lean_box(2);
v___x_613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
lean_ctor_set(v___x_613_, 2, v___x_610_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Data_Trie_matchPrefix___auto__1(void){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Lean_Data_Trie_matchPrefix___auto__1___closed__30, &l_Lean_Data_Trie_matchPrefix___auto__1___closed__30_once, _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(lean_object* v_s_615_, lean_object* v_endByte_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
switch(lean_obj_tag(v_x_617_))
{
case 0:
{
lean_object* v_a_620_; 
lean_dec(v_x_618_);
v_a_620_ = lean_ctor_get(v_x_617_, 0);
if (lean_obj_tag(v_a_620_) == 0)
{
lean_inc(v_x_619_);
return v_x_619_;
}
else
{
lean_inc_ref(v_a_620_);
return v_a_620_;
}
}
case 1:
{
lean_object* v_a_621_; uint8_t v_a_622_; lean_object* v_a_623_; lean_object* v___y_625_; 
v_a_621_ = lean_ctor_get(v_x_617_, 0);
v_a_622_ = lean_ctor_get_uint8(v_x_617_, sizeof(void*)*2);
v_a_623_ = lean_ctor_get(v_x_617_, 1);
if (lean_obj_tag(v_a_621_) == 0)
{
v___y_625_ = v_x_619_;
goto v___jp_624_;
}
else
{
v___y_625_ = v_a_621_;
goto v___jp_624_;
}
v___jp_624_:
{
uint8_t v___x_626_; 
v___x_626_ = lean_nat_dec_lt(v_x_618_, v_endByte_616_);
if (v___x_626_ == 0)
{
lean_dec(v_x_618_);
lean_inc(v___y_625_);
return v___y_625_;
}
else
{
uint8_t v_c_627_; uint8_t v___x_628_; 
lean_inc(v_x_618_);
v_c_627_ = lean_string_get_byte_fast(v_s_615_, v_x_618_);
v___x_628_ = lean_uint8_dec_eq(v_c_627_, v_a_622_);
if (v___x_628_ == 0)
{
lean_dec(v_x_618_);
lean_inc(v___y_625_);
return v___y_625_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_add(v_x_618_, v___x_629_);
lean_dec(v_x_618_);
v_x_617_ = v_a_623_;
v_x_618_ = v___x_630_;
v_x_619_ = v___y_625_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_632_; lean_object* v_a_633_; lean_object* v_a_634_; lean_object* v___x_635_; lean_object* v___y_637_; 
v_a_632_ = lean_ctor_get(v_x_617_, 0);
v_a_633_ = lean_ctor_get(v_x_617_, 1);
v_a_634_ = lean_ctor_get(v_x_617_, 2);
v___x_635_ = lean_obj_once(&l_Lean_Data_Trie_empty___closed__0, &l_Lean_Data_Trie_empty___closed__0_once, _init_l_Lean_Data_Trie_empty___closed__0);
if (lean_obj_tag(v_a_632_) == 0)
{
v___y_637_ = v_x_619_;
goto v___jp_636_;
}
else
{
v___y_637_ = v_a_632_;
goto v___jp_636_;
}
v___jp_636_:
{
uint8_t v___x_638_; 
v___x_638_ = lean_nat_dec_lt(v_x_618_, v_endByte_616_);
if (v___x_638_ == 0)
{
lean_dec(v_x_618_);
lean_inc(v___y_637_);
return v___y_637_;
}
else
{
uint8_t v_c_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_inc(v_x_618_);
v_c_639_ = lean_string_get_byte_fast(v_s_615_, v_x_618_);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_639_, v_a_633_, v___x_640_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_dec(v_x_618_);
lean_inc(v___y_637_);
return v___y_637_;
}
else
{
lean_object* v_val_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_val_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_643_ = lean_array_get_borrowed(v___x_635_, v_a_634_, v_val_642_);
lean_dec(v_val_642_);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_add(v_x_618_, v___x_644_);
lean_dec(v_x_618_);
v_x_617_ = v___x_643_;
v_x_618_ = v___x_645_;
v_x_619_ = v___y_637_;
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
lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(uint8_t v_c_755_, lean_object* v_t_756_){
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
LEAN_EXPORT void l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_755_ = stack[0].m_num;
lean_object* v_t_756_ = stack[1].m_obj;
lean_object* v_res_770_;
v_res_770_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(v_c_755_, v_t_756_);
stack->m_obj
 = v_res_770_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(lean_object* v_00_u03b1_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1___redArg(lean_object* v_t_775_){
_start:
{
lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___f_776_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_777_ = lean_box(1);
v___x_778_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_775_);
v___x_779_ = l_Std_Format_joinSep___redArg(v___f_776_, v___x_778_, v___x_777_);
v___x_780_ = l_Std_Format_defWidth;
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = l_Std_Format_pretty(v___x_779_, v___x_780_, v___x_781_, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___private__1(lean_object* v_00_u03b1_783_, lean_object* v_t_784_){
_start:
{
lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___f_785_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_786_ = lean_box(1);
v___x_787_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_784_);
v___x_788_ = l_Std_Format_joinSep___redArg(v___f_785_, v___x_787_, v___x_786_);
v___x_789_ = l_Std_Format_defWidth;
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = l_Std_Format_pretty(v___x_788_, v___x_789_, v___x_790_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___redArg___lam__0(lean_object* v_t_792_){
_start:
{
lean_object* v___f_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___f_793_ = ((lean_object*)(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0));
v___x_794_ = lean_box(1);
v___x_795_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_792_);
v___x_796_ = l_Std_Format_joinSep___redArg(v___f_793_, v___x_795_, v___x_794_);
v___x_797_ = l_Std_Format_defWidth;
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = l_Std_Format_pretty(v___x_796_, v___x_797_, v___x_798_, v___x_798_);
return v___x_799_;
}
}
lean_object* l_Lean_Data_Trie_instToString___redArg(){
_start:
{
lean_object* v___f_802_; 
v___f_802_ = ((lean_object*)(l_Lean_Data_Trie_instToString___redArg___closed__0));
return v___f_802_;
}
}
LEAN_EXPORT void l_Lean_Data_Trie_instToString___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_803_;
v_res_803_ = l_Lean_Data_Trie_instToString___redArg();
stack->m_obj
 = v_res_803_;
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___redArg___boxed(lean_object* v___dummy_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Data_Trie_instToString___redArg();
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString(lean_object* v_00_u03b1_806_){
_start:
{
lean_object* v___f_807_; 
v___f_807_ = ((lean_object*)(l_Lean_Data_Trie_instToString___redArg___closed__0));
return v___f_807_;
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
