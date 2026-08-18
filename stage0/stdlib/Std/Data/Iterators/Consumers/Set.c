// Lean compiler output
// Module: Std.Data.Iterators.Consumers.Set
// Imports: public import Std.Data.Iterators.Consumers.Monadic.Set public import Init.Data.Iterators.Consumers.Total
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Iter_toHashSet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iter_toHashSet___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iter_toHashSet___redArg___closed__0 = (const lean_object*)&l_Std_Iter_toHashSet___redArg___closed__0_value;
static lean_once_cell_t l_Std_Iter_toHashSet___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toHashSet___redArg___closed__1;
static lean_once_cell_t l_Std_Iter_toHashSet___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toHashSet___redArg___closed__2;
static lean_once_cell_t l_Std_Iter_toHashSet___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toHashSet___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Iter_toTreeSet___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__0 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__0_value;
static const lean_string_object l_Std_Iter_toTreeSet___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__1 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__1_value;
static const lean_string_object l_Std_Iter_toTreeSet___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__2 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__2_value;
static const lean_string_object l_Std_Iter_toTreeSet___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__3 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__3_value;
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__4 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__4_value;
static const lean_array_object l_Std_Iter_toTreeSet___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__5 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__5_value;
static const lean_string_object l_Std_Iter_toTreeSet___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__6 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__6_value;
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__7 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__7_value;
static const lean_string_object l_Std_Iter_toTreeSet___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__8 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__8_value;
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__9 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__9_value;
static const lean_string_object l_Std_Iter_toTreeSet___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__10 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__10_value;
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__11 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__11_value;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__12;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__13;
static const lean_string_object l_Std_Iter_toTreeSet___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__14 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__14_value;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__15;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__16;
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__17 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__17_value;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__18;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__19;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__20;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__21;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__22;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__23;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__24;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__25;
static lean_once_cell_t l_Std_Iter_toTreeSet___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toTreeSet___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet___auto__1;
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toTreeSet___auto__1;
LEAN_EXPORT lean_object* l_Std_Iter_Total_toTreeSet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toTreeSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toTreeSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet___auto__1;
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtTreeSet___auto__1;
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtTreeSet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtTreeSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtTreeSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___redArg___lam__0(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_f_3_, lean_object* v_x_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_apply_1(v_f_3_, v_x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___redArg___lam__1(lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v___x_8_, lean_object* v_x1_9_, lean_object* v_x2_10_, lean_object* v_x3_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___y_14_; lean_object* v_i_15_; lean_object* v___y_22_; lean_object* v___y_33_; lean_object* v_i_34_; lean_object* v___x_51_; 
v___x_12_ = lean_box(0);
lean_inc(v_x1_9_);
lean_inc_ref(v_inst_7_);
lean_inc_ref(v_inst_6_);
v___x_51_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_6_, v_inst_7_, v_x3_11_, v_x1_9_);
switch(lean_obj_tag(v___x_51_))
{
case 0:
{
lean_object* v___x_52_; 
lean_dec_ref_known(v___x_51_, 3);
lean_dec(v_x1_9_);
lean_dec(v___x_8_);
lean_dec_ref(v_inst_7_);
lean_dec_ref(v_inst_6_);
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v_x3_11_);
return v___x_52_;
}
case 1:
{
lean_object* v_index_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_72_; 
v_index_53_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_72_ == 0)
{
v___x_55_ = v___x_51_;
v_isShared_56_ = v_isSharedCheck_72_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_index_53_);
lean_dec(v___x_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_72_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v_size_57_; lean_object* v_keyArray_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_size_57_ = lean_ctor_get(v_x3_11_, 0);
v_keyArray_58_ = lean_ctor_get(v_x3_11_, 1);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_add(v_size_57_, v___x_59_);
v___x_61_ = lean_array_get_size(v_keyArray_58_);
v___x_62_ = lean_nat_dec_lt(v___x_60_, v___x_61_);
if (v___x_62_ == 0)
{
lean_dec(v___x_60_);
lean_del_object(v___x_55_);
lean_dec(v_index_53_);
goto v___jp_40_;
}
else
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_63_ = lean_unsigned_to_nat(4u);
v___x_64_ = lean_nat_mul(v___x_60_, v___x_63_);
v___x_65_ = lean_unsigned_to_nat(3u);
v___x_66_ = lean_nat_mul(v___x_61_, v___x_65_);
v___x_67_ = lean_nat_dec_le(v___x_64_, v___x_66_);
lean_dec(v___x_66_);
lean_dec(v___x_64_);
if (v___x_67_ == 0)
{
lean_dec(v___x_60_);
lean_del_object(v___x_55_);
lean_dec(v_index_53_);
goto v___jp_40_;
}
else
{
lean_object* v___x_68_; lean_object* v___x_70_; 
lean_dec(v___x_8_);
lean_dec_ref(v_inst_7_);
lean_dec_ref(v_inst_6_);
v___x_68_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x3_11_, v___x_60_, v_index_53_, v_x1_9_, v___x_12_);
lean_dec(v_index_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_68_);
v___x_70_ = v___x_55_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
default: 
{
lean_object* v_size_73_; lean_object* v_keyArray_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_size_73_ = lean_ctor_get(v_x3_11_, 0);
v_keyArray_74_ = lean_ctor_get(v_x3_11_, 1);
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_add(v_size_73_, v___x_75_);
v___x_77_ = lean_array_get_size(v_keyArray_74_);
v___x_78_ = lean_nat_dec_lt(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_dec(v___x_76_);
lean_inc_ref(v_inst_7_);
lean_inc_ref(v_inst_6_);
v___x_79_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_6_, v_inst_7_, v_x3_11_);
v___y_22_ = v___x_79_;
goto v___jp_21_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_80_ = lean_unsigned_to_nat(4u);
v___x_81_ = lean_nat_mul(v___x_76_, v___x_80_);
lean_dec(v___x_76_);
v___x_82_ = lean_unsigned_to_nat(3u);
v___x_83_ = lean_nat_mul(v___x_77_, v___x_82_);
v___x_84_ = lean_nat_dec_le(v___x_81_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_81_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
lean_inc_ref(v_inst_7_);
lean_inc_ref(v_inst_6_);
v___x_85_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_6_, v_inst_7_, v_x3_11_);
v___y_22_ = v___x_85_;
goto v___jp_21_;
}
else
{
v___y_22_ = v_x3_11_;
goto v___jp_21_;
}
}
}
}
v___jp_13_:
{
lean_object* v_size_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_size_16_ = lean_ctor_get(v___y_14_, 0);
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_add(v_size_16_, v___x_17_);
v___x_19_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_14_, v___x_18_, v_i_15_, v_x1_9_, v___x_12_);
lean_dec(v_i_15_);
v___x_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
return v___x_20_;
}
v___jp_21_:
{
lean_object* v___x_23_; 
lean_inc(v_x1_9_);
v___x_23_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_6_, v_inst_7_, v___y_22_, v_x1_9_);
switch(lean_obj_tag(v___x_23_))
{
case 0:
{
lean_object* v_index_24_; lean_object* v_size_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v___x_8_);
v_index_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_index_24_);
lean_dec_ref_known(v___x_23_, 3);
v_size_25_ = lean_ctor_get(v___y_22_, 0);
lean_inc(v_size_25_);
v___x_26_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_22_, v_size_25_, v_index_24_, v_x1_9_, v___x_12_);
lean_dec(v_index_24_);
v___x_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
case 1:
{
lean_object* v_index_28_; 
lean_dec(v___x_8_);
v_index_28_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_index_28_);
lean_dec_ref_known(v___x_23_, 1);
v___y_14_ = v___y_22_;
v_i_15_ = v_index_28_;
goto v___jp_13_;
}
default: 
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_22_, v___x_8_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_index_30_; 
v_index_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_index_30_);
lean_dec_ref_known(v___x_29_, 1);
v___y_14_ = v___y_22_;
v_i_15_ = v_index_30_;
goto v___jp_13_;
}
else
{
lean_object* v___x_31_; 
lean_dec(v_x1_9_);
v___x_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_31_, 0, v___y_22_);
return v___x_31_;
}
}
}
}
v___jp_32_:
{
lean_object* v_size_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_size_35_ = lean_ctor_get(v___y_33_, 0);
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = lean_nat_add(v_size_35_, v___x_36_);
v___x_38_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_33_, v___x_37_, v_i_34_, v_x1_9_, v___x_12_);
lean_dec(v_i_34_);
v___x_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
v___jp_40_:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
lean_inc_ref(v_inst_7_);
lean_inc_ref(v_inst_6_);
v___x_41_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_6_, v_inst_7_, v_x3_11_);
lean_inc(v_x1_9_);
v___x_42_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_6_, v_inst_7_, v___x_41_, v_x1_9_);
switch(lean_obj_tag(v___x_42_))
{
case 0:
{
lean_object* v_index_43_; lean_object* v_size_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec(v___x_8_);
v_index_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_index_43_);
lean_dec_ref_known(v___x_42_, 3);
v_size_44_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_size_44_);
v___x_45_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_41_, v_size_44_, v_index_43_, v_x1_9_, v___x_12_);
lean_dec(v_index_43_);
v___x_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
case 1:
{
lean_object* v_index_47_; 
lean_dec(v___x_8_);
v_index_47_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_index_47_);
lean_dec_ref_known(v___x_42_, 1);
v___y_33_ = v___x_41_;
v_i_34_ = v_index_47_;
goto v___jp_32_;
}
default: 
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_41_, v___x_8_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_index_49_; 
v_index_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_index_49_);
lean_dec_ref_known(v___x_48_, 1);
v___y_33_ = v___x_41_;
v_i_34_ = v_index_49_;
goto v___jp_32_;
}
else
{
lean_object* v___x_50_; 
lean_dec(v_x1_9_);
v___x_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_41_);
return v___x_50_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Iter_toHashSet___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_87_; lean_object* v___x_88_; 
v_cellCount_87_ = lean_unsigned_to_nat(16u);
v___x_88_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_87_);
return v___x_88_;
}
}
static lean_object* _init_l_Std_Iter_toHashSet___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_89_; lean_object* v___x_90_; 
v_cellCount_89_ = lean_unsigned_to_nat(16u);
v___x_90_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Std_Iter_toHashSet___redArg___closed__3(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__2, &l_Std_Iter_toHashSet___redArg___closed__2_once, _init_l_Std_Iter_toHashSet___redArg___closed__2);
v___x_92_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__1, &l_Std_Iter_toHashSet___redArg___closed__1_once, _init_l_Std_Iter_toHashSet___redArg___closed__1);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
lean_ctor_set(v___x_94_, 2, v___x_91_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___redArg(lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_it_98_){
_start:
{
lean_object* v___f_99_; lean_object* v___x_100_; lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___f_99_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___x_100_ = lean_unsigned_to_nat(0u);
v___f_101_ = lean_alloc_closure((void*)(l_Std_Iter_toHashSet___redArg___lam__1), 6, 3);
lean_closure_set(v___f_101_, 0, v_inst_95_);
lean_closure_set(v___f_101_, 1, v_inst_96_);
lean_closure_set(v___f_101_, 2, v___x_100_);
v___x_102_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__3, &l_Std_Iter_toHashSet___redArg___closed__3_once, _init_l_Std_Iter_toHashSet___redArg___closed__3);
v___x_103_ = lean_apply_6(v_inst_97_, v___f_99_, lean_box(0), lean_box(0), v_it_98_, v___x_102_, v___f_101_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet(lean_object* v_00_u03b1_104_, lean_object* v_00_u03b2_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_it_110_){
_start:
{
lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___f_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___f_111_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___x_112_ = lean_unsigned_to_nat(0u);
v___f_113_ = lean_alloc_closure((void*)(l_Std_Iter_toHashSet___redArg___lam__1), 6, 3);
lean_closure_set(v___f_113_, 0, v_inst_106_);
lean_closure_set(v___f_113_, 1, v_inst_107_);
lean_closure_set(v___f_113_, 2, v___x_112_);
v___x_114_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__3, &l_Std_Iter_toHashSet___redArg___closed__3_once, _init_l_Std_Iter_toHashSet___redArg___closed__3);
v___x_115_ = lean_apply_6(v_inst_109_, v___f_111_, lean_box(0), lean_box(0), v_it_110_, v___x_114_, v___f_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___boxed(lean_object* v_00_u03b1_116_, lean_object* v_00_u03b2_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_it_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_Iter_toHashSet(v_00_u03b1_116_, v_00_u03b2_117_, v_inst_118_, v_inst_119_, v_inst_120_, v_inst_121_, v_it_122_);
lean_dec(v_inst_120_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet___redArg(lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_it_127_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; lean_object* v___f_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___f_128_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___x_129_ = lean_unsigned_to_nat(0u);
v___f_130_ = lean_alloc_closure((void*)(l_Std_Iter_toHashSet___redArg___lam__1), 6, 3);
lean_closure_set(v___f_130_, 0, v_inst_124_);
lean_closure_set(v___f_130_, 1, v_inst_125_);
lean_closure_set(v___f_130_, 2, v___x_129_);
v___x_131_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__3, &l_Std_Iter_toHashSet___redArg___closed__3_once, _init_l_Std_Iter_toHashSet___redArg___closed__3);
v___x_132_ = lean_apply_6(v_inst_126_, v___f_128_, lean_box(0), lean_box(0), v_it_127_, v___x_131_, v___f_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_it_140_){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___f_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___f_141_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___x_142_ = lean_unsigned_to_nat(0u);
v___f_143_ = lean_alloc_closure((void*)(l_Std_Iter_toHashSet___redArg___lam__1), 6, 3);
lean_closure_set(v___f_143_, 0, v_inst_135_);
lean_closure_set(v___f_143_, 1, v_inst_136_);
lean_closure_set(v___f_143_, 2, v___x_142_);
v___x_144_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__3, &l_Std_Iter_toHashSet___redArg___closed__3_once, _init_l_Std_Iter_toHashSet___redArg___closed__3);
v___x_145_ = lean_apply_6(v_inst_139_, v___f_141_, lean_box(0), lean_box(0), v_it_140_, v___x_144_, v___f_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet___boxed(lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_it_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_Iter_Total_toHashSet(v_00_u03b1_146_, v_00_u03b2_147_, v_inst_148_, v_inst_149_, v_inst_150_, v_inst_151_, v_inst_152_, v_it_153_);
lean_dec(v_inst_150_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet___redArg___lam__1(lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v___x_157_, lean_object* v_x1_158_, lean_object* v_x2_159_, lean_object* v_x3_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___y_163_; lean_object* v_i_164_; lean_object* v___y_171_; lean_object* v___y_182_; lean_object* v_i_183_; lean_object* v___x_200_; 
v___x_161_ = lean_box(0);
lean_inc(v_x1_158_);
lean_inc_ref(v_inst_156_);
lean_inc_ref(v_inst_155_);
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_155_, v_inst_156_, v_x3_160_, v_x1_158_);
switch(lean_obj_tag(v___x_200_))
{
case 0:
{
lean_object* v___x_201_; 
lean_dec_ref_known(v___x_200_, 3);
lean_dec(v_x1_158_);
lean_dec(v___x_157_);
lean_dec_ref(v_inst_156_);
lean_dec_ref(v_inst_155_);
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v_x3_160_);
return v___x_201_;
}
case 1:
{
lean_object* v_index_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_221_; 
v_index_202_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_221_ == 0)
{
v___x_204_ = v___x_200_;
v_isShared_205_ = v_isSharedCheck_221_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_index_202_);
lean_dec(v___x_200_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_221_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v_size_206_; lean_object* v_keyArray_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_size_206_ = lean_ctor_get(v_x3_160_, 0);
v_keyArray_207_ = lean_ctor_get(v_x3_160_, 1);
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_add(v_size_206_, v___x_208_);
v___x_210_ = lean_array_get_size(v_keyArray_207_);
v___x_211_ = lean_nat_dec_lt(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
lean_dec(v___x_209_);
lean_del_object(v___x_204_);
lean_dec(v_index_202_);
goto v___jp_189_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_212_ = lean_unsigned_to_nat(4u);
v___x_213_ = lean_nat_mul(v___x_209_, v___x_212_);
v___x_214_ = lean_unsigned_to_nat(3u);
v___x_215_ = lean_nat_mul(v___x_210_, v___x_214_);
v___x_216_ = lean_nat_dec_le(v___x_213_, v___x_215_);
lean_dec(v___x_215_);
lean_dec(v___x_213_);
if (v___x_216_ == 0)
{
lean_dec(v___x_209_);
lean_del_object(v___x_204_);
lean_dec(v_index_202_);
goto v___jp_189_;
}
else
{
lean_object* v___x_217_; lean_object* v___x_219_; 
lean_dec(v___x_157_);
lean_dec_ref(v_inst_156_);
lean_dec_ref(v_inst_155_);
v___x_217_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x3_160_, v___x_209_, v_index_202_, v_x1_158_, v___x_161_);
lean_dec(v_index_202_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_217_);
v___x_219_ = v___x_204_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
default: 
{
lean_object* v_size_222_; lean_object* v_keyArray_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_size_222_ = lean_ctor_get(v_x3_160_, 0);
v_keyArray_223_ = lean_ctor_get(v_x3_160_, 1);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_add(v_size_222_, v___x_224_);
v___x_226_ = lean_array_get_size(v_keyArray_223_);
v___x_227_ = lean_nat_dec_lt(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec(v___x_225_);
lean_inc_ref(v_inst_156_);
lean_inc_ref(v_inst_155_);
v___x_228_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_155_, v_inst_156_, v_x3_160_);
v___y_171_ = v___x_228_;
goto v___jp_170_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_229_ = lean_unsigned_to_nat(4u);
v___x_230_ = lean_nat_mul(v___x_225_, v___x_229_);
lean_dec(v___x_225_);
v___x_231_ = lean_unsigned_to_nat(3u);
v___x_232_ = lean_nat_mul(v___x_226_, v___x_231_);
v___x_233_ = lean_nat_dec_le(v___x_230_, v___x_232_);
lean_dec(v___x_232_);
lean_dec(v___x_230_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
lean_inc_ref(v_inst_156_);
lean_inc_ref(v_inst_155_);
v___x_234_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_155_, v_inst_156_, v_x3_160_);
v___y_171_ = v___x_234_;
goto v___jp_170_;
}
else
{
v___y_171_ = v_x3_160_;
goto v___jp_170_;
}
}
}
}
v___jp_162_:
{
lean_object* v_size_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_size_165_ = lean_ctor_get(v___y_163_, 0);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v_size_165_, v___x_166_);
v___x_168_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_163_, v___x_167_, v_i_164_, v_x1_158_, v___x_161_);
lean_dec(v_i_164_);
v___x_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
v___jp_170_:
{
lean_object* v___x_172_; 
lean_inc(v_x1_158_);
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_155_, v_inst_156_, v___y_171_, v_x1_158_);
switch(lean_obj_tag(v___x_172_))
{
case 0:
{
lean_object* v_index_173_; lean_object* v_size_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v___x_157_);
v_index_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_index_173_);
lean_dec_ref_known(v___x_172_, 3);
v_size_174_ = lean_ctor_get(v___y_171_, 0);
lean_inc(v_size_174_);
v___x_175_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_171_, v_size_174_, v_index_173_, v_x1_158_, v___x_161_);
lean_dec(v_index_173_);
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
case 1:
{
lean_object* v_index_177_; 
lean_dec(v___x_157_);
v_index_177_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_index_177_);
lean_dec_ref_known(v___x_172_, 1);
v___y_163_ = v___y_171_;
v_i_164_ = v_index_177_;
goto v___jp_162_;
}
default: 
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_171_, v___x_157_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_index_179_; 
v_index_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_index_179_);
lean_dec_ref_known(v___x_178_, 1);
v___y_163_ = v___y_171_;
v_i_164_ = v_index_179_;
goto v___jp_162_;
}
else
{
lean_object* v___x_180_; 
lean_dec(v_x1_158_);
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v___y_171_);
return v___x_180_;
}
}
}
}
v___jp_181_:
{
lean_object* v_size_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_size_184_ = lean_ctor_get(v___y_182_, 0);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_add(v_size_184_, v___x_185_);
v___x_187_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_182_, v___x_186_, v_i_183_, v_x1_158_, v___x_161_);
lean_dec(v_i_183_);
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
v___jp_189_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_inc_ref(v_inst_156_);
lean_inc_ref(v_inst_155_);
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_155_, v_inst_156_, v_x3_160_);
lean_inc(v_x1_158_);
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_155_, v_inst_156_, v___x_190_, v_x1_158_);
switch(lean_obj_tag(v___x_191_))
{
case 0:
{
lean_object* v_index_192_; lean_object* v_size_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v___x_157_);
v_index_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_index_192_);
lean_dec_ref_known(v___x_191_, 3);
v_size_193_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_size_193_);
v___x_194_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_190_, v_size_193_, v_index_192_, v_x1_158_, v___x_161_);
lean_dec(v_index_192_);
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
case 1:
{
lean_object* v_index_196_; 
lean_dec(v___x_157_);
v_index_196_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_index_196_);
lean_dec_ref_known(v___x_191_, 1);
v___y_182_ = v___x_190_;
v_i_183_ = v_index_196_;
goto v___jp_181_;
}
default: 
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_190_, v___x_157_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_index_198_; 
v_index_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_index_198_);
lean_dec_ref_known(v___x_197_, 1);
v___y_182_ = v___x_190_;
v_i_183_ = v_index_198_;
goto v___jp_181_;
}
else
{
lean_object* v___x_199_; 
lean_dec(v_x1_158_);
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_190_);
return v___x_199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet___redArg(lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_it_238_){
_start:
{
lean_object* v___f_239_; lean_object* v___x_240_; lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___f_239_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___x_240_ = lean_unsigned_to_nat(0u);
v___f_241_ = lean_alloc_closure((void*)(l_Std_Iter_toExtHashSet___redArg___lam__1), 6, 3);
lean_closure_set(v___f_241_, 0, v_inst_235_);
lean_closure_set(v___f_241_, 1, v_inst_236_);
lean_closure_set(v___f_241_, 2, v___x_240_);
v___x_242_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__3, &l_Std_Iter_toHashSet___redArg___closed__3_once, _init_l_Std_Iter_toHashSet___redArg___closed__3);
v___x_243_ = lean_apply_6(v_inst_237_, v___f_239_, lean_box(0), lean_box(0), v_it_238_, v___x_242_, v___f_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_it_252_){
_start:
{
lean_object* v___f_253_; lean_object* v___x_254_; lean_object* v___f_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___f_253_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___x_254_ = lean_unsigned_to_nat(0u);
v___f_255_ = lean_alloc_closure((void*)(l_Std_Iter_toExtHashSet___redArg___lam__1), 6, 3);
lean_closure_set(v___f_255_, 0, v_inst_246_);
lean_closure_set(v___f_255_, 1, v_inst_247_);
lean_closure_set(v___f_255_, 2, v___x_254_);
v___x_256_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__3, &l_Std_Iter_toHashSet___redArg___closed__3_once, _init_l_Std_Iter_toHashSet___redArg___closed__3);
v___x_257_ = lean_apply_6(v_inst_251_, v___f_253_, lean_box(0), lean_box(0), v_it_252_, v___x_256_, v___f_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet___boxed(lean_object* v_00_u03b1_258_, lean_object* v_00_u03b2_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_it_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_Iter_toExtHashSet(v_00_u03b1_258_, v_00_u03b2_259_, v_inst_260_, v_inst_261_, v_inst_262_, v_inst_263_, v_inst_264_, v_inst_265_, v_it_266_);
lean_dec(v_inst_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtHashSet___redArg(lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_it_271_){
_start:
{
lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___f_272_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___x_273_ = lean_unsigned_to_nat(0u);
v___f_274_ = lean_alloc_closure((void*)(l_Std_Iter_toExtHashSet___redArg___lam__1), 6, 3);
lean_closure_set(v___f_274_, 0, v_inst_268_);
lean_closure_set(v___f_274_, 1, v_inst_269_);
lean_closure_set(v___f_274_, 2, v___x_273_);
v___x_275_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__3, &l_Std_Iter_toHashSet___redArg___closed__3_once, _init_l_Std_Iter_toHashSet___redArg___closed__3);
v___x_276_ = lean_apply_6(v_inst_270_, v___f_272_, lean_box(0), lean_box(0), v_it_271_, v___x_275_, v___f_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtHashSet(lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_it_286_){
_start:
{
lean_object* v___f_287_; lean_object* v___x_288_; lean_object* v___f_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___f_287_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___x_288_ = lean_unsigned_to_nat(0u);
v___f_289_ = lean_alloc_closure((void*)(l_Std_Iter_toExtHashSet___redArg___lam__1), 6, 3);
lean_closure_set(v___f_289_, 0, v_inst_279_);
lean_closure_set(v___f_289_, 1, v_inst_280_);
lean_closure_set(v___f_289_, 2, v___x_288_);
v___x_290_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__3, &l_Std_Iter_toHashSet___redArg___closed__3_once, _init_l_Std_Iter_toHashSet___redArg___closed__3);
v___x_291_ = lean_apply_6(v_inst_285_, v___f_287_, lean_box(0), lean_box(0), v_it_286_, v___x_290_, v___f_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtHashSet___boxed(lean_object* v_00_u03b1_292_, lean_object* v_00_u03b2_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_it_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_Iter_Total_toExtHashSet(v_00_u03b1_292_, v_00_u03b2_293_, v_inst_294_, v_inst_295_, v_inst_296_, v_inst_297_, v_inst_298_, v_inst_299_, v_inst_300_, v_it_301_);
lean_dec(v_inst_298_);
return v_res_302_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__12(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__10));
v___x_330_ = l_Lean_mkAtom(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__13(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__12, &l_Std_Iter_toTreeSet___auto__1___closed__12_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__12);
v___x_332_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__5));
v___x_333_ = lean_array_push(v___x_332_, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__15(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__14));
v___x_336_ = lean_string_utf8_byte_size(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__16(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_337_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__15, &l_Std_Iter_toTreeSet___auto__1___closed__15_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__15);
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__14));
v___x_340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_338_);
lean_ctor_set(v___x_340_, 2, v___x_337_);
return v___x_340_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__18(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_343_ = lean_box(0);
v___x_344_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__17));
v___x_345_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__16, &l_Std_Iter_toTreeSet___auto__1___closed__16_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__16);
v___x_346_ = lean_box(2);
v___x_347_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
lean_ctor_set(v___x_347_, 2, v___x_344_);
lean_ctor_set(v___x_347_, 3, v___x_343_);
return v___x_347_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__19(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__18, &l_Std_Iter_toTreeSet___auto__1___closed__18_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__18);
v___x_349_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__13, &l_Std_Iter_toTreeSet___auto__1___closed__13_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__13);
v___x_350_ = lean_array_push(v___x_349_, v___x_348_);
return v___x_350_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__20(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_351_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__19, &l_Std_Iter_toTreeSet___auto__1___closed__19_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__19);
v___x_352_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__11));
v___x_353_ = lean_box(2);
v___x_354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
lean_ctor_set(v___x_354_, 2, v___x_351_);
return v___x_354_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__21(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__20, &l_Std_Iter_toTreeSet___auto__1___closed__20_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__20);
v___x_356_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__5));
v___x_357_ = lean_array_push(v___x_356_, v___x_355_);
return v___x_357_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__22(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__21, &l_Std_Iter_toTreeSet___auto__1___closed__21_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__21);
v___x_359_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__9));
v___x_360_ = lean_box(2);
v___x_361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_359_);
lean_ctor_set(v___x_361_, 2, v___x_358_);
return v___x_361_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__23(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__22, &l_Std_Iter_toTreeSet___auto__1___closed__22_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__22);
v___x_363_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__5));
v___x_364_ = lean_array_push(v___x_363_, v___x_362_);
return v___x_364_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__24(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_365_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__23, &l_Std_Iter_toTreeSet___auto__1___closed__23_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__23);
v___x_366_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__7));
v___x_367_ = lean_box(2);
v___x_368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___x_366_);
lean_ctor_set(v___x_368_, 2, v___x_365_);
return v___x_368_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__25(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__24, &l_Std_Iter_toTreeSet___auto__1___closed__24_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__24);
v___x_370_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__5));
v___x_371_ = lean_array_push(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__26(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_372_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__25, &l_Std_Iter_toTreeSet___auto__1___closed__25_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__25);
v___x_373_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__4));
v___x_374_ = lean_box(2);
v___x_375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
lean_ctor_set(v___x_375_, 2, v___x_372_);
return v___x_375_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__26, &l_Std_Iter_toTreeSet___auto__1___closed__26_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__26);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet___redArg___lam__1(lean_object* v_cmp_377_, lean_object* v_x1_378_, lean_object* v_x2_379_, lean_object* v_x3_380_){
_start:
{
uint8_t v___x_381_; 
lean_inc(v_x3_380_);
lean_inc(v_x1_378_);
lean_inc_ref(v_cmp_377_);
v___x_381_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_377_, v_x1_378_, v_x3_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_box(0);
v___x_383_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_377_, v_x1_378_, v___x_382_, v_x3_380_);
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
else
{
lean_object* v___x_385_; 
lean_dec(v_x1_378_);
lean_dec_ref(v_cmp_377_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v_x3_380_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet___redArg(lean_object* v_inst_386_, lean_object* v_it_387_, lean_object* v_cmp_388_){
_start:
{
lean_object* v___f_389_; lean_object* v___f_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___f_389_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_390_ = lean_alloc_closure((void*)(l_Std_Iter_toTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_390_, 0, v_cmp_388_);
v___x_391_ = lean_box(1);
v___x_392_ = lean_apply_6(v_inst_386_, v___f_389_, lean_box(0), lean_box(0), v_it_387_, v___x_391_, v___f_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet(lean_object* v_00_u03b1_393_, lean_object* v_00_u03b2_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_it_397_, lean_object* v_cmp_398_){
_start:
{
lean_object* v___f_399_; lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___f_399_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_400_ = lean_alloc_closure((void*)(l_Std_Iter_toTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_400_, 0, v_cmp_398_);
v___x_401_ = lean_box(1);
v___x_402_ = lean_apply_6(v_inst_396_, v___f_399_, lean_box(0), lean_box(0), v_it_397_, v___x_401_, v___f_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet___boxed(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_it_407_, lean_object* v_cmp_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_Iter_toTreeSet(v_00_u03b1_403_, v_00_u03b2_404_, v_inst_405_, v_inst_406_, v_it_407_, v_cmp_408_);
lean_dec(v_inst_405_);
return v_res_409_;
}
}
static lean_object* _init_l_Std_Iter_Total_toTreeSet___auto__1(void){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__26, &l_Std_Iter_toTreeSet___auto__1___closed__26_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__26);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toTreeSet___redArg(lean_object* v_inst_411_, lean_object* v_it_412_, lean_object* v_cmp_413_){
_start:
{
lean_object* v___f_414_; lean_object* v___f_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___f_414_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_415_ = lean_alloc_closure((void*)(l_Std_Iter_toTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_415_, 0, v_cmp_413_);
v___x_416_ = lean_box(1);
v___x_417_ = lean_apply_6(v_inst_411_, v___f_414_, lean_box(0), lean_box(0), v_it_412_, v___x_416_, v___f_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toTreeSet(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_it_423_, lean_object* v_cmp_424_){
_start:
{
lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___f_425_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_426_ = lean_alloc_closure((void*)(l_Std_Iter_toTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_426_, 0, v_cmp_424_);
v___x_427_ = lean_box(1);
v___x_428_ = lean_apply_6(v_inst_422_, v___f_425_, lean_box(0), lean_box(0), v_it_423_, v___x_427_, v___f_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toTreeSet___boxed(lean_object* v_00_u03b1_429_, lean_object* v_00_u03b2_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_it_434_, lean_object* v_cmp_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_Iter_Total_toTreeSet(v_00_u03b1_429_, v_00_u03b2_430_, v_inst_431_, v_inst_432_, v_inst_433_, v_it_434_, v_cmp_435_);
lean_dec(v_inst_431_);
return v_res_436_;
}
}
static lean_object* _init_l_Std_Iter_toExtTreeSet___auto__1(void){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__26, &l_Std_Iter_toTreeSet___auto__1___closed__26_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__26);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet___redArg___lam__1(lean_object* v_cmp_438_, lean_object* v_x1_439_, lean_object* v_x2_440_, lean_object* v_x3_441_){
_start:
{
uint8_t v___x_442_; 
lean_inc(v_x3_441_);
lean_inc(v_x1_439_);
lean_inc_ref(v_cmp_438_);
v___x_442_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_438_, v_x1_439_, v_x3_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_box(0);
v___x_444_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_438_, v_x1_439_, v___x_443_, v_x3_441_);
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
else
{
lean_object* v___x_446_; 
lean_dec(v_x1_439_);
lean_dec_ref(v_cmp_438_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_x3_441_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet___redArg(lean_object* v_inst_447_, lean_object* v_it_448_, lean_object* v_cmp_449_){
_start:
{
lean_object* v___f_450_; lean_object* v___f_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___f_450_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_451_ = lean_alloc_closure((void*)(l_Std_Iter_toExtTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_451_, 0, v_cmp_449_);
v___x_452_ = lean_box(1);
v___x_453_ = lean_apply_6(v_inst_447_, v___f_450_, lean_box(0), lean_box(0), v_it_448_, v___x_452_, v___f_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet(lean_object* v_00_u03b1_454_, lean_object* v_00_u03b2_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_it_458_, lean_object* v_cmp_459_, lean_object* v_inst_460_){
_start:
{
lean_object* v___f_461_; lean_object* v___f_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___f_461_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_462_ = lean_alloc_closure((void*)(l_Std_Iter_toExtTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_462_, 0, v_cmp_459_);
v___x_463_ = lean_box(1);
v___x_464_ = lean_apply_6(v_inst_457_, v___f_461_, lean_box(0), lean_box(0), v_it_458_, v___x_463_, v___f_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet___boxed(lean_object* v_00_u03b1_465_, lean_object* v_00_u03b2_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_it_469_, lean_object* v_cmp_470_, lean_object* v_inst_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Std_Iter_toExtTreeSet(v_00_u03b1_465_, v_00_u03b2_466_, v_inst_467_, v_inst_468_, v_it_469_, v_cmp_470_, v_inst_471_);
lean_dec(v_inst_467_);
return v_res_472_;
}
}
static lean_object* _init_l_Std_Iter_Total_toExtTreeSet___auto__1(void){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__26, &l_Std_Iter_toTreeSet___auto__1___closed__26_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__26);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtTreeSet___redArg(lean_object* v_inst_474_, lean_object* v_it_475_, lean_object* v_cmp_476_){
_start:
{
lean_object* v___f_477_; lean_object* v___f_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___f_477_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_478_ = lean_alloc_closure((void*)(l_Std_Iter_toExtTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_478_, 0, v_cmp_476_);
v___x_479_ = lean_box(1);
v___x_480_ = lean_apply_6(v_inst_474_, v___f_477_, lean_box(0), lean_box(0), v_it_475_, v___x_479_, v___f_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtTreeSet(lean_object* v_00_u03b1_481_, lean_object* v_00_u03b2_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_it_486_, lean_object* v_cmp_487_, lean_object* v_inst_488_){
_start:
{
lean_object* v___f_489_; lean_object* v___f_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___f_489_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_490_ = lean_alloc_closure((void*)(l_Std_Iter_toExtTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_490_, 0, v_cmp_487_);
v___x_491_ = lean_box(1);
v___x_492_ = lean_apply_6(v_inst_485_, v___f_489_, lean_box(0), lean_box(0), v_it_486_, v___x_491_, v___f_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtTreeSet___boxed(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_it_498_, lean_object* v_cmp_499_, lean_object* v_inst_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_Iter_Total_toExtTreeSet(v_00_u03b1_493_, v_00_u03b2_494_, v_inst_495_, v_inst_496_, v_inst_497_, v_it_498_, v_cmp_499_, v_inst_500_);
lean_dec(v_inst_495_);
return v_res_501_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Consumers_Monadic_Set(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Consumers_Set(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_Iterators_Consumers_Monadic_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Consumers_Set(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Iter_toTreeSet___auto__1 = _init_l_Std_Iter_toTreeSet___auto__1();
lean_mark_persistent(l_Std_Iter_toTreeSet___auto__1);
l_Std_Iter_Total_toTreeSet___auto__1 = _init_l_Std_Iter_Total_toTreeSet___auto__1();
lean_mark_persistent(l_Std_Iter_Total_toTreeSet___auto__1);
l_Std_Iter_toExtTreeSet___auto__1 = _init_l_Std_Iter_toExtTreeSet___auto__1();
lean_mark_persistent(l_Std_Iter_toExtTreeSet___auto__1);
l_Std_Iter_Total_toExtTreeSet___auto__1 = _init_l_Std_Iter_Total_toExtTreeSet___auto__1();
lean_mark_persistent(l_Std_Iter_Total_toExtTreeSet___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Consumers_Monadic_Set(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Consumers_Set(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Consumers_Monadic_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Consumers_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Consumers_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Consumers_Set(builtin);
}
#ifdef __cplusplus
}
#endif
