// Lean compiler output
// Module: Std.Data.Iterators.Consumers.Monadic.Set
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Loop public import Std.Data.HashSet.Basic public import Std.Data.ExtHashSet.Basic public import Std.Data.TreeSet.Basic public import Std.Data.ExtTreeSet.Basic import Init.Data.Iterators.Consumers.Monadic.Loop
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_IterM_toHashSet___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toHashSet___redArg___closed__0;
static lean_once_cell_t l_Std_IterM_toHashSet___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toHashSet___redArg___closed__1;
static lean_once_cell_t l_Std_IterM_toHashSet___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toHashSet___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toTreeSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toTreeSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toTreeSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_IterM_toExtTreeSet___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__0 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__0_value;
static const lean_string_object l_Std_IterM_toExtTreeSet___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__1 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__1_value;
static const lean_string_object l_Std_IterM_toExtTreeSet___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__2 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__2_value;
static const lean_string_object l_Std_IterM_toExtTreeSet___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__3 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__3_value;
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__4 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__4_value;
static const lean_array_object l_Std_IterM_toExtTreeSet___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__5 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__5_value;
static const lean_string_object l_Std_IterM_toExtTreeSet___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__6 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__6_value;
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__7 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__7_value;
static const lean_string_object l_Std_IterM_toExtTreeSet___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__8 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__8_value;
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__9 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__9_value;
static const lean_string_object l_Std_IterM_toExtTreeSet___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__10 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__10_value;
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__11 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__11_value;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__12;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__13;
static const lean_string_object l_Std_IterM_toExtTreeSet___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__14 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__14_value;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__15;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__16;
static const lean_ctor_object l_Std_IterM_toExtTreeSet___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__17 = (const lean_object*)&l_Std_IterM_toExtTreeSet___auto__1___closed__17_value;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__18;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__19;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__20;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__21;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__22;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__23;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__24;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__25;
static lean_once_cell_t l_Std_IterM_toExtTreeSet___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toExtTreeSet___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet___auto__1;
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtTreeSet___auto__1;
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtTreeSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtTreeSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtTreeSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg___lam__0(lean_object* v_toBind_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_f_4_, lean_object* v_x_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_4(v_toBind_1_, lean_box(0), lean_box(0), v_x_5_, v_f_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg___lam__1(lean_object* v_toPure_7_, lean_object* v_____do__lift_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_2(v_toPure_7_, lean_box(0), v_____do__lift_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg___lam__2(lean_object* v_toPure_10_, lean_object* v_toBind_11_, lean_object* v___f_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v___x_15_, lean_object* v_x1_16_, lean_object* v_x2_17_, lean_object* v_x3_18_){
_start:
{
lean_object* v___y_20_; lean_object* v___x_24_; lean_object* v___y_26_; lean_object* v_i_27_; lean_object* v___y_33_; lean_object* v___y_42_; lean_object* v_i_43_; lean_object* v___x_57_; 
v___x_24_ = lean_box(0);
lean_inc(v_x1_16_);
lean_inc_ref(v_inst_14_);
lean_inc_ref(v_inst_13_);
v___x_57_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_13_, v_inst_14_, v_x3_18_, v_x1_16_);
switch(lean_obj_tag(v___x_57_))
{
case 0:
{
lean_dec_ref_known(v___x_57_, 3);
lean_dec(v_x1_16_);
lean_dec(v___x_15_);
lean_dec_ref(v_inst_14_);
lean_dec_ref(v_inst_13_);
v___y_20_ = v_x3_18_;
goto v___jp_19_;
}
case 1:
{
lean_object* v_index_58_; lean_object* v_size_59_; lean_object* v_keyArray_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v_index_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_index_58_);
lean_dec_ref_known(v___x_57_, 1);
v_size_59_ = lean_ctor_get(v_x3_18_, 0);
v_keyArray_60_ = lean_ctor_get(v_x3_18_, 1);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_size_59_, v___x_61_);
v___x_63_ = lean_array_get_size(v_keyArray_60_);
v___x_64_ = lean_nat_dec_lt(v___x_62_, v___x_63_);
if (v___x_64_ == 0)
{
lean_dec(v___x_62_);
lean_dec(v_index_58_);
goto v___jp_48_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_65_ = lean_unsigned_to_nat(4u);
v___x_66_ = lean_nat_mul(v___x_62_, v___x_65_);
v___x_67_ = lean_unsigned_to_nat(3u);
v___x_68_ = lean_nat_mul(v___x_63_, v___x_67_);
v___x_69_ = lean_nat_dec_le(v___x_66_, v___x_68_);
lean_dec(v___x_68_);
lean_dec(v___x_66_);
if (v___x_69_ == 0)
{
lean_dec(v___x_62_);
lean_dec(v_index_58_);
goto v___jp_48_;
}
else
{
lean_object* v___x_70_; 
lean_dec(v___x_15_);
lean_dec_ref(v_inst_14_);
lean_dec_ref(v_inst_13_);
v___x_70_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x3_18_, v___x_62_, v_index_58_, v_x1_16_, v___x_24_);
lean_dec(v_index_58_);
v___y_20_ = v___x_70_;
goto v___jp_19_;
}
}
}
default: 
{
lean_object* v_size_71_; lean_object* v_keyArray_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_size_71_ = lean_ctor_get(v_x3_18_, 0);
v_keyArray_72_ = lean_ctor_get(v_x3_18_, 1);
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_add(v_size_71_, v___x_73_);
v___x_75_ = lean_array_get_size(v_keyArray_72_);
v___x_76_ = lean_nat_dec_lt(v___x_74_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_dec(v___x_74_);
lean_inc_ref(v_inst_14_);
lean_inc_ref(v_inst_13_);
v___x_77_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_13_, v_inst_14_, v_x3_18_);
v___y_33_ = v___x_77_;
goto v___jp_32_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_78_ = lean_unsigned_to_nat(4u);
v___x_79_ = lean_nat_mul(v___x_74_, v___x_78_);
lean_dec(v___x_74_);
v___x_80_ = lean_unsigned_to_nat(3u);
v___x_81_ = lean_nat_mul(v___x_75_, v___x_80_);
v___x_82_ = lean_nat_dec_le(v___x_79_, v___x_81_);
lean_dec(v___x_81_);
lean_dec(v___x_79_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
lean_inc_ref(v_inst_14_);
lean_inc_ref(v_inst_13_);
v___x_83_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_13_, v_inst_14_, v_x3_18_);
v___y_33_ = v___x_83_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x3_18_;
goto v___jp_32_;
}
}
}
}
v___jp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v___y_20_);
v___x_22_ = lean_apply_2(v_toPure_10_, lean_box(0), v___x_21_);
v___x_23_ = lean_apply_4(v_toBind_11_, lean_box(0), lean_box(0), v___x_22_, v___f_12_);
return v___x_23_;
}
v___jp_25_:
{
lean_object* v_size_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_size_28_ = lean_ctor_get(v___y_26_, 0);
v___x_29_ = lean_unsigned_to_nat(1u);
v___x_30_ = lean_nat_add(v_size_28_, v___x_29_);
v___x_31_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_26_, v___x_30_, v_i_27_, v_x1_16_, v___x_24_);
lean_dec(v_i_27_);
v___y_20_ = v___x_31_;
goto v___jp_19_;
}
v___jp_32_:
{
lean_object* v___x_34_; 
lean_inc(v_x1_16_);
v___x_34_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_13_, v_inst_14_, v___y_33_, v_x1_16_);
switch(lean_obj_tag(v___x_34_))
{
case 0:
{
lean_object* v_index_35_; lean_object* v_size_36_; lean_object* v___x_37_; 
lean_dec(v___x_15_);
v_index_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_index_35_);
lean_dec_ref_known(v___x_34_, 3);
v_size_36_ = lean_ctor_get(v___y_33_, 0);
lean_inc(v_size_36_);
v___x_37_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_33_, v_size_36_, v_index_35_, v_x1_16_, v___x_24_);
lean_dec(v_index_35_);
v___y_20_ = v___x_37_;
goto v___jp_19_;
}
case 1:
{
lean_object* v_index_38_; 
lean_dec(v___x_15_);
v_index_38_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_index_38_);
lean_dec_ref_known(v___x_34_, 1);
v___y_26_ = v___y_33_;
v_i_27_ = v_index_38_;
goto v___jp_25_;
}
default: 
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_33_, v___x_15_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_index_40_; 
v_index_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_index_40_);
lean_dec_ref_known(v___x_39_, 1);
v___y_26_ = v___y_33_;
v_i_27_ = v_index_40_;
goto v___jp_25_;
}
else
{
lean_dec(v_x1_16_);
v___y_20_ = v___y_33_;
goto v___jp_19_;
}
}
}
}
v___jp_41_:
{
lean_object* v_size_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_size_44_ = lean_ctor_get(v___y_42_, 0);
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_add(v_size_44_, v___x_45_);
v___x_47_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_42_, v___x_46_, v_i_43_, v_x1_16_, v___x_24_);
lean_dec(v_i_43_);
v___y_20_ = v___x_47_;
goto v___jp_19_;
}
v___jp_48_:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_inc_ref(v_inst_14_);
lean_inc_ref(v_inst_13_);
v___x_49_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_13_, v_inst_14_, v_x3_18_);
lean_inc(v_x1_16_);
v___x_50_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_13_, v_inst_14_, v___x_49_, v_x1_16_);
switch(lean_obj_tag(v___x_50_))
{
case 0:
{
lean_object* v_index_51_; lean_object* v_size_52_; lean_object* v___x_53_; 
lean_dec(v___x_15_);
v_index_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_index_51_);
lean_dec_ref_known(v___x_50_, 3);
v_size_52_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_size_52_);
v___x_53_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_49_, v_size_52_, v_index_51_, v_x1_16_, v___x_24_);
lean_dec(v_index_51_);
v___y_20_ = v___x_53_;
goto v___jp_19_;
}
case 1:
{
lean_object* v_index_54_; 
lean_dec(v___x_15_);
v_index_54_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_index_54_);
lean_dec_ref_known(v___x_50_, 1);
v___y_42_ = v___x_49_;
v_i_43_ = v_index_54_;
goto v___jp_41_;
}
default: 
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_49_, v___x_15_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_index_56_; 
v_index_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_index_56_);
lean_dec_ref_known(v___x_55_, 1);
v___y_42_ = v___x_49_;
v_i_43_ = v_index_56_;
goto v___jp_41_;
}
else
{
lean_dec(v_x1_16_);
v___y_20_ = v___x_49_;
goto v___jp_19_;
}
}
}
}
}
}
static lean_object* _init_l_Std_IterM_toHashSet___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_84_; lean_object* v___x_85_; 
v_cellCount_84_ = lean_unsigned_to_nat(16u);
v___x_85_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_84_);
return v___x_85_;
}
}
static lean_object* _init_l_Std_IterM_toHashSet___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_86_; lean_object* v___x_87_; 
v_cellCount_86_ = lean_unsigned_to_nat(16u);
v___x_87_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Std_IterM_toHashSet___redArg___closed__2(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__1, &l_Std_IterM_toHashSet___redArg___closed__1_once, _init_l_Std_IterM_toHashSet___redArg___closed__1);
v___x_89_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__0, &l_Std_IterM_toHashSet___redArg___closed__0_once, _init_l_Std_IterM_toHashSet___redArg___closed__0);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
lean_ctor_set(v___x_91_, 2, v___x_88_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg(lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_it_96_){
_start:
{
lean_object* v_toApplicative_97_; lean_object* v_toBind_98_; lean_object* v_toPure_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___f_104_; lean_object* v___x_105_; 
v_toApplicative_97_ = lean_ctor_get(v_inst_94_, 0);
lean_inc_ref(v_toApplicative_97_);
v_toBind_98_ = lean_ctor_get(v_inst_94_, 1);
lean_inc_n(v_toBind_98_, 2);
lean_dec_ref(v_inst_94_);
v_toPure_99_ = lean_ctor_get(v_toApplicative_97_, 1);
lean_inc_n(v_toPure_99_, 2);
lean_dec_ref(v_toApplicative_97_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__2, &l_Std_IterM_toHashSet___redArg___closed__2_once, _init_l_Std_IterM_toHashSet___redArg___closed__2);
v___f_102_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_102_, 0, v_toBind_98_);
v___f_103_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_103_, 0, v_toPure_99_);
v___f_104_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__2), 9, 6);
lean_closure_set(v___f_104_, 0, v_toPure_99_);
lean_closure_set(v___f_104_, 1, v_toBind_98_);
lean_closure_set(v___f_104_, 2, v___f_103_);
lean_closure_set(v___f_104_, 3, v_inst_92_);
lean_closure_set(v___f_104_, 4, v_inst_93_);
lean_closure_set(v___f_104_, 5, v___x_100_);
v___x_105_ = lean_apply_6(v_inst_95_, v___f_102_, lean_box(0), lean_box(0), v_it_96_, v___x_101_, v___f_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet(lean_object* v_00_u03b1_106_, lean_object* v_00_u03b2_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_m_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_it_114_){
_start:
{
lean_object* v_toApplicative_115_; lean_object* v_toBind_116_; lean_object* v_toPure_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___f_122_; lean_object* v___x_123_; 
v_toApplicative_115_ = lean_ctor_get(v_inst_111_, 0);
lean_inc_ref(v_toApplicative_115_);
v_toBind_116_ = lean_ctor_get(v_inst_111_, 1);
lean_inc_n(v_toBind_116_, 2);
lean_dec_ref(v_inst_111_);
v_toPure_117_ = lean_ctor_get(v_toApplicative_115_, 1);
lean_inc_n(v_toPure_117_, 2);
lean_dec_ref(v_toApplicative_115_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__2, &l_Std_IterM_toHashSet___redArg___closed__2_once, _init_l_Std_IterM_toHashSet___redArg___closed__2);
v___f_120_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_120_, 0, v_toBind_116_);
v___f_121_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_121_, 0, v_toPure_117_);
v___f_122_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__2), 9, 6);
lean_closure_set(v___f_122_, 0, v_toPure_117_);
lean_closure_set(v___f_122_, 1, v_toBind_116_);
lean_closure_set(v___f_122_, 2, v___f_121_);
lean_closure_set(v___f_122_, 3, v_inst_108_);
lean_closure_set(v___f_122_, 4, v_inst_109_);
lean_closure_set(v___f_122_, 5, v___x_118_);
v___x_123_ = lean_apply_6(v_inst_113_, v___f_120_, lean_box(0), lean_box(0), v_it_114_, v___x_119_, v___f_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___boxed(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_m_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_it_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_IterM_toHashSet(v_00_u03b1_124_, v_00_u03b2_125_, v_inst_126_, v_inst_127_, v_m_128_, v_inst_129_, v_inst_130_, v_inst_131_, v_it_132_);
lean_dec(v_inst_130_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet___redArg(lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_it_138_){
_start:
{
lean_object* v_toApplicative_139_; lean_object* v_toBind_140_; lean_object* v_toPure_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___x_147_; 
v_toApplicative_139_ = lean_ctor_get(v_inst_136_, 0);
lean_inc_ref(v_toApplicative_139_);
v_toBind_140_ = lean_ctor_get(v_inst_136_, 1);
lean_inc_n(v_toBind_140_, 2);
lean_dec_ref(v_inst_136_);
v_toPure_141_ = lean_ctor_get(v_toApplicative_139_, 1);
lean_inc_n(v_toPure_141_, 2);
lean_dec_ref(v_toApplicative_139_);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__2, &l_Std_IterM_toHashSet___redArg___closed__2_once, _init_l_Std_IterM_toHashSet___redArg___closed__2);
v___f_144_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_144_, 0, v_toBind_140_);
v___f_145_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_145_, 0, v_toPure_141_);
v___f_146_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__2), 9, 6);
lean_closure_set(v___f_146_, 0, v_toPure_141_);
lean_closure_set(v___f_146_, 1, v_toBind_140_);
lean_closure_set(v___f_146_, 2, v___f_145_);
lean_closure_set(v___f_146_, 3, v_inst_134_);
lean_closure_set(v___f_146_, 4, v_inst_135_);
lean_closure_set(v___f_146_, 5, v___x_142_);
v___x_147_ = lean_apply_6(v_inst_137_, v___f_144_, lean_box(0), lean_box(0), v_it_138_, v___x_143_, v___f_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_m_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_it_157_){
_start:
{
lean_object* v_toApplicative_158_; lean_object* v_toBind_159_; lean_object* v_toPure_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___x_166_; 
v_toApplicative_158_ = lean_ctor_get(v_inst_153_, 0);
lean_inc_ref(v_toApplicative_158_);
v_toBind_159_ = lean_ctor_get(v_inst_153_, 1);
lean_inc_n(v_toBind_159_, 2);
lean_dec_ref(v_inst_153_);
v_toPure_160_ = lean_ctor_get(v_toApplicative_158_, 1);
lean_inc_n(v_toPure_160_, 2);
lean_dec_ref(v_toApplicative_158_);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__2, &l_Std_IterM_toHashSet___redArg___closed__2_once, _init_l_Std_IterM_toHashSet___redArg___closed__2);
v___f_163_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_163_, 0, v_toBind_159_);
v___f_164_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_164_, 0, v_toPure_160_);
v___f_165_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__2), 9, 6);
lean_closure_set(v___f_165_, 0, v_toPure_160_);
lean_closure_set(v___f_165_, 1, v_toBind_159_);
lean_closure_set(v___f_165_, 2, v___f_164_);
lean_closure_set(v___f_165_, 3, v_inst_150_);
lean_closure_set(v___f_165_, 4, v_inst_151_);
lean_closure_set(v___f_165_, 5, v___x_161_);
v___x_166_ = lean_apply_6(v_inst_156_, v___f_163_, lean_box(0), lean_box(0), v_it_157_, v___x_162_, v___f_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet___boxed(lean_object* v_00_u03b1_167_, lean_object* v_00_u03b2_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_m_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_it_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_IterM_Total_toHashSet(v_00_u03b1_167_, v_00_u03b2_168_, v_inst_169_, v_inst_170_, v_m_171_, v_inst_172_, v_inst_173_, v_inst_174_, v_inst_175_, v_it_176_);
lean_dec(v_inst_173_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___redArg___lam__1(lean_object* v_toPure_178_, lean_object* v_____do__lift_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_apply_2(v_toPure_178_, lean_box(0), v_____do__lift_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___redArg___lam__0(lean_object* v_toPure_181_, lean_object* v_toBind_182_, lean_object* v___f_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v___x_186_, lean_object* v_x1_187_, lean_object* v_x2_188_, lean_object* v_x3_189_){
_start:
{
lean_object* v___y_191_; lean_object* v___x_195_; lean_object* v___y_197_; lean_object* v_i_198_; lean_object* v___y_204_; lean_object* v___y_213_; lean_object* v_i_214_; lean_object* v___x_228_; 
v___x_195_ = lean_box(0);
lean_inc(v_x1_187_);
lean_inc_ref(v_inst_185_);
lean_inc_ref(v_inst_184_);
v___x_228_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_184_, v_inst_185_, v_x3_189_, v_x1_187_);
switch(lean_obj_tag(v___x_228_))
{
case 0:
{
lean_dec_ref_known(v___x_228_, 3);
lean_dec(v_x1_187_);
lean_dec(v___x_186_);
lean_dec_ref(v_inst_185_);
lean_dec_ref(v_inst_184_);
v___y_191_ = v_x3_189_;
goto v___jp_190_;
}
case 1:
{
lean_object* v_index_229_; lean_object* v_size_230_; lean_object* v_keyArray_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_index_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_index_229_);
lean_dec_ref_known(v___x_228_, 1);
v_size_230_ = lean_ctor_get(v_x3_189_, 0);
v_keyArray_231_ = lean_ctor_get(v_x3_189_, 1);
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_add(v_size_230_, v___x_232_);
v___x_234_ = lean_array_get_size(v_keyArray_231_);
v___x_235_ = lean_nat_dec_lt(v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
lean_dec(v___x_233_);
lean_dec(v_index_229_);
goto v___jp_219_;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_236_ = lean_unsigned_to_nat(4u);
v___x_237_ = lean_nat_mul(v___x_233_, v___x_236_);
v___x_238_ = lean_unsigned_to_nat(3u);
v___x_239_ = lean_nat_mul(v___x_234_, v___x_238_);
v___x_240_ = lean_nat_dec_le(v___x_237_, v___x_239_);
lean_dec(v___x_239_);
lean_dec(v___x_237_);
if (v___x_240_ == 0)
{
lean_dec(v___x_233_);
lean_dec(v_index_229_);
goto v___jp_219_;
}
else
{
lean_object* v___x_241_; 
lean_dec(v___x_186_);
lean_dec_ref(v_inst_185_);
lean_dec_ref(v_inst_184_);
v___x_241_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x3_189_, v___x_233_, v_index_229_, v_x1_187_, v___x_195_);
lean_dec(v_index_229_);
v___y_191_ = v___x_241_;
goto v___jp_190_;
}
}
}
default: 
{
lean_object* v_size_242_; lean_object* v_keyArray_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v_size_242_ = lean_ctor_get(v_x3_189_, 0);
v_keyArray_243_ = lean_ctor_get(v_x3_189_, 1);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_add(v_size_242_, v___x_244_);
v___x_246_ = lean_array_get_size(v_keyArray_243_);
v___x_247_ = lean_nat_dec_lt(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec(v___x_245_);
lean_inc_ref(v_inst_185_);
lean_inc_ref(v_inst_184_);
v___x_248_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_184_, v_inst_185_, v_x3_189_);
v___y_204_ = v___x_248_;
goto v___jp_203_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_249_ = lean_unsigned_to_nat(4u);
v___x_250_ = lean_nat_mul(v___x_245_, v___x_249_);
lean_dec(v___x_245_);
v___x_251_ = lean_unsigned_to_nat(3u);
v___x_252_ = lean_nat_mul(v___x_246_, v___x_251_);
v___x_253_ = lean_nat_dec_le(v___x_250_, v___x_252_);
lean_dec(v___x_252_);
lean_dec(v___x_250_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_inc_ref(v_inst_185_);
lean_inc_ref(v_inst_184_);
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_184_, v_inst_185_, v_x3_189_);
v___y_204_ = v___x_254_;
goto v___jp_203_;
}
else
{
v___y_204_ = v_x3_189_;
goto v___jp_203_;
}
}
}
}
v___jp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v___y_191_);
v___x_193_ = lean_apply_2(v_toPure_181_, lean_box(0), v___x_192_);
v___x_194_ = lean_apply_4(v_toBind_182_, lean_box(0), lean_box(0), v___x_193_, v___f_183_);
return v___x_194_;
}
v___jp_196_:
{
lean_object* v_size_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_size_199_ = lean_ctor_get(v___y_197_, 0);
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_add(v_size_199_, v___x_200_);
v___x_202_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_197_, v___x_201_, v_i_198_, v_x1_187_, v___x_195_);
lean_dec(v_i_198_);
v___y_191_ = v___x_202_;
goto v___jp_190_;
}
v___jp_203_:
{
lean_object* v___x_205_; 
lean_inc(v_x1_187_);
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_184_, v_inst_185_, v___y_204_, v_x1_187_);
switch(lean_obj_tag(v___x_205_))
{
case 0:
{
lean_object* v_index_206_; lean_object* v_size_207_; lean_object* v___x_208_; 
lean_dec(v___x_186_);
v_index_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_index_206_);
lean_dec_ref_known(v___x_205_, 3);
v_size_207_ = lean_ctor_get(v___y_204_, 0);
lean_inc(v_size_207_);
v___x_208_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_204_, v_size_207_, v_index_206_, v_x1_187_, v___x_195_);
lean_dec(v_index_206_);
v___y_191_ = v___x_208_;
goto v___jp_190_;
}
case 1:
{
lean_object* v_index_209_; 
lean_dec(v___x_186_);
v_index_209_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_index_209_);
lean_dec_ref_known(v___x_205_, 1);
v___y_197_ = v___y_204_;
v_i_198_ = v_index_209_;
goto v___jp_196_;
}
default: 
{
lean_object* v___x_210_; 
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_204_, v___x_186_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_index_211_; 
v_index_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_index_211_);
lean_dec_ref_known(v___x_210_, 1);
v___y_197_ = v___y_204_;
v_i_198_ = v_index_211_;
goto v___jp_196_;
}
else
{
lean_dec(v_x1_187_);
v___y_191_ = v___y_204_;
goto v___jp_190_;
}
}
}
}
v___jp_212_:
{
lean_object* v_size_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_size_215_ = lean_ctor_get(v___y_213_, 0);
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_add(v_size_215_, v___x_216_);
v___x_218_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_213_, v___x_217_, v_i_214_, v_x1_187_, v___x_195_);
lean_dec(v_i_214_);
v___y_191_ = v___x_218_;
goto v___jp_190_;
}
v___jp_219_:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_inc_ref(v_inst_185_);
lean_inc_ref(v_inst_184_);
v___x_220_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_184_, v_inst_185_, v_x3_189_);
lean_inc(v_x1_187_);
v___x_221_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_184_, v_inst_185_, v___x_220_, v_x1_187_);
switch(lean_obj_tag(v___x_221_))
{
case 0:
{
lean_object* v_index_222_; lean_object* v_size_223_; lean_object* v___x_224_; 
lean_dec(v___x_186_);
v_index_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_index_222_);
lean_dec_ref_known(v___x_221_, 3);
v_size_223_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_size_223_);
v___x_224_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_220_, v_size_223_, v_index_222_, v_x1_187_, v___x_195_);
lean_dec(v_index_222_);
v___y_191_ = v___x_224_;
goto v___jp_190_;
}
case 1:
{
lean_object* v_index_225_; 
lean_dec(v___x_186_);
v_index_225_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_index_225_);
lean_dec_ref_known(v___x_221_, 1);
v___y_213_ = v___x_220_;
v_i_214_ = v_index_225_;
goto v___jp_212_;
}
default: 
{
lean_object* v___x_226_; 
v___x_226_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_220_, v___x_186_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_index_227_; 
v_index_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_index_227_);
lean_dec_ref_known(v___x_226_, 1);
v___y_213_ = v___x_220_;
v_i_214_ = v_index_227_;
goto v___jp_212_;
}
else
{
lean_dec(v_x1_187_);
v___y_191_ = v___x_220_;
goto v___jp_190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___redArg(lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_it_259_){
_start:
{
lean_object* v_toApplicative_260_; lean_object* v_toBind_261_; lean_object* v_toPure_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___f_265_; lean_object* v___f_266_; lean_object* v___f_267_; lean_object* v___x_268_; 
v_toApplicative_260_ = lean_ctor_get(v_inst_257_, 0);
lean_inc_ref(v_toApplicative_260_);
v_toBind_261_ = lean_ctor_get(v_inst_257_, 1);
lean_inc_n(v_toBind_261_, 2);
lean_dec_ref(v_inst_257_);
v_toPure_262_ = lean_ctor_get(v_toApplicative_260_, 1);
lean_inc_n(v_toPure_262_, 2);
lean_dec_ref(v_toApplicative_260_);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__2, &l_Std_IterM_toHashSet___redArg___closed__2_once, _init_l_Std_IterM_toHashSet___redArg___closed__2);
v___f_265_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_265_, 0, v_toBind_261_);
v___f_266_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_266_, 0, v_toPure_262_);
v___f_267_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__0), 9, 6);
lean_closure_set(v___f_267_, 0, v_toPure_262_);
lean_closure_set(v___f_267_, 1, v_toBind_261_);
lean_closure_set(v___f_267_, 2, v___f_266_);
lean_closure_set(v___f_267_, 3, v_inst_255_);
lean_closure_set(v___f_267_, 4, v_inst_256_);
lean_closure_set(v___f_267_, 5, v___x_263_);
v___x_268_ = lean_apply_6(v_inst_258_, v___f_265_, lean_box(0), lean_box(0), v_it_259_, v___x_264_, v___f_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_m_275_, lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_it_279_){
_start:
{
lean_object* v_toApplicative_280_; lean_object* v_toBind_281_; lean_object* v_toPure_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___f_285_; lean_object* v___f_286_; lean_object* v___f_287_; lean_object* v___x_288_; 
v_toApplicative_280_ = lean_ctor_get(v_inst_276_, 0);
lean_inc_ref(v_toApplicative_280_);
v_toBind_281_ = lean_ctor_get(v_inst_276_, 1);
lean_inc_n(v_toBind_281_, 2);
lean_dec_ref(v_inst_276_);
v_toPure_282_ = lean_ctor_get(v_toApplicative_280_, 1);
lean_inc_n(v_toPure_282_, 2);
lean_dec_ref(v_toApplicative_280_);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__2, &l_Std_IterM_toHashSet___redArg___closed__2_once, _init_l_Std_IterM_toHashSet___redArg___closed__2);
v___f_285_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_285_, 0, v_toBind_281_);
v___f_286_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_286_, 0, v_toPure_282_);
v___f_287_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__0), 9, 6);
lean_closure_set(v___f_287_, 0, v_toPure_282_);
lean_closure_set(v___f_287_, 1, v_toBind_281_);
lean_closure_set(v___f_287_, 2, v___f_286_);
lean_closure_set(v___f_287_, 3, v_inst_271_);
lean_closure_set(v___f_287_, 4, v_inst_272_);
lean_closure_set(v___f_287_, 5, v___x_283_);
v___x_288_ = lean_apply_6(v_inst_278_, v___f_285_, lean_box(0), lean_box(0), v_it_279_, v___x_284_, v___f_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___boxed(lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_m_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_it_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_IterM_toExtHashSet(v_00_u03b1_289_, v_00_u03b2_290_, v_inst_291_, v_inst_292_, v_inst_293_, v_inst_294_, v_m_295_, v_inst_296_, v_inst_297_, v_inst_298_, v_it_299_);
lean_dec(v_inst_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtHashSet___redArg(lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_it_305_){
_start:
{
lean_object* v_toApplicative_306_; lean_object* v_toBind_307_; lean_object* v_toPure_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___f_311_; lean_object* v___f_312_; lean_object* v___f_313_; lean_object* v___x_314_; 
v_toApplicative_306_ = lean_ctor_get(v_inst_303_, 0);
lean_inc_ref(v_toApplicative_306_);
v_toBind_307_ = lean_ctor_get(v_inst_303_, 1);
lean_inc_n(v_toBind_307_, 2);
lean_dec_ref(v_inst_303_);
v_toPure_308_ = lean_ctor_get(v_toApplicative_306_, 1);
lean_inc_n(v_toPure_308_, 2);
lean_dec_ref(v_toApplicative_306_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__2, &l_Std_IterM_toHashSet___redArg___closed__2_once, _init_l_Std_IterM_toHashSet___redArg___closed__2);
v___f_311_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_311_, 0, v_toBind_307_);
v___f_312_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_312_, 0, v_toPure_308_);
v___f_313_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__0), 9, 6);
lean_closure_set(v___f_313_, 0, v_toPure_308_);
lean_closure_set(v___f_313_, 1, v_toBind_307_);
lean_closure_set(v___f_313_, 2, v___f_312_);
lean_closure_set(v___f_313_, 3, v_inst_301_);
lean_closure_set(v___f_313_, 4, v_inst_302_);
lean_closure_set(v___f_313_, 5, v___x_309_);
v___x_314_ = lean_apply_6(v_inst_304_, v___f_311_, lean_box(0), lean_box(0), v_it_305_, v___x_310_, v___f_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtHashSet(lean_object* v_00_u03b1_315_, lean_object* v_00_u03b2_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_m_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_it_326_){
_start:
{
lean_object* v_toApplicative_327_; lean_object* v_toBind_328_; lean_object* v_toPure_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___f_332_; lean_object* v___f_333_; lean_object* v___f_334_; lean_object* v___x_335_; 
v_toApplicative_327_ = lean_ctor_get(v_inst_322_, 0);
lean_inc_ref(v_toApplicative_327_);
v_toBind_328_ = lean_ctor_get(v_inst_322_, 1);
lean_inc_n(v_toBind_328_, 2);
lean_dec_ref(v_inst_322_);
v_toPure_329_ = lean_ctor_get(v_toApplicative_327_, 1);
lean_inc_n(v_toPure_329_, 2);
lean_dec_ref(v_toApplicative_327_);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__2, &l_Std_IterM_toHashSet___redArg___closed__2_once, _init_l_Std_IterM_toHashSet___redArg___closed__2);
v___f_332_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_332_, 0, v_toBind_328_);
v___f_333_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_333_, 0, v_toPure_329_);
v___f_334_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__0), 9, 6);
lean_closure_set(v___f_334_, 0, v_toPure_329_);
lean_closure_set(v___f_334_, 1, v_toBind_328_);
lean_closure_set(v___f_334_, 2, v___f_333_);
lean_closure_set(v___f_334_, 3, v_inst_317_);
lean_closure_set(v___f_334_, 4, v_inst_318_);
lean_closure_set(v___f_334_, 5, v___x_330_);
v___x_335_ = lean_apply_6(v_inst_325_, v___f_332_, lean_box(0), lean_box(0), v_it_326_, v___x_331_, v___f_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtHashSet___boxed(lean_object* v_00_u03b1_336_, lean_object* v_00_u03b2_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_m_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_it_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_IterM_Total_toExtHashSet(v_00_u03b1_336_, v_00_u03b2_337_, v_inst_338_, v_inst_339_, v_inst_340_, v_inst_341_, v_m_342_, v_inst_343_, v_inst_344_, v_inst_345_, v_inst_346_, v_it_347_);
lean_dec(v_inst_344_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___redArg___lam__1(lean_object* v_toPure_349_, lean_object* v_____do__lift_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_apply_2(v_toPure_349_, lean_box(0), v_____do__lift_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___redArg___lam__0(lean_object* v_toPure_352_, lean_object* v_toBind_353_, lean_object* v___f_354_, lean_object* v_cmp_355_, lean_object* v_x1_356_, lean_object* v_x2_357_, lean_object* v_x3_358_){
_start:
{
lean_object* v___y_360_; uint8_t v___x_364_; 
lean_inc(v_x3_358_);
lean_inc(v_x1_356_);
lean_inc_ref(v_cmp_355_);
v___x_364_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_355_, v_x1_356_, v_x3_358_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_box(0);
v___x_366_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_355_, v_x1_356_, v___x_365_, v_x3_358_);
v___y_360_ = v___x_366_;
goto v___jp_359_;
}
else
{
lean_dec(v_x1_356_);
lean_dec_ref(v_cmp_355_);
v___y_360_ = v_x3_358_;
goto v___jp_359_;
}
v___jp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v___y_360_);
v___x_362_ = lean_apply_2(v_toPure_352_, lean_box(0), v___x_361_);
v___x_363_ = lean_apply_4(v_toBind_353_, lean_box(0), lean_box(0), v___x_362_, v___f_354_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___redArg(lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_it_369_, lean_object* v_cmp_370_){
_start:
{
lean_object* v_toApplicative_371_; lean_object* v_toBind_372_; lean_object* v_toPure_373_; lean_object* v___x_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___x_378_; 
v_toApplicative_371_ = lean_ctor_get(v_inst_367_, 0);
lean_inc_ref(v_toApplicative_371_);
v_toBind_372_ = lean_ctor_get(v_inst_367_, 1);
lean_inc_n(v_toBind_372_, 2);
lean_dec_ref(v_inst_367_);
v_toPure_373_ = lean_ctor_get(v_toApplicative_371_, 1);
lean_inc_n(v_toPure_373_, 2);
lean_dec_ref(v_toApplicative_371_);
v___x_374_ = lean_box(1);
v___f_375_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_375_, 0, v_toBind_372_);
v___f_376_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_376_, 0, v_toPure_373_);
v___f_377_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__0), 7, 4);
lean_closure_set(v___f_377_, 0, v_toPure_373_);
lean_closure_set(v___f_377_, 1, v_toBind_372_);
lean_closure_set(v___f_377_, 2, v___f_376_);
lean_closure_set(v___f_377_, 3, v_cmp_370_);
v___x_378_ = lean_apply_6(v_inst_368_, v___f_375_, lean_box(0), lean_box(0), v_it_369_, v___x_374_, v___f_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_m_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_it_385_, lean_object* v_cmp_386_){
_start:
{
lean_object* v_toApplicative_387_; lean_object* v_toBind_388_; lean_object* v_toPure_389_; lean_object* v___x_390_; lean_object* v___f_391_; lean_object* v___f_392_; lean_object* v___f_393_; lean_object* v___x_394_; 
v_toApplicative_387_ = lean_ctor_get(v_inst_382_, 0);
lean_inc_ref(v_toApplicative_387_);
v_toBind_388_ = lean_ctor_get(v_inst_382_, 1);
lean_inc_n(v_toBind_388_, 2);
lean_dec_ref(v_inst_382_);
v_toPure_389_ = lean_ctor_get(v_toApplicative_387_, 1);
lean_inc_n(v_toPure_389_, 2);
lean_dec_ref(v_toApplicative_387_);
v___x_390_ = lean_box(1);
v___f_391_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_391_, 0, v_toBind_388_);
v___f_392_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_392_, 0, v_toPure_389_);
v___f_393_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__0), 7, 4);
lean_closure_set(v___f_393_, 0, v_toPure_389_);
lean_closure_set(v___f_393_, 1, v_toBind_388_);
lean_closure_set(v___f_393_, 2, v___f_392_);
lean_closure_set(v___f_393_, 3, v_cmp_386_);
v___x_394_ = lean_apply_6(v_inst_384_, v___f_391_, lean_box(0), lean_box(0), v_it_385_, v___x_390_, v___f_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___boxed(lean_object* v_00_u03b1_395_, lean_object* v_00_u03b2_396_, lean_object* v_m_397_, lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_it_401_, lean_object* v_cmp_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_IterM_toTreeSet(v_00_u03b1_395_, v_00_u03b2_396_, v_m_397_, v_inst_398_, v_inst_399_, v_inst_400_, v_it_401_, v_cmp_402_);
lean_dec(v_inst_399_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toTreeSet___redArg(lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_it_406_, lean_object* v_cmp_407_){
_start:
{
lean_object* v_toApplicative_408_; lean_object* v_toBind_409_; lean_object* v_toPure_410_; lean_object* v___x_411_; lean_object* v___f_412_; lean_object* v___f_413_; lean_object* v___f_414_; lean_object* v___x_415_; 
v_toApplicative_408_ = lean_ctor_get(v_inst_404_, 0);
lean_inc_ref(v_toApplicative_408_);
v_toBind_409_ = lean_ctor_get(v_inst_404_, 1);
lean_inc_n(v_toBind_409_, 2);
lean_dec_ref(v_inst_404_);
v_toPure_410_ = lean_ctor_get(v_toApplicative_408_, 1);
lean_inc_n(v_toPure_410_, 2);
lean_dec_ref(v_toApplicative_408_);
v___x_411_ = lean_box(1);
v___f_412_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_412_, 0, v_toBind_409_);
v___f_413_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_413_, 0, v_toPure_410_);
v___f_414_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__0), 7, 4);
lean_closure_set(v___f_414_, 0, v_toPure_410_);
lean_closure_set(v___f_414_, 1, v_toBind_409_);
lean_closure_set(v___f_414_, 2, v___f_413_);
lean_closure_set(v___f_414_, 3, v_cmp_407_);
v___x_415_ = lean_apply_6(v_inst_405_, v___f_412_, lean_box(0), lean_box(0), v_it_406_, v___x_411_, v___f_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toTreeSet(lean_object* v_00_u03b1_416_, lean_object* v_00_u03b2_417_, lean_object* v_m_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_it_423_, lean_object* v_cmp_424_){
_start:
{
lean_object* v_toApplicative_425_; lean_object* v_toBind_426_; lean_object* v_toPure_427_; lean_object* v___x_428_; lean_object* v___f_429_; lean_object* v___f_430_; lean_object* v___f_431_; lean_object* v___x_432_; 
v_toApplicative_425_ = lean_ctor_get(v_inst_419_, 0);
lean_inc_ref(v_toApplicative_425_);
v_toBind_426_ = lean_ctor_get(v_inst_419_, 1);
lean_inc_n(v_toBind_426_, 2);
lean_dec_ref(v_inst_419_);
v_toPure_427_ = lean_ctor_get(v_toApplicative_425_, 1);
lean_inc_n(v_toPure_427_, 2);
lean_dec_ref(v_toApplicative_425_);
v___x_428_ = lean_box(1);
v___f_429_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_429_, 0, v_toBind_426_);
v___f_430_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_430_, 0, v_toPure_427_);
v___f_431_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__0), 7, 4);
lean_closure_set(v___f_431_, 0, v_toPure_427_);
lean_closure_set(v___f_431_, 1, v_toBind_426_);
lean_closure_set(v___f_431_, 2, v___f_430_);
lean_closure_set(v___f_431_, 3, v_cmp_424_);
v___x_432_ = lean_apply_6(v_inst_422_, v___f_429_, lean_box(0), lean_box(0), v_it_423_, v___x_428_, v___f_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toTreeSet___boxed(lean_object* v_00_u03b1_433_, lean_object* v_00_u03b2_434_, lean_object* v_m_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_it_440_, lean_object* v_cmp_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_IterM_Total_toTreeSet(v_00_u03b1_433_, v_00_u03b2_434_, v_m_435_, v_inst_436_, v_inst_437_, v_inst_438_, v_inst_439_, v_it_440_, v_cmp_441_);
lean_dec(v_inst_437_);
return v_res_442_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__12(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__10));
v___x_470_ = l_Lean_mkAtom(v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__13(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__12, &l_Std_IterM_toExtTreeSet___auto__1___closed__12_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__12);
v___x_472_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__5));
v___x_473_ = lean_array_push(v___x_472_, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__15(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__14));
v___x_476_ = lean_string_utf8_byte_size(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__16(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_477_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__15, &l_Std_IterM_toExtTreeSet___auto__1___closed__15_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__15);
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__14));
v___x_480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
lean_ctor_set(v___x_480_, 2, v___x_477_);
return v___x_480_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__18(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_483_ = lean_box(0);
v___x_484_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__17));
v___x_485_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__16, &l_Std_IterM_toExtTreeSet___auto__1___closed__16_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__16);
v___x_486_ = lean_box(2);
v___x_487_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_484_);
lean_ctor_set(v___x_487_, 3, v___x_483_);
return v___x_487_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__19(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__18, &l_Std_IterM_toExtTreeSet___auto__1___closed__18_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__18);
v___x_489_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__13, &l_Std_IterM_toExtTreeSet___auto__1___closed__13_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__13);
v___x_490_ = lean_array_push(v___x_489_, v___x_488_);
return v___x_490_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__20(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_491_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__19, &l_Std_IterM_toExtTreeSet___auto__1___closed__19_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__19);
v___x_492_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__11));
v___x_493_ = lean_box(2);
v___x_494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
lean_ctor_set(v___x_494_, 2, v___x_491_);
return v___x_494_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__21(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__20, &l_Std_IterM_toExtTreeSet___auto__1___closed__20_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__20);
v___x_496_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__5));
v___x_497_ = lean_array_push(v___x_496_, v___x_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__22(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__21, &l_Std_IterM_toExtTreeSet___auto__1___closed__21_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__21);
v___x_499_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__9));
v___x_500_ = lean_box(2);
v___x_501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_499_);
lean_ctor_set(v___x_501_, 2, v___x_498_);
return v___x_501_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__23(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__22, &l_Std_IterM_toExtTreeSet___auto__1___closed__22_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__22);
v___x_503_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__5));
v___x_504_ = lean_array_push(v___x_503_, v___x_502_);
return v___x_504_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__24(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_505_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__23, &l_Std_IterM_toExtTreeSet___auto__1___closed__23_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__23);
v___x_506_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__7));
v___x_507_ = lean_box(2);
v___x_508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v___x_506_);
lean_ctor_set(v___x_508_, 2, v___x_505_);
return v___x_508_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__25(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__24, &l_Std_IterM_toExtTreeSet___auto__1___closed__24_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__24);
v___x_510_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__5));
v___x_511_ = lean_array_push(v___x_510_, v___x_509_);
return v___x_511_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__26(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_512_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__25, &l_Std_IterM_toExtTreeSet___auto__1___closed__25_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__25);
v___x_513_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__4));
v___x_514_ = lean_box(2);
v___x_515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v___x_513_);
lean_ctor_set(v___x_515_, 2, v___x_512_);
return v___x_515_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1(void){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__26, &l_Std_IterM_toExtTreeSet___auto__1___closed__26_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__26);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet___redArg___lam__2(lean_object* v_toPure_517_, lean_object* v_toBind_518_, lean_object* v___f_519_, lean_object* v_cmp_520_, lean_object* v_x1_521_, lean_object* v_x2_522_, lean_object* v_x3_523_){
_start:
{
lean_object* v___y_525_; uint8_t v___x_529_; 
lean_inc(v_x3_523_);
lean_inc(v_x1_521_);
lean_inc_ref(v_cmp_520_);
v___x_529_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_520_, v_x1_521_, v_x3_523_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_box(0);
v___x_531_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_520_, v_x1_521_, v___x_530_, v_x3_523_);
v___y_525_ = v___x_531_;
goto v___jp_524_;
}
else
{
lean_dec(v_x1_521_);
lean_dec_ref(v_cmp_520_);
v___y_525_ = v_x3_523_;
goto v___jp_524_;
}
v___jp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___y_525_);
v___x_527_ = lean_apply_2(v_toPure_517_, lean_box(0), v___x_526_);
v___x_528_ = lean_apply_4(v_toBind_518_, lean_box(0), lean_box(0), v___x_527_, v___f_519_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet___redArg(lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_it_534_, lean_object* v_cmp_535_){
_start:
{
lean_object* v_toApplicative_536_; lean_object* v_toBind_537_; lean_object* v_toPure_538_; lean_object* v___x_539_; lean_object* v___f_540_; lean_object* v___f_541_; lean_object* v___f_542_; lean_object* v___x_543_; 
v_toApplicative_536_ = lean_ctor_get(v_inst_532_, 0);
lean_inc_ref(v_toApplicative_536_);
v_toBind_537_ = lean_ctor_get(v_inst_532_, 1);
lean_inc_n(v_toBind_537_, 2);
lean_dec_ref(v_inst_532_);
v_toPure_538_ = lean_ctor_get(v_toApplicative_536_, 1);
lean_inc_n(v_toPure_538_, 2);
lean_dec_ref(v_toApplicative_536_);
v___x_539_ = lean_box(1);
v___f_540_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_540_, 0, v_toBind_537_);
v___f_541_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_541_, 0, v_toPure_538_);
v___f_542_ = lean_alloc_closure((void*)(l_Std_IterM_toExtTreeSet___redArg___lam__2), 7, 4);
lean_closure_set(v___f_542_, 0, v_toPure_538_);
lean_closure_set(v___f_542_, 1, v_toBind_537_);
lean_closure_set(v___f_542_, 2, v___f_541_);
lean_closure_set(v___f_542_, 3, v_cmp_535_);
v___x_543_ = lean_apply_6(v_inst_533_, v___f_540_, lean_box(0), lean_box(0), v_it_534_, v___x_539_, v___f_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet(lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_m_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_it_550_, lean_object* v_cmp_551_, lean_object* v_inst_552_){
_start:
{
lean_object* v_toApplicative_553_; lean_object* v_toBind_554_; lean_object* v_toPure_555_; lean_object* v___x_556_; lean_object* v___f_557_; lean_object* v___f_558_; lean_object* v___f_559_; lean_object* v___x_560_; 
v_toApplicative_553_ = lean_ctor_get(v_inst_547_, 0);
lean_inc_ref(v_toApplicative_553_);
v_toBind_554_ = lean_ctor_get(v_inst_547_, 1);
lean_inc_n(v_toBind_554_, 2);
lean_dec_ref(v_inst_547_);
v_toPure_555_ = lean_ctor_get(v_toApplicative_553_, 1);
lean_inc_n(v_toPure_555_, 2);
lean_dec_ref(v_toApplicative_553_);
v___x_556_ = lean_box(1);
v___f_557_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_557_, 0, v_toBind_554_);
v___f_558_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_558_, 0, v_toPure_555_);
v___f_559_ = lean_alloc_closure((void*)(l_Std_IterM_toExtTreeSet___redArg___lam__2), 7, 4);
lean_closure_set(v___f_559_, 0, v_toPure_555_);
lean_closure_set(v___f_559_, 1, v_toBind_554_);
lean_closure_set(v___f_559_, 2, v___f_558_);
lean_closure_set(v___f_559_, 3, v_cmp_551_);
v___x_560_ = lean_apply_6(v_inst_549_, v___f_557_, lean_box(0), lean_box(0), v_it_550_, v___x_556_, v___f_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet___boxed(lean_object* v_00_u03b1_561_, lean_object* v_00_u03b2_562_, lean_object* v_m_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_it_567_, lean_object* v_cmp_568_, lean_object* v_inst_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_IterM_toExtTreeSet(v_00_u03b1_561_, v_00_u03b2_562_, v_m_563_, v_inst_564_, v_inst_565_, v_inst_566_, v_it_567_, v_cmp_568_, v_inst_569_);
lean_dec(v_inst_565_);
return v_res_570_;
}
}
static lean_object* _init_l_Std_IterM_Total_toExtTreeSet___auto__1(void){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__26, &l_Std_IterM_toExtTreeSet___auto__1___closed__26_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__26);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtTreeSet___redArg(lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_it_574_, lean_object* v_cmp_575_){
_start:
{
lean_object* v_toApplicative_576_; lean_object* v_toBind_577_; lean_object* v_toPure_578_; lean_object* v___x_579_; lean_object* v___f_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___x_583_; 
v_toApplicative_576_ = lean_ctor_get(v_inst_572_, 0);
lean_inc_ref(v_toApplicative_576_);
v_toBind_577_ = lean_ctor_get(v_inst_572_, 1);
lean_inc_n(v_toBind_577_, 2);
lean_dec_ref(v_inst_572_);
v_toPure_578_ = lean_ctor_get(v_toApplicative_576_, 1);
lean_inc_n(v_toPure_578_, 2);
lean_dec_ref(v_toApplicative_576_);
v___x_579_ = lean_box(1);
v___f_580_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_580_, 0, v_toBind_577_);
v___f_581_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_581_, 0, v_toPure_578_);
v___f_582_ = lean_alloc_closure((void*)(l_Std_IterM_toExtTreeSet___redArg___lam__2), 7, 4);
lean_closure_set(v___f_582_, 0, v_toPure_578_);
lean_closure_set(v___f_582_, 1, v_toBind_577_);
lean_closure_set(v___f_582_, 2, v___f_581_);
lean_closure_set(v___f_582_, 3, v_cmp_575_);
v___x_583_ = lean_apply_6(v_inst_573_, v___f_580_, lean_box(0), lean_box(0), v_it_574_, v___x_579_, v___f_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtTreeSet(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_m_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_it_591_, lean_object* v_cmp_592_, lean_object* v_inst_593_){
_start:
{
lean_object* v_toApplicative_594_; lean_object* v_toBind_595_; lean_object* v_toPure_596_; lean_object* v___x_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___x_601_; 
v_toApplicative_594_ = lean_ctor_get(v_inst_587_, 0);
lean_inc_ref(v_toApplicative_594_);
v_toBind_595_ = lean_ctor_get(v_inst_587_, 1);
lean_inc_n(v_toBind_595_, 2);
lean_dec_ref(v_inst_587_);
v_toPure_596_ = lean_ctor_get(v_toApplicative_594_, 1);
lean_inc_n(v_toPure_596_, 2);
lean_dec_ref(v_toApplicative_594_);
v___x_597_ = lean_box(1);
v___f_598_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_598_, 0, v_toBind_595_);
v___f_599_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_599_, 0, v_toPure_596_);
v___f_600_ = lean_alloc_closure((void*)(l_Std_IterM_toExtTreeSet___redArg___lam__2), 7, 4);
lean_closure_set(v___f_600_, 0, v_toPure_596_);
lean_closure_set(v___f_600_, 1, v_toBind_595_);
lean_closure_set(v___f_600_, 2, v___f_599_);
lean_closure_set(v___f_600_, 3, v_cmp_592_);
v___x_601_ = lean_apply_6(v_inst_590_, v___f_598_, lean_box(0), lean_box(0), v_it_591_, v___x_597_, v___f_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtTreeSet___boxed(lean_object* v_00_u03b1_602_, lean_object* v_00_u03b2_603_, lean_object* v_m_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_it_609_, lean_object* v_cmp_610_, lean_object* v_inst_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_IterM_Total_toExtTreeSet(v_00_u03b1_602_, v_00_u03b2_603_, v_m_604_, v_inst_605_, v_inst_606_, v_inst_607_, v_inst_608_, v_it_609_, v_cmp_610_, v_inst_611_);
lean_dec(v_inst_606_);
return v_res_612_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_ExtHashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_ExtTreeSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Consumers_Monadic_Set(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_ExtHashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_ExtTreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Consumers_Monadic_Set(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_IterM_toExtTreeSet___auto__1 = _init_l_Std_IterM_toExtTreeSet___auto__1();
lean_mark_persistent(l_Std_IterM_toExtTreeSet___auto__1);
l_Std_IterM_Total_toExtTreeSet___auto__1 = _init_l_Std_IterM_Total_toExtTreeSet___auto__1();
lean_mark_persistent(l_Std_IterM_Total_toExtTreeSet___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_ExtHashSet_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_ExtTreeSet_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Consumers_Monadic_Set(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_ExtHashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_ExtTreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Consumers_Monadic_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Consumers_Monadic_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Consumers_Monadic_Set(builtin);
}
#ifdef __cplusplus
}
#endif
