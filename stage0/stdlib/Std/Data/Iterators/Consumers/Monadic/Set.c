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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_IterM_toHashSet___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toHashSet___redArg___closed__0;
static lean_once_cell_t l_Std_IterM_toHashSet___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IterM_toHashSet___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg___lam__2(lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_toPure_12_, lean_object* v_toBind_13_, lean_object* v___f_14_, lean_object* v_x1_15_, lean_object* v_x2_16_, lean_object* v_x3_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_18_ = lean_box(0);
v___x_19_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_10_, v_inst_11_, v_x3_17_, v_x1_15_, v___x_18_);
v___x_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
v___x_21_ = lean_apply_2(v_toPure_12_, lean_box(0), v___x_20_);
v___x_22_ = lean_apply_4(v_toBind_13_, lean_box(0), lean_box(0), v___x_21_, v___f_14_);
return v___x_22_;
}
}
static lean_object* _init_l_Std_IterM_toHashSet___redArg___closed__0(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = lean_box(0);
v___x_24_ = lean_unsigned_to_nat(16u);
v___x_25_ = lean_mk_array(v___x_24_, v___x_23_);
return v___x_25_;
}
}
static lean_object* _init_l_Std_IterM_toHashSet___redArg___closed__1(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__0, &l_Std_IterM_toHashSet___redArg___closed__0_once, _init_l_Std_IterM_toHashSet___redArg___closed__0);
v___x_27_ = lean_unsigned_to_nat(0u);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v___x_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___redArg(lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_it_33_){
_start:
{
lean_object* v_toApplicative_34_; lean_object* v_toBind_35_; lean_object* v_toPure_36_; lean_object* v___x_37_; lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___f_40_; lean_object* v___x_41_; 
v_toApplicative_34_ = lean_ctor_get(v_inst_31_, 0);
lean_inc_ref(v_toApplicative_34_);
v_toBind_35_ = lean_ctor_get(v_inst_31_, 1);
lean_inc(v_toBind_35_);
lean_dec_ref(v_inst_31_);
v_toPure_36_ = lean_ctor_get(v_toApplicative_34_, 1);
lean_inc(v_toPure_36_);
lean_dec_ref(v_toApplicative_34_);
v___x_37_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__1, &l_Std_IterM_toHashSet___redArg___closed__1_once, _init_l_Std_IterM_toHashSet___redArg___closed__1);
lean_inc(v_toBind_35_);
v___f_38_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_38_, 0, v_toBind_35_);
lean_inc(v_toPure_36_);
v___f_39_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_39_, 0, v_toPure_36_);
v___f_40_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__2), 8, 5);
lean_closure_set(v___f_40_, 0, v_inst_29_);
lean_closure_set(v___f_40_, 1, v_inst_30_);
lean_closure_set(v___f_40_, 2, v_toPure_36_);
lean_closure_set(v___f_40_, 3, v_toBind_35_);
lean_closure_set(v___f_40_, 4, v___f_39_);
v___x_41_ = lean_apply_6(v_inst_32_, v___f_38_, lean_box(0), lean_box(0), v_it_33_, v___x_37_, v___f_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet(lean_object* v_00_u03b1_42_, lean_object* v_00_u03b2_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_m_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_it_50_){
_start:
{
lean_object* v_toApplicative_51_; lean_object* v_toBind_52_; lean_object* v_toPure_53_; lean_object* v___x_54_; lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___x_58_; 
v_toApplicative_51_ = lean_ctor_get(v_inst_47_, 0);
lean_inc_ref(v_toApplicative_51_);
v_toBind_52_ = lean_ctor_get(v_inst_47_, 1);
lean_inc(v_toBind_52_);
lean_dec_ref(v_inst_47_);
v_toPure_53_ = lean_ctor_get(v_toApplicative_51_, 1);
lean_inc(v_toPure_53_);
lean_dec_ref(v_toApplicative_51_);
v___x_54_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__1, &l_Std_IterM_toHashSet___redArg___closed__1_once, _init_l_Std_IterM_toHashSet___redArg___closed__1);
lean_inc(v_toBind_52_);
v___f_55_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_55_, 0, v_toBind_52_);
lean_inc(v_toPure_53_);
v___f_56_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_56_, 0, v_toPure_53_);
v___f_57_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__2), 8, 5);
lean_closure_set(v___f_57_, 0, v_inst_44_);
lean_closure_set(v___f_57_, 1, v_inst_45_);
lean_closure_set(v___f_57_, 2, v_toPure_53_);
lean_closure_set(v___f_57_, 3, v_toBind_52_);
lean_closure_set(v___f_57_, 4, v___f_56_);
v___x_58_ = lean_apply_6(v_inst_49_, v___f_55_, lean_box(0), lean_box(0), v_it_50_, v___x_54_, v___f_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toHashSet___boxed(lean_object* v_00_u03b1_59_, lean_object* v_00_u03b2_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_m_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_it_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_IterM_toHashSet(v_00_u03b1_59_, v_00_u03b2_60_, v_inst_61_, v_inst_62_, v_m_63_, v_inst_64_, v_inst_65_, v_inst_66_, v_it_67_);
lean_dec(v_inst_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet___redArg(lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_it_73_){
_start:
{
lean_object* v_toApplicative_74_; lean_object* v_toBind_75_; lean_object* v_toPure_76_; lean_object* v___x_77_; lean_object* v___f_78_; lean_object* v___f_79_; lean_object* v___f_80_; lean_object* v___x_81_; 
v_toApplicative_74_ = lean_ctor_get(v_inst_71_, 0);
lean_inc_ref(v_toApplicative_74_);
v_toBind_75_ = lean_ctor_get(v_inst_71_, 1);
lean_inc(v_toBind_75_);
lean_dec_ref(v_inst_71_);
v_toPure_76_ = lean_ctor_get(v_toApplicative_74_, 1);
lean_inc(v_toPure_76_);
lean_dec_ref(v_toApplicative_74_);
v___x_77_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__1, &l_Std_IterM_toHashSet___redArg___closed__1_once, _init_l_Std_IterM_toHashSet___redArg___closed__1);
lean_inc(v_toBind_75_);
v___f_78_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_78_, 0, v_toBind_75_);
lean_inc(v_toPure_76_);
v___f_79_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_79_, 0, v_toPure_76_);
v___f_80_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__2), 8, 5);
lean_closure_set(v___f_80_, 0, v_inst_69_);
lean_closure_set(v___f_80_, 1, v_inst_70_);
lean_closure_set(v___f_80_, 2, v_toPure_76_);
lean_closure_set(v___f_80_, 3, v_toBind_75_);
lean_closure_set(v___f_80_, 4, v___f_79_);
v___x_81_ = lean_apply_6(v_inst_72_, v___f_78_, lean_box(0), lean_box(0), v_it_73_, v___x_77_, v___f_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_m_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_it_91_){
_start:
{
lean_object* v_toApplicative_92_; lean_object* v_toBind_93_; lean_object* v_toPure_94_; lean_object* v___x_95_; lean_object* v___f_96_; lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___x_99_; 
v_toApplicative_92_ = lean_ctor_get(v_inst_87_, 0);
lean_inc_ref(v_toApplicative_92_);
v_toBind_93_ = lean_ctor_get(v_inst_87_, 1);
lean_inc(v_toBind_93_);
lean_dec_ref(v_inst_87_);
v_toPure_94_ = lean_ctor_get(v_toApplicative_92_, 1);
lean_inc(v_toPure_94_);
lean_dec_ref(v_toApplicative_92_);
v___x_95_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__1, &l_Std_IterM_toHashSet___redArg___closed__1_once, _init_l_Std_IterM_toHashSet___redArg___closed__1);
lean_inc(v_toBind_93_);
v___f_96_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_96_, 0, v_toBind_93_);
lean_inc(v_toPure_94_);
v___f_97_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_97_, 0, v_toPure_94_);
v___f_98_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__2), 8, 5);
lean_closure_set(v___f_98_, 0, v_inst_84_);
lean_closure_set(v___f_98_, 1, v_inst_85_);
lean_closure_set(v___f_98_, 2, v_toPure_94_);
lean_closure_set(v___f_98_, 3, v_toBind_93_);
lean_closure_set(v___f_98_, 4, v___f_97_);
v___x_99_ = lean_apply_6(v_inst_90_, v___f_96_, lean_box(0), lean_box(0), v_it_91_, v___x_95_, v___f_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toHashSet___boxed(lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_m_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_it_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_IterM_Total_toHashSet(v_00_u03b1_100_, v_00_u03b2_101_, v_inst_102_, v_inst_103_, v_m_104_, v_inst_105_, v_inst_106_, v_inst_107_, v_inst_108_, v_it_109_);
lean_dec(v_inst_106_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___redArg___lam__1(lean_object* v_toPure_111_, lean_object* v_____do__lift_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_apply_2(v_toPure_111_, lean_box(0), v_____do__lift_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___redArg___lam__0(lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_toPure_116_, lean_object* v_toBind_117_, lean_object* v___f_118_, lean_object* v_x1_119_, lean_object* v_x2_120_, lean_object* v_x3_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_122_ = lean_box(0);
v___x_123_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_114_, v_inst_115_, v_x3_121_, v_x1_119_, v___x_122_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
v___x_125_ = lean_apply_2(v_toPure_116_, lean_box(0), v___x_124_);
v___x_126_ = lean_apply_4(v_toBind_117_, lean_box(0), lean_box(0), v___x_125_, v___f_118_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___redArg(lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_it_131_){
_start:
{
lean_object* v_toApplicative_132_; lean_object* v_toBind_133_; lean_object* v_toPure_134_; lean_object* v___x_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; 
v_toApplicative_132_ = lean_ctor_get(v_inst_129_, 0);
lean_inc_ref(v_toApplicative_132_);
v_toBind_133_ = lean_ctor_get(v_inst_129_, 1);
lean_inc(v_toBind_133_);
lean_dec_ref(v_inst_129_);
v_toPure_134_ = lean_ctor_get(v_toApplicative_132_, 1);
lean_inc(v_toPure_134_);
lean_dec_ref(v_toApplicative_132_);
v___x_135_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__1, &l_Std_IterM_toHashSet___redArg___closed__1_once, _init_l_Std_IterM_toHashSet___redArg___closed__1);
lean_inc(v_toBind_133_);
v___f_136_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_136_, 0, v_toBind_133_);
lean_inc(v_toPure_134_);
v___f_137_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_137_, 0, v_toPure_134_);
v___f_138_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__0), 8, 5);
lean_closure_set(v___f_138_, 0, v_inst_127_);
lean_closure_set(v___f_138_, 1, v_inst_128_);
lean_closure_set(v___f_138_, 2, v_toPure_134_);
lean_closure_set(v___f_138_, 3, v_toBind_133_);
lean_closure_set(v___f_138_, 4, v___f_137_);
v___x_139_ = lean_apply_6(v_inst_130_, v___f_136_, lean_box(0), lean_box(0), v_it_131_, v___x_135_, v___f_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet(lean_object* v_00_u03b1_140_, lean_object* v_00_u03b2_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_m_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_it_150_){
_start:
{
lean_object* v_toApplicative_151_; lean_object* v_toBind_152_; lean_object* v_toPure_153_; lean_object* v___x_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___x_158_; 
v_toApplicative_151_ = lean_ctor_get(v_inst_147_, 0);
lean_inc_ref(v_toApplicative_151_);
v_toBind_152_ = lean_ctor_get(v_inst_147_, 1);
lean_inc(v_toBind_152_);
lean_dec_ref(v_inst_147_);
v_toPure_153_ = lean_ctor_get(v_toApplicative_151_, 1);
lean_inc(v_toPure_153_);
lean_dec_ref(v_toApplicative_151_);
v___x_154_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__1, &l_Std_IterM_toHashSet___redArg___closed__1_once, _init_l_Std_IterM_toHashSet___redArg___closed__1);
lean_inc(v_toBind_152_);
v___f_155_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_155_, 0, v_toBind_152_);
lean_inc(v_toPure_153_);
v___f_156_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_156_, 0, v_toPure_153_);
v___f_157_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__0), 8, 5);
lean_closure_set(v___f_157_, 0, v_inst_142_);
lean_closure_set(v___f_157_, 1, v_inst_143_);
lean_closure_set(v___f_157_, 2, v_toPure_153_);
lean_closure_set(v___f_157_, 3, v_toBind_152_);
lean_closure_set(v___f_157_, 4, v___f_156_);
v___x_158_ = lean_apply_6(v_inst_149_, v___f_155_, lean_box(0), lean_box(0), v_it_150_, v___x_154_, v___f_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtHashSet___boxed(lean_object* v_00_u03b1_159_, lean_object* v_00_u03b2_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_m_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_it_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_IterM_toExtHashSet(v_00_u03b1_159_, v_00_u03b2_160_, v_inst_161_, v_inst_162_, v_inst_163_, v_inst_164_, v_m_165_, v_inst_166_, v_inst_167_, v_inst_168_, v_it_169_);
lean_dec(v_inst_167_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtHashSet___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_it_175_){
_start:
{
lean_object* v_toApplicative_176_; lean_object* v_toBind_177_; lean_object* v_toPure_178_; lean_object* v___x_179_; lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___x_183_; 
v_toApplicative_176_ = lean_ctor_get(v_inst_173_, 0);
lean_inc_ref(v_toApplicative_176_);
v_toBind_177_ = lean_ctor_get(v_inst_173_, 1);
lean_inc(v_toBind_177_);
lean_dec_ref(v_inst_173_);
v_toPure_178_ = lean_ctor_get(v_toApplicative_176_, 1);
lean_inc(v_toPure_178_);
lean_dec_ref(v_toApplicative_176_);
v___x_179_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__1, &l_Std_IterM_toHashSet___redArg___closed__1_once, _init_l_Std_IterM_toHashSet___redArg___closed__1);
lean_inc(v_toBind_177_);
v___f_180_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_180_, 0, v_toBind_177_);
lean_inc(v_toPure_178_);
v___f_181_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_181_, 0, v_toPure_178_);
v___f_182_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__0), 8, 5);
lean_closure_set(v___f_182_, 0, v_inst_171_);
lean_closure_set(v___f_182_, 1, v_inst_172_);
lean_closure_set(v___f_182_, 2, v_toPure_178_);
lean_closure_set(v___f_182_, 3, v_toBind_177_);
lean_closure_set(v___f_182_, 4, v___f_181_);
v___x_183_ = lean_apply_6(v_inst_174_, v___f_180_, lean_box(0), lean_box(0), v_it_175_, v___x_179_, v___f_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtHashSet(lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_m_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_it_195_){
_start:
{
lean_object* v_toApplicative_196_; lean_object* v_toBind_197_; lean_object* v_toPure_198_; lean_object* v___x_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v_toApplicative_196_ = lean_ctor_get(v_inst_191_, 0);
lean_inc_ref(v_toApplicative_196_);
v_toBind_197_ = lean_ctor_get(v_inst_191_, 1);
lean_inc(v_toBind_197_);
lean_dec_ref(v_inst_191_);
v_toPure_198_ = lean_ctor_get(v_toApplicative_196_, 1);
lean_inc(v_toPure_198_);
lean_dec_ref(v_toApplicative_196_);
v___x_199_ = lean_obj_once(&l_Std_IterM_toHashSet___redArg___closed__1, &l_Std_IterM_toHashSet___redArg___closed__1_once, _init_l_Std_IterM_toHashSet___redArg___closed__1);
lean_inc(v_toBind_197_);
v___f_200_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_200_, 0, v_toBind_197_);
lean_inc(v_toPure_198_);
v___f_201_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_201_, 0, v_toPure_198_);
v___f_202_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__0), 8, 5);
lean_closure_set(v___f_202_, 0, v_inst_186_);
lean_closure_set(v___f_202_, 1, v_inst_187_);
lean_closure_set(v___f_202_, 2, v_toPure_198_);
lean_closure_set(v___f_202_, 3, v_toBind_197_);
lean_closure_set(v___f_202_, 4, v___f_201_);
v___x_203_ = lean_apply_6(v_inst_194_, v___f_200_, lean_box(0), lean_box(0), v_it_195_, v___x_199_, v___f_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtHashSet___boxed(lean_object* v_00_u03b1_204_, lean_object* v_00_u03b2_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_m_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_it_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_IterM_Total_toExtHashSet(v_00_u03b1_204_, v_00_u03b2_205_, v_inst_206_, v_inst_207_, v_inst_208_, v_inst_209_, v_m_210_, v_inst_211_, v_inst_212_, v_inst_213_, v_inst_214_, v_it_215_);
lean_dec(v_inst_212_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___redArg___lam__1(lean_object* v_toPure_217_, lean_object* v_____do__lift_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_apply_2(v_toPure_217_, lean_box(0), v_____do__lift_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___redArg___lam__0(lean_object* v_toPure_220_, lean_object* v_toBind_221_, lean_object* v___f_222_, lean_object* v_cmp_223_, lean_object* v_x1_224_, lean_object* v_x2_225_, lean_object* v_x3_226_){
_start:
{
lean_object* v___y_228_; uint8_t v___x_232_; 
lean_inc(v_x3_226_);
lean_inc(v_x1_224_);
lean_inc_ref(v_cmp_223_);
v___x_232_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_223_, v_x1_224_, v_x3_226_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_box(0);
v___x_234_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_223_, v_x1_224_, v___x_233_, v_x3_226_);
v___y_228_ = v___x_234_;
goto v___jp_227_;
}
else
{
lean_dec(v_x1_224_);
lean_dec_ref(v_cmp_223_);
v___y_228_ = v_x3_226_;
goto v___jp_227_;
}
v___jp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v___y_228_);
v___x_230_ = lean_apply_2(v_toPure_220_, lean_box(0), v___x_229_);
v___x_231_ = lean_apply_4(v_toBind_221_, lean_box(0), lean_box(0), v___x_230_, v___f_222_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___redArg(lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_it_237_, lean_object* v_cmp_238_){
_start:
{
lean_object* v_toApplicative_239_; lean_object* v_toBind_240_; lean_object* v_toPure_241_; lean_object* v___x_242_; lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___f_245_; lean_object* v___x_246_; 
v_toApplicative_239_ = lean_ctor_get(v_inst_235_, 0);
lean_inc_ref(v_toApplicative_239_);
v_toBind_240_ = lean_ctor_get(v_inst_235_, 1);
lean_inc(v_toBind_240_);
lean_dec_ref(v_inst_235_);
v_toPure_241_ = lean_ctor_get(v_toApplicative_239_, 1);
lean_inc(v_toPure_241_);
lean_dec_ref(v_toApplicative_239_);
v___x_242_ = lean_box(1);
lean_inc(v_toBind_240_);
v___f_243_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_243_, 0, v_toBind_240_);
lean_inc(v_toPure_241_);
v___f_244_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_244_, 0, v_toPure_241_);
v___f_245_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__0), 7, 4);
lean_closure_set(v___f_245_, 0, v_toPure_241_);
lean_closure_set(v___f_245_, 1, v_toBind_240_);
lean_closure_set(v___f_245_, 2, v___f_244_);
lean_closure_set(v___f_245_, 3, v_cmp_238_);
v___x_246_ = lean_apply_6(v_inst_236_, v___f_243_, lean_box(0), lean_box(0), v_it_237_, v___x_242_, v___f_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_m_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_it_253_, lean_object* v_cmp_254_){
_start:
{
lean_object* v_toApplicative_255_; lean_object* v_toBind_256_; lean_object* v_toPure_257_; lean_object* v___x_258_; lean_object* v___f_259_; lean_object* v___f_260_; lean_object* v___f_261_; lean_object* v___x_262_; 
v_toApplicative_255_ = lean_ctor_get(v_inst_250_, 0);
lean_inc_ref(v_toApplicative_255_);
v_toBind_256_ = lean_ctor_get(v_inst_250_, 1);
lean_inc(v_toBind_256_);
lean_dec_ref(v_inst_250_);
v_toPure_257_ = lean_ctor_get(v_toApplicative_255_, 1);
lean_inc(v_toPure_257_);
lean_dec_ref(v_toApplicative_255_);
v___x_258_ = lean_box(1);
lean_inc(v_toBind_256_);
v___f_259_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_259_, 0, v_toBind_256_);
lean_inc(v_toPure_257_);
v___f_260_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_260_, 0, v_toPure_257_);
v___f_261_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__0), 7, 4);
lean_closure_set(v___f_261_, 0, v_toPure_257_);
lean_closure_set(v___f_261_, 1, v_toBind_256_);
lean_closure_set(v___f_261_, 2, v___f_260_);
lean_closure_set(v___f_261_, 3, v_cmp_254_);
v___x_262_ = lean_apply_6(v_inst_252_, v___f_259_, lean_box(0), lean_box(0), v_it_253_, v___x_258_, v___f_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTreeSet___boxed(lean_object* v_00_u03b1_263_, lean_object* v_00_u03b2_264_, lean_object* v_m_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_it_269_, lean_object* v_cmp_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_IterM_toTreeSet(v_00_u03b1_263_, v_00_u03b2_264_, v_m_265_, v_inst_266_, v_inst_267_, v_inst_268_, v_it_269_, v_cmp_270_);
lean_dec(v_inst_267_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toTreeSet___redArg(lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_it_274_, lean_object* v_cmp_275_){
_start:
{
lean_object* v_toApplicative_276_; lean_object* v_toBind_277_; lean_object* v_toPure_278_; lean_object* v___x_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___f_282_; lean_object* v___x_283_; 
v_toApplicative_276_ = lean_ctor_get(v_inst_272_, 0);
lean_inc_ref(v_toApplicative_276_);
v_toBind_277_ = lean_ctor_get(v_inst_272_, 1);
lean_inc(v_toBind_277_);
lean_dec_ref(v_inst_272_);
v_toPure_278_ = lean_ctor_get(v_toApplicative_276_, 1);
lean_inc(v_toPure_278_);
lean_dec_ref(v_toApplicative_276_);
v___x_279_ = lean_box(1);
lean_inc(v_toBind_277_);
v___f_280_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_280_, 0, v_toBind_277_);
lean_inc(v_toPure_278_);
v___f_281_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_281_, 0, v_toPure_278_);
v___f_282_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__0), 7, 4);
lean_closure_set(v___f_282_, 0, v_toPure_278_);
lean_closure_set(v___f_282_, 1, v_toBind_277_);
lean_closure_set(v___f_282_, 2, v___f_281_);
lean_closure_set(v___f_282_, 3, v_cmp_275_);
v___x_283_ = lean_apply_6(v_inst_273_, v___f_280_, lean_box(0), lean_box(0), v_it_274_, v___x_279_, v___f_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toTreeSet(lean_object* v_00_u03b1_284_, lean_object* v_00_u03b2_285_, lean_object* v_m_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_it_291_, lean_object* v_cmp_292_){
_start:
{
lean_object* v_toApplicative_293_; lean_object* v_toBind_294_; lean_object* v_toPure_295_; lean_object* v___x_296_; lean_object* v___f_297_; lean_object* v___f_298_; lean_object* v___f_299_; lean_object* v___x_300_; 
v_toApplicative_293_ = lean_ctor_get(v_inst_287_, 0);
lean_inc_ref(v_toApplicative_293_);
v_toBind_294_ = lean_ctor_get(v_inst_287_, 1);
lean_inc(v_toBind_294_);
lean_dec_ref(v_inst_287_);
v_toPure_295_ = lean_ctor_get(v_toApplicative_293_, 1);
lean_inc(v_toPure_295_);
lean_dec_ref(v_toApplicative_293_);
v___x_296_ = lean_box(1);
lean_inc(v_toBind_294_);
v___f_297_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_297_, 0, v_toBind_294_);
lean_inc(v_toPure_295_);
v___f_298_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_298_, 0, v_toPure_295_);
v___f_299_ = lean_alloc_closure((void*)(l_Std_IterM_toTreeSet___redArg___lam__0), 7, 4);
lean_closure_set(v___f_299_, 0, v_toPure_295_);
lean_closure_set(v___f_299_, 1, v_toBind_294_);
lean_closure_set(v___f_299_, 2, v___f_298_);
lean_closure_set(v___f_299_, 3, v_cmp_292_);
v___x_300_ = lean_apply_6(v_inst_290_, v___f_297_, lean_box(0), lean_box(0), v_it_291_, v___x_296_, v___f_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toTreeSet___boxed(lean_object* v_00_u03b1_301_, lean_object* v_00_u03b2_302_, lean_object* v_m_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_it_308_, lean_object* v_cmp_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_IterM_Total_toTreeSet(v_00_u03b1_301_, v_00_u03b2_302_, v_m_303_, v_inst_304_, v_inst_305_, v_inst_306_, v_inst_307_, v_it_308_, v_cmp_309_);
lean_dec(v_inst_305_);
return v_res_310_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__12(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__10));
v___x_338_ = l_Lean_mkAtom(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__13(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__12, &l_Std_IterM_toExtTreeSet___auto__1___closed__12_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__12);
v___x_340_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__5));
v___x_341_ = lean_array_push(v___x_340_, v___x_339_);
return v___x_341_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__15(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__14));
v___x_344_ = lean_string_utf8_byte_size(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__16(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_345_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__15, &l_Std_IterM_toExtTreeSet___auto__1___closed__15_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__15);
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__14));
v___x_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_346_);
lean_ctor_set(v___x_348_, 2, v___x_345_);
return v___x_348_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__18(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_351_ = lean_box(0);
v___x_352_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__17));
v___x_353_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__16, &l_Std_IterM_toExtTreeSet___auto__1___closed__16_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__16);
v___x_354_ = lean_box(2);
v___x_355_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_353_);
lean_ctor_set(v___x_355_, 2, v___x_352_);
lean_ctor_set(v___x_355_, 3, v___x_351_);
return v___x_355_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__19(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__18, &l_Std_IterM_toExtTreeSet___auto__1___closed__18_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__18);
v___x_357_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__13, &l_Std_IterM_toExtTreeSet___auto__1___closed__13_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__13);
v___x_358_ = lean_array_push(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__20(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__19, &l_Std_IterM_toExtTreeSet___auto__1___closed__19_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__19);
v___x_360_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__11));
v___x_361_ = lean_box(2);
v___x_362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v___x_360_);
lean_ctor_set(v___x_362_, 2, v___x_359_);
return v___x_362_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__21(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__20, &l_Std_IterM_toExtTreeSet___auto__1___closed__20_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__20);
v___x_364_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__5));
v___x_365_ = lean_array_push(v___x_364_, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__22(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_366_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__21, &l_Std_IterM_toExtTreeSet___auto__1___closed__21_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__21);
v___x_367_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__9));
v___x_368_ = lean_box(2);
v___x_369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
lean_ctor_set(v___x_369_, 2, v___x_366_);
return v___x_369_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__23(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__22, &l_Std_IterM_toExtTreeSet___auto__1___closed__22_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__22);
v___x_371_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__5));
v___x_372_ = lean_array_push(v___x_371_, v___x_370_);
return v___x_372_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__24(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__23, &l_Std_IterM_toExtTreeSet___auto__1___closed__23_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__23);
v___x_374_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__7));
v___x_375_ = lean_box(2);
v___x_376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
lean_ctor_set(v___x_376_, 2, v___x_373_);
return v___x_376_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__25(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__24, &l_Std_IterM_toExtTreeSet___auto__1___closed__24_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__24);
v___x_378_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__5));
v___x_379_ = lean_array_push(v___x_378_, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1___closed__26(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_380_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__25, &l_Std_IterM_toExtTreeSet___auto__1___closed__25_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__25);
v___x_381_ = ((lean_object*)(l_Std_IterM_toExtTreeSet___auto__1___closed__4));
v___x_382_ = lean_box(2);
v___x_383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___x_380_);
return v___x_383_;
}
}
static lean_object* _init_l_Std_IterM_toExtTreeSet___auto__1(void){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__26, &l_Std_IterM_toExtTreeSet___auto__1___closed__26_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__26);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet___redArg___lam__2(lean_object* v_toPure_385_, lean_object* v_toBind_386_, lean_object* v___f_387_, lean_object* v_cmp_388_, lean_object* v_x1_389_, lean_object* v_x2_390_, lean_object* v_x3_391_){
_start:
{
lean_object* v___y_393_; uint8_t v___x_397_; 
lean_inc(v_x3_391_);
lean_inc(v_x1_389_);
lean_inc_ref(v_cmp_388_);
v___x_397_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_388_, v_x1_389_, v_x3_391_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_box(0);
v___x_399_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_388_, v_x1_389_, v___x_398_, v_x3_391_);
v___y_393_ = v___x_399_;
goto v___jp_392_;
}
else
{
lean_dec(v_x1_389_);
lean_dec_ref(v_cmp_388_);
v___y_393_ = v_x3_391_;
goto v___jp_392_;
}
v___jp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v___y_393_);
v___x_395_ = lean_apply_2(v_toPure_385_, lean_box(0), v___x_394_);
v___x_396_ = lean_apply_4(v_toBind_386_, lean_box(0), lean_box(0), v___x_395_, v___f_387_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet___redArg(lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_it_402_, lean_object* v_cmp_403_){
_start:
{
lean_object* v_toApplicative_404_; lean_object* v_toBind_405_; lean_object* v_toPure_406_; lean_object* v___x_407_; lean_object* v___f_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___x_411_; 
v_toApplicative_404_ = lean_ctor_get(v_inst_400_, 0);
lean_inc_ref(v_toApplicative_404_);
v_toBind_405_ = lean_ctor_get(v_inst_400_, 1);
lean_inc(v_toBind_405_);
lean_dec_ref(v_inst_400_);
v_toPure_406_ = lean_ctor_get(v_toApplicative_404_, 1);
lean_inc(v_toPure_406_);
lean_dec_ref(v_toApplicative_404_);
v___x_407_ = lean_box(1);
lean_inc(v_toBind_405_);
v___f_408_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_408_, 0, v_toBind_405_);
lean_inc(v_toPure_406_);
v___f_409_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_409_, 0, v_toPure_406_);
v___f_410_ = lean_alloc_closure((void*)(l_Std_IterM_toExtTreeSet___redArg___lam__2), 7, 4);
lean_closure_set(v___f_410_, 0, v_toPure_406_);
lean_closure_set(v___f_410_, 1, v_toBind_405_);
lean_closure_set(v___f_410_, 2, v___f_409_);
lean_closure_set(v___f_410_, 3, v_cmp_403_);
v___x_411_ = lean_apply_6(v_inst_401_, v___f_408_, lean_box(0), lean_box(0), v_it_402_, v___x_407_, v___f_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_m_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_it_418_, lean_object* v_cmp_419_, lean_object* v_inst_420_){
_start:
{
lean_object* v_toApplicative_421_; lean_object* v_toBind_422_; lean_object* v_toPure_423_; lean_object* v___x_424_; lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___x_428_; 
v_toApplicative_421_ = lean_ctor_get(v_inst_415_, 0);
lean_inc_ref(v_toApplicative_421_);
v_toBind_422_ = lean_ctor_get(v_inst_415_, 1);
lean_inc(v_toBind_422_);
lean_dec_ref(v_inst_415_);
v_toPure_423_ = lean_ctor_get(v_toApplicative_421_, 1);
lean_inc(v_toPure_423_);
lean_dec_ref(v_toApplicative_421_);
v___x_424_ = lean_box(1);
lean_inc(v_toBind_422_);
v___f_425_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_425_, 0, v_toBind_422_);
lean_inc(v_toPure_423_);
v___f_426_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_426_, 0, v_toPure_423_);
v___f_427_ = lean_alloc_closure((void*)(l_Std_IterM_toExtTreeSet___redArg___lam__2), 7, 4);
lean_closure_set(v___f_427_, 0, v_toPure_423_);
lean_closure_set(v___f_427_, 1, v_toBind_422_);
lean_closure_set(v___f_427_, 2, v___f_426_);
lean_closure_set(v___f_427_, 3, v_cmp_419_);
v___x_428_ = lean_apply_6(v_inst_417_, v___f_425_, lean_box(0), lean_box(0), v_it_418_, v___x_424_, v___f_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toExtTreeSet___boxed(lean_object* v_00_u03b1_429_, lean_object* v_00_u03b2_430_, lean_object* v_m_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_it_435_, lean_object* v_cmp_436_, lean_object* v_inst_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_IterM_toExtTreeSet(v_00_u03b1_429_, v_00_u03b2_430_, v_m_431_, v_inst_432_, v_inst_433_, v_inst_434_, v_it_435_, v_cmp_436_, v_inst_437_);
lean_dec(v_inst_433_);
return v_res_438_;
}
}
static lean_object* _init_l_Std_IterM_Total_toExtTreeSet___auto__1(void){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_obj_once(&l_Std_IterM_toExtTreeSet___auto__1___closed__26, &l_Std_IterM_toExtTreeSet___auto__1___closed__26_once, _init_l_Std_IterM_toExtTreeSet___auto__1___closed__26);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtTreeSet___redArg(lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_it_442_, lean_object* v_cmp_443_){
_start:
{
lean_object* v_toApplicative_444_; lean_object* v_toBind_445_; lean_object* v_toPure_446_; lean_object* v___x_447_; lean_object* v___f_448_; lean_object* v___f_449_; lean_object* v___f_450_; lean_object* v___x_451_; 
v_toApplicative_444_ = lean_ctor_get(v_inst_440_, 0);
lean_inc_ref(v_toApplicative_444_);
v_toBind_445_ = lean_ctor_get(v_inst_440_, 1);
lean_inc(v_toBind_445_);
lean_dec_ref(v_inst_440_);
v_toPure_446_ = lean_ctor_get(v_toApplicative_444_, 1);
lean_inc(v_toPure_446_);
lean_dec_ref(v_toApplicative_444_);
v___x_447_ = lean_box(1);
lean_inc(v_toBind_445_);
v___f_448_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_448_, 0, v_toBind_445_);
lean_inc(v_toPure_446_);
v___f_449_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_449_, 0, v_toPure_446_);
v___f_450_ = lean_alloc_closure((void*)(l_Std_IterM_toExtTreeSet___redArg___lam__2), 7, 4);
lean_closure_set(v___f_450_, 0, v_toPure_446_);
lean_closure_set(v___f_450_, 1, v_toBind_445_);
lean_closure_set(v___f_450_, 2, v___f_449_);
lean_closure_set(v___f_450_, 3, v_cmp_443_);
v___x_451_ = lean_apply_6(v_inst_441_, v___f_448_, lean_box(0), lean_box(0), v_it_442_, v___x_447_, v___f_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtTreeSet(lean_object* v_00_u03b1_452_, lean_object* v_00_u03b2_453_, lean_object* v_m_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_it_459_, lean_object* v_cmp_460_, lean_object* v_inst_461_){
_start:
{
lean_object* v_toApplicative_462_; lean_object* v_toBind_463_; lean_object* v_toPure_464_; lean_object* v___x_465_; lean_object* v___f_466_; lean_object* v___f_467_; lean_object* v___f_468_; lean_object* v___x_469_; 
v_toApplicative_462_ = lean_ctor_get(v_inst_455_, 0);
lean_inc_ref(v_toApplicative_462_);
v_toBind_463_ = lean_ctor_get(v_inst_455_, 1);
lean_inc(v_toBind_463_);
lean_dec_ref(v_inst_455_);
v_toPure_464_ = lean_ctor_get(v_toApplicative_462_, 1);
lean_inc(v_toPure_464_);
lean_dec_ref(v_toApplicative_462_);
v___x_465_ = lean_box(1);
lean_inc(v_toBind_463_);
v___f_466_ = lean_alloc_closure((void*)(l_Std_IterM_toHashSet___redArg___lam__0), 5, 1);
lean_closure_set(v___f_466_, 0, v_toBind_463_);
lean_inc(v_toPure_464_);
v___f_467_ = lean_alloc_closure((void*)(l_Std_IterM_toExtHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_467_, 0, v_toPure_464_);
v___f_468_ = lean_alloc_closure((void*)(l_Std_IterM_toExtTreeSet___redArg___lam__2), 7, 4);
lean_closure_set(v___f_468_, 0, v_toPure_464_);
lean_closure_set(v___f_468_, 1, v_toBind_463_);
lean_closure_set(v___f_468_, 2, v___f_467_);
lean_closure_set(v___f_468_, 3, v_cmp_460_);
v___x_469_ = lean_apply_6(v_inst_458_, v___f_466_, lean_box(0), lean_box(0), v_it_459_, v___x_465_, v___f_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_toExtTreeSet___boxed(lean_object* v_00_u03b1_470_, lean_object* v_00_u03b2_471_, lean_object* v_m_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_it_477_, lean_object* v_cmp_478_, lean_object* v_inst_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_IterM_Total_toExtTreeSet(v_00_u03b1_470_, v_00_u03b2_471_, v_m_472_, v_inst_473_, v_inst_474_, v_inst_475_, v_inst_476_, v_it_477_, v_cmp_478_, v_inst_479_);
lean_dec(v_inst_474_);
return v_res_480_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_ExtHashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_ExtTreeSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Consumers_Monadic_Set(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
