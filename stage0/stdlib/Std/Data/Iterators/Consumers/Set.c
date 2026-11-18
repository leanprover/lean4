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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Iter_toHashSet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iter_toHashSet___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iter_toHashSet___redArg___closed__0 = (const lean_object*)&l_Std_Iter_toHashSet___redArg___closed__0_value;
static lean_once_cell_t l_Std_Iter_toHashSet___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toHashSet___redArg___closed__1;
static lean_once_cell_t l_Std_Iter_toHashSet___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Iter_toHashSet___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__15 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__15_value;
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_Iter_toTreeSet___auto__1___closed__16 = (const lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__16_value;
static const lean_ctor_object l_Std_Iter_toTreeSet___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__15_value),((lean_object*)&l_Std_Iter_toTreeSet___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___redArg___lam__1(lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_x1_8_, lean_object* v_x2_9_, lean_object* v_x3_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_box(0);
v___x_12_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_6_, v_inst_7_, v_x3_10_, v_x1_8_, v___x_11_);
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
static lean_object* _init_l_Std_Iter_toHashSet___redArg___closed__1(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_box(0);
v___x_16_ = lean_unsigned_to_nat(16u);
v___x_17_ = lean_mk_array(v___x_16_, v___x_15_);
return v___x_17_;
}
}
static lean_object* _init_l_Std_Iter_toHashSet___redArg___closed__2(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__1, &l_Std_Iter_toHashSet___redArg___closed__1_once, _init_l_Std_Iter_toHashSet___redArg___closed__1);
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___redArg(lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_it_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___f_25_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_26_ = lean_alloc_closure((void*)(l_Std_Iter_toHashSet___redArg___lam__1), 5, 2);
lean_closure_set(v___f_26_, 0, v_inst_21_);
lean_closure_set(v___f_26_, 1, v_inst_22_);
v___x_27_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__2, &l_Std_Iter_toHashSet___redArg___closed__2_once, _init_l_Std_Iter_toHashSet___redArg___closed__2);
v___x_28_ = lean_apply_6(v_inst_23_, v___f_25_, lean_box(0), lean_box(0), v_it_24_, v___x_27_, v___f_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_it_35_){
_start:
{
lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___f_36_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_37_ = lean_alloc_closure((void*)(l_Std_Iter_toHashSet___redArg___lam__1), 5, 2);
lean_closure_set(v___f_37_, 0, v_inst_31_);
lean_closure_set(v___f_37_, 1, v_inst_32_);
v___x_38_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__2, &l_Std_Iter_toHashSet___redArg___closed__2_once, _init_l_Std_Iter_toHashSet___redArg___closed__2);
v___x_39_ = lean_apply_6(v_inst_34_, v___f_36_, lean_box(0), lean_box(0), v_it_35_, v___x_38_, v___f_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toHashSet___boxed(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_it_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Std_Iter_toHashSet(v_00_u03b1_40_, v_00_u03b2_41_, v_inst_42_, v_inst_43_, v_inst_44_, v_inst_45_, v_it_46_);
lean_dec(v_inst_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet___redArg(lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_it_51_){
_start:
{
lean_object* v___f_52_; lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___f_52_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_53_ = lean_alloc_closure((void*)(l_Std_Iter_toHashSet___redArg___lam__1), 5, 2);
lean_closure_set(v___f_53_, 0, v_inst_48_);
lean_closure_set(v___f_53_, 1, v_inst_49_);
v___x_54_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__2, &l_Std_Iter_toHashSet___redArg___closed__2_once, _init_l_Std_Iter_toHashSet___redArg___closed__2);
v___x_55_ = lean_apply_6(v_inst_50_, v___f_52_, lean_box(0), lean_box(0), v_it_51_, v___x_54_, v___f_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet(lean_object* v_00_u03b1_56_, lean_object* v_00_u03b2_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_it_63_){
_start:
{
lean_object* v___f_64_; lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___f_64_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_65_ = lean_alloc_closure((void*)(l_Std_Iter_toHashSet___redArg___lam__1), 5, 2);
lean_closure_set(v___f_65_, 0, v_inst_58_);
lean_closure_set(v___f_65_, 1, v_inst_59_);
v___x_66_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__2, &l_Std_Iter_toHashSet___redArg___closed__2_once, _init_l_Std_Iter_toHashSet___redArg___closed__2);
v___x_67_ = lean_apply_6(v_inst_62_, v___f_64_, lean_box(0), lean_box(0), v_it_63_, v___x_66_, v___f_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toHashSet___boxed(lean_object* v_00_u03b1_68_, lean_object* v_00_u03b2_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_it_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_Iter_Total_toHashSet(v_00_u03b1_68_, v_00_u03b2_69_, v_inst_70_, v_inst_71_, v_inst_72_, v_inst_73_, v_inst_74_, v_it_75_);
lean_dec(v_inst_72_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet___redArg___lam__1(lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_x1_79_, lean_object* v_x2_80_, lean_object* v_x3_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_box(0);
v___x_83_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_77_, v_inst_78_, v_x3_81_, v_x1_79_, v___x_82_);
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet___redArg(lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_it_88_){
_start:
{
lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___f_89_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_90_ = lean_alloc_closure((void*)(l_Std_Iter_toExtHashSet___redArg___lam__1), 5, 2);
lean_closure_set(v___f_90_, 0, v_inst_85_);
lean_closure_set(v___f_90_, 1, v_inst_86_);
v___x_91_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__2, &l_Std_Iter_toHashSet___redArg___closed__2_once, _init_l_Std_Iter_toHashSet___redArg___closed__2);
v___x_92_ = lean_apply_6(v_inst_87_, v___f_89_, lean_box(0), lean_box(0), v_it_88_, v___x_91_, v___f_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_it_101_){
_start:
{
lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___f_102_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_103_ = lean_alloc_closure((void*)(l_Std_Iter_toExtHashSet___redArg___lam__1), 5, 2);
lean_closure_set(v___f_103_, 0, v_inst_95_);
lean_closure_set(v___f_103_, 1, v_inst_96_);
v___x_104_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__2, &l_Std_Iter_toHashSet___redArg___closed__2_once, _init_l_Std_Iter_toHashSet___redArg___closed__2);
v___x_105_ = lean_apply_6(v_inst_100_, v___f_102_, lean_box(0), lean_box(0), v_it_101_, v___x_104_, v___f_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtHashSet___boxed(lean_object* v_00_u03b1_106_, lean_object* v_00_u03b2_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_it_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Iter_toExtHashSet(v_00_u03b1_106_, v_00_u03b2_107_, v_inst_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_inst_113_, v_it_114_);
lean_dec(v_inst_112_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtHashSet___redArg(lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_it_119_){
_start:
{
lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___f_120_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_121_ = lean_alloc_closure((void*)(l_Std_Iter_toExtHashSet___redArg___lam__1), 5, 2);
lean_closure_set(v___f_121_, 0, v_inst_116_);
lean_closure_set(v___f_121_, 1, v_inst_117_);
v___x_122_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__2, &l_Std_Iter_toHashSet___redArg___closed__2_once, _init_l_Std_Iter_toHashSet___redArg___closed__2);
v___x_123_ = lean_apply_6(v_inst_118_, v___f_120_, lean_box(0), lean_box(0), v_it_119_, v___x_122_, v___f_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtHashSet(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_it_133_){
_start:
{
lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___f_134_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_135_ = lean_alloc_closure((void*)(l_Std_Iter_toExtHashSet___redArg___lam__1), 5, 2);
lean_closure_set(v___f_135_, 0, v_inst_126_);
lean_closure_set(v___f_135_, 1, v_inst_127_);
v___x_136_ = lean_obj_once(&l_Std_Iter_toHashSet___redArg___closed__2, &l_Std_Iter_toHashSet___redArg___closed__2_once, _init_l_Std_Iter_toHashSet___redArg___closed__2);
v___x_137_ = lean_apply_6(v_inst_132_, v___f_134_, lean_box(0), lean_box(0), v_it_133_, v___x_136_, v___f_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtHashSet___boxed(lean_object* v_00_u03b1_138_, lean_object* v_00_u03b2_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_it_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_Iter_Total_toExtHashSet(v_00_u03b1_138_, v_00_u03b2_139_, v_inst_140_, v_inst_141_, v_inst_142_, v_inst_143_, v_inst_144_, v_inst_145_, v_inst_146_, v_it_147_);
lean_dec(v_inst_144_);
return v_res_148_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__12(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__10));
v___x_176_ = l_Lean_mkAtom(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__13(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__12, &l_Std_Iter_toTreeSet___auto__1___closed__12_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__12);
v___x_178_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__5));
v___x_179_ = lean_array_push(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__18(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__17));
v___x_193_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__13, &l_Std_Iter_toTreeSet___auto__1___closed__13_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__13);
v___x_194_ = lean_array_push(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__19(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_195_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__18, &l_Std_Iter_toTreeSet___auto__1___closed__18_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__18);
v___x_196_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__11));
v___x_197_ = lean_box(2);
v___x_198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_196_);
lean_ctor_set(v___x_198_, 2, v___x_195_);
return v___x_198_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__20(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__19, &l_Std_Iter_toTreeSet___auto__1___closed__19_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__19);
v___x_200_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__5));
v___x_201_ = lean_array_push(v___x_200_, v___x_199_);
return v___x_201_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__21(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_202_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__20, &l_Std_Iter_toTreeSet___auto__1___closed__20_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__20);
v___x_203_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__9));
v___x_204_ = lean_box(2);
v___x_205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
lean_ctor_set(v___x_205_, 2, v___x_202_);
return v___x_205_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__22(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__21, &l_Std_Iter_toTreeSet___auto__1___closed__21_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__21);
v___x_207_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__5));
v___x_208_ = lean_array_push(v___x_207_, v___x_206_);
return v___x_208_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__23(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_209_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__22, &l_Std_Iter_toTreeSet___auto__1___closed__22_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__22);
v___x_210_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__7));
v___x_211_ = lean_box(2);
v___x_212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
lean_ctor_set(v___x_212_, 2, v___x_209_);
return v___x_212_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__24(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__23, &l_Std_Iter_toTreeSet___auto__1___closed__23_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__23);
v___x_214_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__5));
v___x_215_ = lean_array_push(v___x_214_, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1___closed__25(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_216_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__24, &l_Std_Iter_toTreeSet___auto__1___closed__24_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__24);
v___x_217_ = ((lean_object*)(l_Std_Iter_toTreeSet___auto__1___closed__4));
v___x_218_ = lean_box(2);
v___x_219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
lean_ctor_set(v___x_219_, 2, v___x_216_);
return v___x_219_;
}
}
static lean_object* _init_l_Std_Iter_toTreeSet___auto__1(void){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__25, &l_Std_Iter_toTreeSet___auto__1___closed__25_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__25);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet___redArg___lam__1(lean_object* v_cmp_221_, lean_object* v_x1_222_, lean_object* v_x2_223_, lean_object* v_x3_224_){
_start:
{
uint8_t v___x_225_; 
lean_inc(v_x3_224_);
lean_inc(v_x1_222_);
lean_inc_ref(v_cmp_221_);
v___x_225_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_221_, v_x1_222_, v_x3_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_box(0);
v___x_227_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_221_, v_x1_222_, v___x_226_, v_x3_224_);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; 
lean_dec(v_x1_222_);
lean_dec_ref(v_cmp_221_);
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v_x3_224_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet___redArg(lean_object* v_inst_230_, lean_object* v_it_231_, lean_object* v_cmp_232_){
_start:
{
lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___f_233_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_234_ = lean_alloc_closure((void*)(l_Std_Iter_toTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_234_, 0, v_cmp_232_);
v___x_235_ = lean_box(1);
v___x_236_ = lean_apply_6(v_inst_230_, v___f_233_, lean_box(0), lean_box(0), v_it_231_, v___x_235_, v___f_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet(lean_object* v_00_u03b1_237_, lean_object* v_00_u03b2_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_it_241_, lean_object* v_cmp_242_){
_start:
{
lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___f_243_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_244_ = lean_alloc_closure((void*)(l_Std_Iter_toTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_244_, 0, v_cmp_242_);
v___x_245_ = lean_box(1);
v___x_246_ = lean_apply_6(v_inst_240_, v___f_243_, lean_box(0), lean_box(0), v_it_241_, v___x_245_, v___f_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toTreeSet___boxed(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_it_251_, lean_object* v_cmp_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_Iter_toTreeSet(v_00_u03b1_247_, v_00_u03b2_248_, v_inst_249_, v_inst_250_, v_it_251_, v_cmp_252_);
lean_dec(v_inst_249_);
return v_res_253_;
}
}
static lean_object* _init_l_Std_Iter_Total_toTreeSet___auto__1(void){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__25, &l_Std_Iter_toTreeSet___auto__1___closed__25_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__25);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toTreeSet___redArg(lean_object* v_inst_255_, lean_object* v_it_256_, lean_object* v_cmp_257_){
_start:
{
lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___f_258_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_259_ = lean_alloc_closure((void*)(l_Std_Iter_toTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_259_, 0, v_cmp_257_);
v___x_260_ = lean_box(1);
v___x_261_ = lean_apply_6(v_inst_255_, v___f_258_, lean_box(0), lean_box(0), v_it_256_, v___x_260_, v___f_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toTreeSet(lean_object* v_00_u03b1_262_, lean_object* v_00_u03b2_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_it_267_, lean_object* v_cmp_268_){
_start:
{
lean_object* v___f_269_; lean_object* v___f_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___f_269_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_270_ = lean_alloc_closure((void*)(l_Std_Iter_toTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_270_, 0, v_cmp_268_);
v___x_271_ = lean_box(1);
v___x_272_ = lean_apply_6(v_inst_266_, v___f_269_, lean_box(0), lean_box(0), v_it_267_, v___x_271_, v___f_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toTreeSet___boxed(lean_object* v_00_u03b1_273_, lean_object* v_00_u03b2_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_it_278_, lean_object* v_cmp_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_Iter_Total_toTreeSet(v_00_u03b1_273_, v_00_u03b2_274_, v_inst_275_, v_inst_276_, v_inst_277_, v_it_278_, v_cmp_279_);
lean_dec(v_inst_275_);
return v_res_280_;
}
}
static lean_object* _init_l_Std_Iter_toExtTreeSet___auto__1(void){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__25, &l_Std_Iter_toTreeSet___auto__1___closed__25_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__25);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet___redArg___lam__1(lean_object* v_cmp_282_, lean_object* v_x1_283_, lean_object* v_x2_284_, lean_object* v_x3_285_){
_start:
{
uint8_t v___x_286_; 
lean_inc(v_x3_285_);
lean_inc(v_x1_283_);
lean_inc_ref(v_cmp_282_);
v___x_286_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_282_, v_x1_283_, v_x3_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_box(0);
v___x_288_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_282_, v_x1_283_, v___x_287_, v_x3_285_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
else
{
lean_object* v___x_290_; 
lean_dec(v_x1_283_);
lean_dec_ref(v_cmp_282_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v_x3_285_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet___redArg(lean_object* v_inst_291_, lean_object* v_it_292_, lean_object* v_cmp_293_){
_start:
{
lean_object* v___f_294_; lean_object* v___f_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___f_294_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_295_ = lean_alloc_closure((void*)(l_Std_Iter_toExtTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_295_, 0, v_cmp_293_);
v___x_296_ = lean_box(1);
v___x_297_ = lean_apply_6(v_inst_291_, v___f_294_, lean_box(0), lean_box(0), v_it_292_, v___x_296_, v___f_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet(lean_object* v_00_u03b1_298_, lean_object* v_00_u03b2_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_it_302_, lean_object* v_cmp_303_, lean_object* v_inst_304_){
_start:
{
lean_object* v___f_305_; lean_object* v___f_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___f_305_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_306_ = lean_alloc_closure((void*)(l_Std_Iter_toExtTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_306_, 0, v_cmp_303_);
v___x_307_ = lean_box(1);
v___x_308_ = lean_apply_6(v_inst_301_, v___f_305_, lean_box(0), lean_box(0), v_it_302_, v___x_307_, v___f_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toExtTreeSet___boxed(lean_object* v_00_u03b1_309_, lean_object* v_00_u03b2_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_it_313_, lean_object* v_cmp_314_, lean_object* v_inst_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_Iter_toExtTreeSet(v_00_u03b1_309_, v_00_u03b2_310_, v_inst_311_, v_inst_312_, v_it_313_, v_cmp_314_, v_inst_315_);
lean_dec(v_inst_311_);
return v_res_316_;
}
}
static lean_object* _init_l_Std_Iter_Total_toExtTreeSet___auto__1(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Std_Iter_toTreeSet___auto__1___closed__25, &l_Std_Iter_toTreeSet___auto__1___closed__25_once, _init_l_Std_Iter_toTreeSet___auto__1___closed__25);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtTreeSet___redArg(lean_object* v_inst_318_, lean_object* v_it_319_, lean_object* v_cmp_320_){
_start:
{
lean_object* v___f_321_; lean_object* v___f_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___f_321_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_322_ = lean_alloc_closure((void*)(l_Std_Iter_toExtTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_322_, 0, v_cmp_320_);
v___x_323_ = lean_box(1);
v___x_324_ = lean_apply_6(v_inst_318_, v___f_321_, lean_box(0), lean_box(0), v_it_319_, v___x_323_, v___f_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtTreeSet(lean_object* v_00_u03b1_325_, lean_object* v_00_u03b2_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_it_330_, lean_object* v_cmp_331_, lean_object* v_inst_332_){
_start:
{
lean_object* v___f_333_; lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___f_333_ = ((lean_object*)(l_Std_Iter_toHashSet___redArg___closed__0));
v___f_334_ = lean_alloc_closure((void*)(l_Std_Iter_toExtTreeSet___redArg___lam__1), 4, 1);
lean_closure_set(v___f_334_, 0, v_cmp_331_);
v___x_335_ = lean_box(1);
v___x_336_ = lean_apply_6(v_inst_329_, v___f_333_, lean_box(0), lean_box(0), v_it_330_, v___x_335_, v___f_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toExtTreeSet___boxed(lean_object* v_00_u03b1_337_, lean_object* v_00_u03b2_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_it_342_, lean_object* v_cmp_343_, lean_object* v_inst_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Iter_Total_toExtTreeSet(v_00_u03b1_337_, v_00_u03b2_338_, v_inst_339_, v_inst_340_, v_inst_341_, v_it_342_, v_cmp_343_, v_inst_344_);
lean_dec(v_inst_339_);
return v_res_345_;
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
