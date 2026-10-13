// Lean compiler output
// Module: Std.Data.TreeSet.Raw.Slice
// Imports: public import Std.Data.TreeMap.Raw.Slice public import Std.Data.TreeSet.Raw.Basic
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__0_value;
static const lean_string_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__1 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__1_value;
static const lean_string_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__2 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__2_value;
static const lean_string_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__3 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__3_value;
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__4 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__4_value;
static const lean_array_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__5 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__5_value;
static const lean_string_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__6 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__6_value;
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__7 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__7_value;
static const lean_string_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__8 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__8_value;
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__9 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__9_value;
static const lean_string_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__10 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__10_value;
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__11 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__11_value;
static lean_once_cell_t l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__12;
static lean_once_cell_t l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__13;
static const lean_string_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__14 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__14_value;
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__15 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__15_value;
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__16 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__16_value;
static const lean_ctor_object l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__15_value),((lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__17 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__17_value;
static lean_once_cell_t l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__18;
static lean_once_cell_t l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__19;
static lean_once_cell_t l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__20;
static lean_once_cell_t l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__21;
static lean_once_cell_t l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__22;
static lean_once_cell_t l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__23;
static lean_once_cell_t l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__24;
static lean_once_cell_t l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList__rii___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_instSliceableRicSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_Raw_instSliceableRicSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRicSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList__ric___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_instSliceableRioSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_Raw_instSliceableRioSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRioSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList__rio___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_instSliceableRciSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_Raw_instSliceableRciSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRciSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList__rci___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList__rco___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_instSliceableRccSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_Raw_instSliceableRccSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRccSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList__rcc___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList__roi___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_instSliceableRocSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_Raw_instSliceableRocSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRocSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList__roc___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeSet_Raw_instSliceableRooSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_Raw_instSliceableRooSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeSet_Raw_instSliceableRooSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_toList__roo___auto__1;
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__12, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__12_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__17));
v___x_45_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__13, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__13_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__13);
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__18, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__18_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__18);
v___x_48_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__11));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__19, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__19_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__19);
v___x_52_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__20, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__20_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__20);
v___x_55_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__9));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__22(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__21, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__21_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__21);
v___x_59_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__23(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__22, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__22_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__22);
v___x_62_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__7));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__24(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__23, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__23_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__23);
v___x_66_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__24, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__24_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__24);
v___x_69_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__4));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg___lam__0(lean_object* v_carrier_73_, lean_object* v_range_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v_carrier_73_);
lean_ctor_set(v___x_75_, 1, v_range_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg(){
_start:
{
lean_object* v___f_78_; 
v___f_78_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg___closed__0));
return v___f_78_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg___boxed(lean_object* v___dummy_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg();
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice(lean_object* v_00_u03b1_81_, lean_object* v_cmp_82_){
_start:
{
lean_object* v___f_83_; 
v___f_83_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRiiSlice___redArg___closed__0));
return v___f_83_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRiiSlice___boxed(lean_object* v_00_u03b1_84_, lean_object* v_cmp_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_TreeSet_Raw_instSliceableRiiSlice(v_00_u03b1_84_, v_cmp_85_);
lean_dec_ref(v_cmp_85_);
return v_res_86_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_toList__rii___auto__1(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_87_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRicSlice___auto__1(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice___redArg___lam__0(lean_object* v_carrier_89_, lean_object* v_range_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_carrier_89_);
lean_ctor_set(v___x_91_, 1, v_range_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice___redArg(){
_start:
{
lean_object* v___f_94_; 
v___f_94_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRicSlice___redArg___closed__0));
return v___f_94_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice___redArg___boxed(lean_object* v___dummy_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_TreeSet_Raw_instSliceableRicSlice___redArg();
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice(lean_object* v_00_u03b1_97_, lean_object* v_cmp_98_){
_start:
{
lean_object* v___f_99_; 
v___f_99_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRicSlice___redArg___closed__0));
return v___f_99_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRicSlice___boxed(lean_object* v_00_u03b1_100_, lean_object* v_cmp_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_TreeSet_Raw_instSliceableRicSlice(v_00_u03b1_100_, v_cmp_101_);
lean_dec_ref(v_cmp_101_);
return v_res_102_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_toList__ric___auto__1(void){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_103_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRioSlice___auto__1(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice___redArg___lam__0(lean_object* v_carrier_105_, lean_object* v_range_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v_carrier_105_);
lean_ctor_set(v___x_107_, 1, v_range_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice___redArg(){
_start:
{
lean_object* v___f_110_; 
v___f_110_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRioSlice___redArg___closed__0));
return v___f_110_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice___redArg___boxed(lean_object* v___dummy_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_TreeSet_Raw_instSliceableRioSlice___redArg();
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice(lean_object* v_00_u03b1_113_, lean_object* v_cmp_114_){
_start:
{
lean_object* v___f_115_; 
v___f_115_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRioSlice___redArg___closed__0));
return v___f_115_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRioSlice___boxed(lean_object* v_00_u03b1_116_, lean_object* v_cmp_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_TreeSet_Raw_instSliceableRioSlice(v_00_u03b1_116_, v_cmp_117_);
lean_dec_ref(v_cmp_117_);
return v_res_118_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_toList__rio___auto__1(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_119_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRciSlice___auto__1(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice___redArg___lam__0(lean_object* v_carrier_121_, lean_object* v_range_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v_carrier_121_);
lean_ctor_set(v___x_123_, 1, v_range_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice___redArg(){
_start:
{
lean_object* v___f_126_; 
v___f_126_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRciSlice___redArg___closed__0));
return v___f_126_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice___redArg___boxed(lean_object* v___dummy_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_TreeSet_Raw_instSliceableRciSlice___redArg();
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice(lean_object* v_00_u03b1_129_, lean_object* v_cmp_130_){
_start:
{
lean_object* v___f_131_; 
v___f_131_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRciSlice___redArg___closed__0));
return v___f_131_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRciSlice___boxed(lean_object* v_00_u03b1_132_, lean_object* v_cmp_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_TreeSet_Raw_instSliceableRciSlice(v_00_u03b1_132_, v_cmp_133_);
lean_dec_ref(v_cmp_133_);
return v_res_134_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_toList__rci___auto__1(void){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_135_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRcoSlice___auto__1(void){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg___lam__0(lean_object* v_carrier_137_, lean_object* v_range_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v_carrier_137_);
lean_ctor_set(v___x_139_, 1, v_range_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg(){
_start:
{
lean_object* v___f_142_; 
v___f_142_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg___closed__0));
return v___f_142_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg___boxed(lean_object* v___dummy_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg();
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice(lean_object* v_00_u03b1_145_, lean_object* v_cmp_146_){
_start:
{
lean_object* v___f_147_; 
v___f_147_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRcoSlice___redArg___closed__0));
return v___f_147_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRcoSlice___boxed(lean_object* v_00_u03b1_148_, lean_object* v_cmp_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_TreeSet_Raw_instSliceableRcoSlice(v_00_u03b1_148_, v_cmp_149_);
lean_dec_ref(v_cmp_149_);
return v_res_150_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_toList__rco___auto__1(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_151_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRccSlice___auto__1(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice___redArg___lam__0(lean_object* v_carrier_153_, lean_object* v_range_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_carrier_153_);
lean_ctor_set(v___x_155_, 1, v_range_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice___redArg(){
_start:
{
lean_object* v___f_158_; 
v___f_158_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRccSlice___redArg___closed__0));
return v___f_158_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice___redArg___boxed(lean_object* v___dummy_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_TreeSet_Raw_instSliceableRccSlice___redArg();
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice(lean_object* v_00_u03b1_161_, lean_object* v_cmp_162_){
_start:
{
lean_object* v___f_163_; 
v___f_163_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRccSlice___redArg___closed__0));
return v___f_163_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRccSlice___boxed(lean_object* v_00_u03b1_164_, lean_object* v_cmp_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_TreeSet_Raw_instSliceableRccSlice(v_00_u03b1_164_, v_cmp_165_);
lean_dec_ref(v_cmp_165_);
return v_res_166_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_toList__rcc___auto__1(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_167_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRoiSlice___auto__1(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg___lam__0(lean_object* v_carrier_169_, lean_object* v_range_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_carrier_169_);
lean_ctor_set(v___x_171_, 1, v_range_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg(){
_start:
{
lean_object* v___f_174_; 
v___f_174_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg___closed__0));
return v___f_174_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg___boxed(lean_object* v___dummy_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg();
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice(lean_object* v_00_u03b1_177_, lean_object* v_cmp_178_){
_start:
{
lean_object* v___f_179_; 
v___f_179_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRoiSlice___redArg___closed__0));
return v___f_179_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRoiSlice___boxed(lean_object* v_00_u03b1_180_, lean_object* v_cmp_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_TreeSet_Raw_instSliceableRoiSlice(v_00_u03b1_180_, v_cmp_181_);
lean_dec_ref(v_cmp_181_);
return v_res_182_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_toList__roi___auto__1(void){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_183_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRocSlice___auto__1(void){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice___redArg___lam__0(lean_object* v_carrier_185_, lean_object* v_range_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v_carrier_185_);
lean_ctor_set(v___x_187_, 1, v_range_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice___redArg(){
_start:
{
lean_object* v___f_190_; 
v___f_190_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRocSlice___redArg___closed__0));
return v___f_190_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice___redArg___boxed(lean_object* v___dummy_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_TreeSet_Raw_instSliceableRocSlice___redArg();
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice(lean_object* v_00_u03b1_193_, lean_object* v_cmp_194_){
_start:
{
lean_object* v___f_195_; 
v___f_195_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRocSlice___redArg___closed__0));
return v___f_195_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRocSlice___boxed(lean_object* v_00_u03b1_196_, lean_object* v_cmp_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_TreeSet_Raw_instSliceableRocSlice(v_00_u03b1_196_, v_cmp_197_);
lean_dec_ref(v_cmp_197_);
return v_res_198_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_toList__roc___auto__1(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_199_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instSliceableRooSlice___auto__1(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice___redArg___lam__0(lean_object* v_carrier_201_, lean_object* v_range_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_carrier_201_);
lean_ctor_set(v___x_203_, 1, v_range_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice___redArg(){
_start:
{
lean_object* v___f_206_; 
v___f_206_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRooSlice___redArg___closed__0));
return v___f_206_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice___redArg___boxed(lean_object* v___dummy_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_TreeSet_Raw_instSliceableRooSlice___redArg();
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice(lean_object* v_00_u03b1_209_, lean_object* v_cmp_210_){
_start:
{
lean_object* v___f_211_; 
v___f_211_ = ((lean_object*)(l_Std_TreeSet_Raw_instSliceableRooSlice___redArg___closed__0));
return v___f_211_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instSliceableRooSlice___boxed(lean_object* v_00_u03b1_212_, lean_object* v_cmp_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_TreeSet_Raw_instSliceableRooSlice(v_00_u03b1_212_, v_cmp_213_);
lean_dec_ref(v_cmp_213_);
return v_res_214_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_toList__roo___auto__1(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_215_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Slice(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeSet_Raw_Slice(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_TreeMap_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeSet_Raw_Slice(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1 = _init_l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_instSliceableRiiSlice___auto__1);
l_Std_TreeSet_Raw_toList__rii___auto__1 = _init_l_Std_TreeSet_Raw_toList__rii___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_toList__rii___auto__1);
l_Std_TreeSet_Raw_instSliceableRicSlice___auto__1 = _init_l_Std_TreeSet_Raw_instSliceableRicSlice___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_instSliceableRicSlice___auto__1);
l_Std_TreeSet_Raw_toList__ric___auto__1 = _init_l_Std_TreeSet_Raw_toList__ric___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_toList__ric___auto__1);
l_Std_TreeSet_Raw_instSliceableRioSlice___auto__1 = _init_l_Std_TreeSet_Raw_instSliceableRioSlice___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_instSliceableRioSlice___auto__1);
l_Std_TreeSet_Raw_toList__rio___auto__1 = _init_l_Std_TreeSet_Raw_toList__rio___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_toList__rio___auto__1);
l_Std_TreeSet_Raw_instSliceableRciSlice___auto__1 = _init_l_Std_TreeSet_Raw_instSliceableRciSlice___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_instSliceableRciSlice___auto__1);
l_Std_TreeSet_Raw_toList__rci___auto__1 = _init_l_Std_TreeSet_Raw_toList__rci___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_toList__rci___auto__1);
l_Std_TreeSet_Raw_instSliceableRcoSlice___auto__1 = _init_l_Std_TreeSet_Raw_instSliceableRcoSlice___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_instSliceableRcoSlice___auto__1);
l_Std_TreeSet_Raw_toList__rco___auto__1 = _init_l_Std_TreeSet_Raw_toList__rco___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_toList__rco___auto__1);
l_Std_TreeSet_Raw_instSliceableRccSlice___auto__1 = _init_l_Std_TreeSet_Raw_instSliceableRccSlice___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_instSliceableRccSlice___auto__1);
l_Std_TreeSet_Raw_toList__rcc___auto__1 = _init_l_Std_TreeSet_Raw_toList__rcc___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_toList__rcc___auto__1);
l_Std_TreeSet_Raw_instSliceableRoiSlice___auto__1 = _init_l_Std_TreeSet_Raw_instSliceableRoiSlice___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_instSliceableRoiSlice___auto__1);
l_Std_TreeSet_Raw_toList__roi___auto__1 = _init_l_Std_TreeSet_Raw_toList__roi___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_toList__roi___auto__1);
l_Std_TreeSet_Raw_instSliceableRocSlice___auto__1 = _init_l_Std_TreeSet_Raw_instSliceableRocSlice___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_instSliceableRocSlice___auto__1);
l_Std_TreeSet_Raw_toList__roc___auto__1 = _init_l_Std_TreeSet_Raw_toList__roc___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_toList__roc___auto__1);
l_Std_TreeSet_Raw_instSliceableRooSlice___auto__1 = _init_l_Std_TreeSet_Raw_instSliceableRooSlice___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_instSliceableRooSlice___auto__1);
l_Std_TreeSet_Raw_toList__roo___auto__1 = _init_l_Std_TreeSet_Raw_toList__roo___auto__1();
lean_mark_persistent(l_Std_TreeSet_Raw_toList__roo___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_TreeMap_Raw_Slice(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeSet_Raw_Slice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeSet_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeSet_Raw_Slice(builtin);
}
#ifdef __cplusplus
}
#endif
