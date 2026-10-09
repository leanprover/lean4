// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.Slice
// Imports: public import Std.Data.DTreeMap.Internal.Zipper public import Std.Data.DTreeMap.Raw.Basic
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
static const lean_string_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__3 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value;
static const lean_array_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__6 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value;
static const lean_string_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__8 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__9 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__9_value;
static const lean_string_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__10 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__10_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value;
static lean_once_cell_t l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12;
static lean_once_cell_t l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13;
static const lean_string_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__14 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__14_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__15 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__15_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__16 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__16_value;
static const lean_ctor_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__15_value),((lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__17 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__17_value;
static lean_once_cell_t l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18;
static lean_once_cell_t l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19;
static lean_once_cell_t l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20;
static lean_once_cell_t l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21;
static lean_once_cell_t l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22;
static lean_once_cell_t l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23;
static lean_once_cell_t l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24;
static lean_once_cell_t l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList__rii___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList__ric___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList__rio___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList__rci___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList__rco___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList__rcc___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList__roi___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList__roc___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList__roo___auto__1;
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__17));
v___x_45_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13);
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18);
v___x_48_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19);
v___x_52_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20);
v___x_55_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__9));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21);
v___x_59_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22);
v___x_62_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23);
v___x_66_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24);
v___x_69_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg___lam__0(lean_object* v_carrier_73_, lean_object* v_range_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v_carrier_73_);
lean_ctor_set(v___x_75_, 1, v_range_74_);
return v___x_75_;
}
}
lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg(){
_start:
{
lean_object* v___f_78_; 
v___f_78_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg___closed__0));
return v___f_78_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_79_;
v_res_79_ = l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg();
stack->m_obj
 = v_res_79_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg___boxed(lean_object* v___dummy_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg();
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_cmp_84_){
_start:
{
lean_object* v___f_85_; 
v___f_85_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRiiSlice___redArg___closed__0));
return v___f_85_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRiiSlice___boxed(lean_object* v_00_u03b1_86_, lean_object* v_00_u03b2_87_, lean_object* v_cmp_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_DTreeMap_Raw_instSliceableRiiSlice(v_00_u03b1_86_, v_00_u03b2_87_, v_cmp_88_);
lean_dec_ref(v_cmp_88_);
return v_res_89_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_toList__rii___auto__1(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_90_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRicSlice___auto__1(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg___lam__0(lean_object* v_carrier_92_, lean_object* v_range_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_carrier_92_);
lean_ctor_set(v___x_94_, 1, v_range_93_);
return v___x_94_;
}
}
lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg(){
_start:
{
lean_object* v___f_97_; 
v___f_97_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg___closed__0));
return v___f_97_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_98_;
v_res_98_ = l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg();
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg___boxed(lean_object* v___dummy_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_cmp_103_){
_start:
{
lean_object* v___f_104_; 
v___f_104_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRicSlice___redArg___closed__0));
return v___f_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRicSlice___boxed(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_cmp_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_DTreeMap_Raw_instSliceableRicSlice(v_00_u03b1_105_, v_00_u03b2_106_, v_cmp_107_);
lean_dec_ref(v_cmp_107_);
return v_res_108_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_toList__ric___auto__1(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_109_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRioSlice___auto__1(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg___lam__0(lean_object* v_carrier_111_, lean_object* v_range_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_carrier_111_);
lean_ctor_set(v___x_113_, 1, v_range_112_);
return v___x_113_;
}
}
lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg(){
_start:
{
lean_object* v___f_116_; 
v___f_116_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg___closed__0));
return v___f_116_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_117_;
v_res_117_ = l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg();
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg___boxed(lean_object* v___dummy_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg();
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice(lean_object* v_00_u03b1_120_, lean_object* v_00_u03b2_121_, lean_object* v_cmp_122_){
_start:
{
lean_object* v___f_123_; 
v___f_123_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRioSlice___redArg___closed__0));
return v___f_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRioSlice___boxed(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_cmp_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_DTreeMap_Raw_instSliceableRioSlice(v_00_u03b1_124_, v_00_u03b2_125_, v_cmp_126_);
lean_dec_ref(v_cmp_126_);
return v_res_127_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_toList__rio___auto__1(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_128_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRciSlice___auto__1(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg___lam__0(lean_object* v_carrier_130_, lean_object* v_range_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_carrier_130_);
lean_ctor_set(v___x_132_, 1, v_range_131_);
return v___x_132_;
}
}
lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg(){
_start:
{
lean_object* v___f_135_; 
v___f_135_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg___closed__0));
return v___f_135_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_136_;
v_res_136_ = l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg();
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg___boxed(lean_object* v___dummy_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg();
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice(lean_object* v_00_u03b1_139_, lean_object* v_00_u03b2_140_, lean_object* v_cmp_141_){
_start:
{
lean_object* v___f_142_; 
v___f_142_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRciSlice___redArg___closed__0));
return v___f_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRciSlice___boxed(lean_object* v_00_u03b1_143_, lean_object* v_00_u03b2_144_, lean_object* v_cmp_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_DTreeMap_Raw_instSliceableRciSlice(v_00_u03b1_143_, v_00_u03b2_144_, v_cmp_145_);
lean_dec_ref(v_cmp_145_);
return v_res_146_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_toList__rci___auto__1(void){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_147_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRcoSlice___auto__1(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg___lam__0(lean_object* v_carrier_149_, lean_object* v_range_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v_carrier_149_);
lean_ctor_set(v___x_151_, 1, v_range_150_);
return v___x_151_;
}
}
lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg(){
_start:
{
lean_object* v___f_154_; 
v___f_154_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg___closed__0));
return v___f_154_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_155_;
v_res_155_ = l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg();
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg___boxed(lean_object* v___dummy_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg();
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice(lean_object* v_00_u03b1_158_, lean_object* v_00_u03b2_159_, lean_object* v_cmp_160_){
_start:
{
lean_object* v___f_161_; 
v___f_161_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRcoSlice___redArg___closed__0));
return v___f_161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRcoSlice___boxed(lean_object* v_00_u03b1_162_, lean_object* v_00_u03b2_163_, lean_object* v_cmp_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Std_DTreeMap_Raw_instSliceableRcoSlice(v_00_u03b1_162_, v_00_u03b2_163_, v_cmp_164_);
lean_dec_ref(v_cmp_164_);
return v_res_165_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_toList__rco___auto__1(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_166_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRccSlice___auto__1(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg___lam__0(lean_object* v_carrier_168_, lean_object* v_range_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v_carrier_168_);
lean_ctor_set(v___x_170_, 1, v_range_169_);
return v___x_170_;
}
}
lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg(){
_start:
{
lean_object* v___f_173_; 
v___f_173_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg___closed__0));
return v___f_173_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_174_;
v_res_174_ = l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg();
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg___boxed(lean_object* v___dummy_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg();
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice(lean_object* v_00_u03b1_177_, lean_object* v_00_u03b2_178_, lean_object* v_cmp_179_){
_start:
{
lean_object* v___f_180_; 
v___f_180_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRccSlice___redArg___closed__0));
return v___f_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRccSlice___boxed(lean_object* v_00_u03b1_181_, lean_object* v_00_u03b2_182_, lean_object* v_cmp_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_DTreeMap_Raw_instSliceableRccSlice(v_00_u03b1_181_, v_00_u03b2_182_, v_cmp_183_);
lean_dec_ref(v_cmp_183_);
return v_res_184_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_toList__rcc___auto__1(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_185_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRoiSlice___auto__1(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg___lam__0(lean_object* v_carrier_187_, lean_object* v_range_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_carrier_187_);
lean_ctor_set(v___x_189_, 1, v_range_188_);
return v___x_189_;
}
}
lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg(){
_start:
{
lean_object* v___f_192_; 
v___f_192_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg___closed__0));
return v___f_192_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_193_;
v_res_193_ = l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg();
stack->m_obj
 = v_res_193_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg___boxed(lean_object* v___dummy_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg();
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_cmp_198_){
_start:
{
lean_object* v___f_199_; 
v___f_199_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRoiSlice___redArg___closed__0));
return v___f_199_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRoiSlice___boxed(lean_object* v_00_u03b1_200_, lean_object* v_00_u03b2_201_, lean_object* v_cmp_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_DTreeMap_Raw_instSliceableRoiSlice(v_00_u03b1_200_, v_00_u03b2_201_, v_cmp_202_);
lean_dec_ref(v_cmp_202_);
return v_res_203_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_toList__roi___auto__1(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_204_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRocSlice___auto__1(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg___lam__0(lean_object* v_carrier_206_, lean_object* v_range_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v_carrier_206_);
lean_ctor_set(v___x_208_, 1, v_range_207_);
return v___x_208_;
}
}
lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg(){
_start:
{
lean_object* v___f_211_; 
v___f_211_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg___closed__0));
return v___f_211_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_212_;
v_res_212_ = l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg();
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg___boxed(lean_object* v___dummy_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg();
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, lean_object* v_cmp_217_){
_start:
{
lean_object* v___f_218_; 
v___f_218_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRocSlice___redArg___closed__0));
return v___f_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRocSlice___boxed(lean_object* v_00_u03b1_219_, lean_object* v_00_u03b2_220_, lean_object* v_cmp_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_DTreeMap_Raw_instSliceableRocSlice(v_00_u03b1_219_, v_00_u03b2_220_, v_cmp_221_);
lean_dec_ref(v_cmp_221_);
return v_res_222_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_toList__roc___auto__1(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_223_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_instSliceableRooSlice___auto__1(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg___lam__0(lean_object* v_carrier_225_, lean_object* v_range_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v_carrier_225_);
lean_ctor_set(v___x_227_, 1, v_range_226_);
return v___x_227_;
}
}
lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg(){
_start:
{
lean_object* v___f_230_; 
v___f_230_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg___closed__0));
return v___f_230_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_231_;
v_res_231_ = l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg();
stack->m_obj
 = v_res_231_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg___boxed(lean_object* v___dummy_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg();
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_cmp_236_){
_start:
{
lean_object* v___f_237_; 
v___f_237_ = ((lean_object*)(l_Std_DTreeMap_Raw_instSliceableRooSlice___redArg___closed__0));
return v___f_237_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSliceableRooSlice___boxed(lean_object* v_00_u03b1_238_, lean_object* v_00_u03b2_239_, lean_object* v_cmp_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_DTreeMap_Raw_instSliceableRooSlice(v_00_u03b1_238_, v_00_u03b2_239_, v_cmp_240_);
lean_dec_ref(v_cmp_240_);
return v_res_241_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_toList__roo___auto__1(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_obj_once(&l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
return v___x_242_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Zipper(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Slice(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Raw_Slice(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1 = _init_l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_instSliceableRiiSlice___auto__1);
l_Std_DTreeMap_Raw_toList__rii___auto__1 = _init_l_Std_DTreeMap_Raw_toList__rii___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_toList__rii___auto__1);
l_Std_DTreeMap_Raw_instSliceableRicSlice___auto__1 = _init_l_Std_DTreeMap_Raw_instSliceableRicSlice___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_instSliceableRicSlice___auto__1);
l_Std_DTreeMap_Raw_toList__ric___auto__1 = _init_l_Std_DTreeMap_Raw_toList__ric___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_toList__ric___auto__1);
l_Std_DTreeMap_Raw_instSliceableRioSlice___auto__1 = _init_l_Std_DTreeMap_Raw_instSliceableRioSlice___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_instSliceableRioSlice___auto__1);
l_Std_DTreeMap_Raw_toList__rio___auto__1 = _init_l_Std_DTreeMap_Raw_toList__rio___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_toList__rio___auto__1);
l_Std_DTreeMap_Raw_instSliceableRciSlice___auto__1 = _init_l_Std_DTreeMap_Raw_instSliceableRciSlice___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_instSliceableRciSlice___auto__1);
l_Std_DTreeMap_Raw_toList__rci___auto__1 = _init_l_Std_DTreeMap_Raw_toList__rci___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_toList__rci___auto__1);
l_Std_DTreeMap_Raw_instSliceableRcoSlice___auto__1 = _init_l_Std_DTreeMap_Raw_instSliceableRcoSlice___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_instSliceableRcoSlice___auto__1);
l_Std_DTreeMap_Raw_toList__rco___auto__1 = _init_l_Std_DTreeMap_Raw_toList__rco___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_toList__rco___auto__1);
l_Std_DTreeMap_Raw_instSliceableRccSlice___auto__1 = _init_l_Std_DTreeMap_Raw_instSliceableRccSlice___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_instSliceableRccSlice___auto__1);
l_Std_DTreeMap_Raw_toList__rcc___auto__1 = _init_l_Std_DTreeMap_Raw_toList__rcc___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_toList__rcc___auto__1);
l_Std_DTreeMap_Raw_instSliceableRoiSlice___auto__1 = _init_l_Std_DTreeMap_Raw_instSliceableRoiSlice___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_instSliceableRoiSlice___auto__1);
l_Std_DTreeMap_Raw_toList__roi___auto__1 = _init_l_Std_DTreeMap_Raw_toList__roi___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_toList__roi___auto__1);
l_Std_DTreeMap_Raw_instSliceableRocSlice___auto__1 = _init_l_Std_DTreeMap_Raw_instSliceableRocSlice___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_instSliceableRocSlice___auto__1);
l_Std_DTreeMap_Raw_toList__roc___auto__1 = _init_l_Std_DTreeMap_Raw_toList__roc___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_toList__roc___auto__1);
l_Std_DTreeMap_Raw_instSliceableRooSlice___auto__1 = _init_l_Std_DTreeMap_Raw_instSliceableRooSlice___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_instSliceableRooSlice___auto__1);
l_Std_DTreeMap_Raw_toList__roo___auto__1 = _init_l_Std_DTreeMap_Raw_toList__roo___auto__1();
lean_mark_persistent(l_Std_DTreeMap_Raw_toList__roo___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Internal_Zipper(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Raw_Slice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Raw_Slice(builtin);
}
#ifdef __cplusplus
}
#endif
