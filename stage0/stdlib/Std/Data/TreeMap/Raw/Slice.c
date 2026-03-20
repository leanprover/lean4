// Lean compiler output
// Module: Std.Data.TreeMap.Raw.Slice
// Imports: public import Std.Data.DTreeMap.Raw.Slice public import Std.Data.TreeMap.Raw.Basic
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0_value;
static const lean_string_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1_value;
static const lean_string_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2_value;
static const lean_string_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__3 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__3_value;
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4_value;
static const lean_array_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5_value;
static const lean_string_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__6 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__6_value;
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7_value;
static const lean_string_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__8 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__8_value;
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__9 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__9_value;
static const lean_string_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__10 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__10_value;
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11_value;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13;
static const lean_string_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__14 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__14_value;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__15;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__16;
static const lean_ctor_object l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__17 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__17_value;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25;
static lean_once_cell_t l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_instSliceableRiiSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_instSliceableRiiSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRiiSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList__rii___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRicSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRicSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_instSliceableRicSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_instSliceableRicSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_instSliceableRicSlice___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRicSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRicSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRicSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList__ric___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRioSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRioSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_instSliceableRioSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_instSliceableRioSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_instSliceableRioSlice___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRioSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRioSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRioSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList__rio___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRciSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRciSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_instSliceableRciSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_instSliceableRciSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_instSliceableRciSlice___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRciSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRciSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRciSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList__rci___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRcoSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRcoSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_instSliceableRcoSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_instSliceableRcoSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_instSliceableRcoSlice___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRcoSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRcoSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRcoSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList__rco___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRccSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRccSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_instSliceableRccSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_instSliceableRccSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_instSliceableRccSlice___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRccSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRccSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRccSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList__rcc___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRoiSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRoiSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_instSliceableRoiSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_instSliceableRoiSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_instSliceableRoiSlice___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRoiSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRoiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRoiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList__roi___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRocSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRocSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_instSliceableRocSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_instSliceableRocSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_instSliceableRocSlice___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRocSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRocSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRocSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList__roc___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRooSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRooSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_Raw_instSliceableRooSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_Raw_instSliceableRooSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_Raw_instSliceableRooSlice___closed__0 = (const lean_object*)&l_Std_TreeMap_Raw_instSliceableRooSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRooSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRooSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_toList__roo___auto__1;
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__14));
v___x_34_ = lean_string_utf8_byte_size(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__16(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__15, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__15_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__15);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__14));
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_box(0);
v___x_42_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__17));
v___x_43_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__16, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__16_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__16);
v___x_44_ = lean_box(2);
v___x_45_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
lean_ctor_set(v___x_45_, 2, v___x_42_);
lean_ctor_set(v___x_45_, 3, v___x_41_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__18);
v___x_47_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__13);
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__19);
v___x_50_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__11));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__20);
v___x_54_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__21);
v___x_57_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__9));
v___x_58_ = lean_box(2);
v___x_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__22);
v___x_61_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__23);
v___x_64_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__7));
v___x_65_ = lean_box(2);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__24);
v___x_68_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__5));
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__25);
v___x_71_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__4));
v___x_72_ = lean_box(2);
v___x_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___lam__0(lean_object* v_carrier_75_, lean_object* v_range_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v_carrier_75_);
lean_ctor_set(v___x_77_, 1, v_range_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_cmp_81_){
_start:
{
lean_object* v___f_82_; 
v___f_82_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRiiSlice___closed__0));
return v___f_82_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRiiSlice___boxed(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_cmp_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_TreeMap_Raw_instSliceableRiiSlice(v_00_u03b1_83_, v_00_u03b2_84_, v_cmp_85_);
lean_dec_ref(v_cmp_85_);
return v_res_86_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_toList__rii___auto__1(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_87_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRicSlice___auto__1(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRicSlice___lam__0(lean_object* v_carrier_89_, lean_object* v_range_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_carrier_89_);
lean_ctor_set(v___x_91_, 1, v_range_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRicSlice(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_cmp_95_){
_start:
{
lean_object* v___f_96_; 
v___f_96_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRicSlice___closed__0));
return v___f_96_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRicSlice___boxed(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_cmp_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_TreeMap_Raw_instSliceableRicSlice(v_00_u03b1_97_, v_00_u03b2_98_, v_cmp_99_);
lean_dec_ref(v_cmp_99_);
return v_res_100_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_toList__ric___auto__1(void){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_101_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRioSlice___auto__1(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRioSlice___lam__0(lean_object* v_carrier_103_, lean_object* v_range_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v_carrier_103_);
lean_ctor_set(v___x_105_, 1, v_range_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRioSlice(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_cmp_109_){
_start:
{
lean_object* v___f_110_; 
v___f_110_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRioSlice___closed__0));
return v___f_110_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRioSlice___boxed(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_cmp_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_TreeMap_Raw_instSliceableRioSlice(v_00_u03b1_111_, v_00_u03b2_112_, v_cmp_113_);
lean_dec_ref(v_cmp_113_);
return v_res_114_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_toList__rio___auto__1(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_115_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRciSlice___auto__1(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRciSlice___lam__0(lean_object* v_carrier_117_, lean_object* v_range_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_carrier_117_);
lean_ctor_set(v___x_119_, 1, v_range_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRciSlice(lean_object* v_00_u03b1_121_, lean_object* v_00_u03b2_122_, lean_object* v_cmp_123_){
_start:
{
lean_object* v___f_124_; 
v___f_124_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRciSlice___closed__0));
return v___f_124_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRciSlice___boxed(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_cmp_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_TreeMap_Raw_instSliceableRciSlice(v_00_u03b1_125_, v_00_u03b2_126_, v_cmp_127_);
lean_dec_ref(v_cmp_127_);
return v_res_128_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_toList__rci___auto__1(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_129_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRcoSlice___auto__1(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRcoSlice___lam__0(lean_object* v_carrier_131_, lean_object* v_range_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_carrier_131_);
lean_ctor_set(v___x_133_, 1, v_range_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRcoSlice(lean_object* v_00_u03b1_135_, lean_object* v_00_u03b2_136_, lean_object* v_cmp_137_){
_start:
{
lean_object* v___f_138_; 
v___f_138_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRcoSlice___closed__0));
return v___f_138_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRcoSlice___boxed(lean_object* v_00_u03b1_139_, lean_object* v_00_u03b2_140_, lean_object* v_cmp_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_TreeMap_Raw_instSliceableRcoSlice(v_00_u03b1_139_, v_00_u03b2_140_, v_cmp_141_);
lean_dec_ref(v_cmp_141_);
return v_res_142_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_toList__rco___auto__1(void){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_143_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRccSlice___auto__1(void){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRccSlice___lam__0(lean_object* v_carrier_145_, lean_object* v_range_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v_carrier_145_);
lean_ctor_set(v___x_147_, 1, v_range_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRccSlice(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_cmp_151_){
_start:
{
lean_object* v___f_152_; 
v___f_152_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRccSlice___closed__0));
return v___f_152_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRccSlice___boxed(lean_object* v_00_u03b1_153_, lean_object* v_00_u03b2_154_, lean_object* v_cmp_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_TreeMap_Raw_instSliceableRccSlice(v_00_u03b1_153_, v_00_u03b2_154_, v_cmp_155_);
lean_dec_ref(v_cmp_155_);
return v_res_156_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_toList__rcc___auto__1(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_157_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRoiSlice___auto__1(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRoiSlice___lam__0(lean_object* v_carrier_159_, lean_object* v_range_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_carrier_159_);
lean_ctor_set(v___x_161_, 1, v_range_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRoiSlice(lean_object* v_00_u03b1_163_, lean_object* v_00_u03b2_164_, lean_object* v_cmp_165_){
_start:
{
lean_object* v___f_166_; 
v___f_166_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRoiSlice___closed__0));
return v___f_166_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRoiSlice___boxed(lean_object* v_00_u03b1_167_, lean_object* v_00_u03b2_168_, lean_object* v_cmp_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_TreeMap_Raw_instSliceableRoiSlice(v_00_u03b1_167_, v_00_u03b2_168_, v_cmp_169_);
lean_dec_ref(v_cmp_169_);
return v_res_170_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_toList__roi___auto__1(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_171_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRocSlice___auto__1(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRocSlice___lam__0(lean_object* v_carrier_173_, lean_object* v_range_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_carrier_173_);
lean_ctor_set(v___x_175_, 1, v_range_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRocSlice(lean_object* v_00_u03b1_177_, lean_object* v_00_u03b2_178_, lean_object* v_cmp_179_){
_start:
{
lean_object* v___f_180_; 
v___f_180_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRocSlice___closed__0));
return v___f_180_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRocSlice___boxed(lean_object* v_00_u03b1_181_, lean_object* v_00_u03b2_182_, lean_object* v_cmp_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_TreeMap_Raw_instSliceableRocSlice(v_00_u03b1_181_, v_00_u03b2_182_, v_cmp_183_);
lean_dec_ref(v_cmp_183_);
return v_res_184_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_toList__roc___auto__1(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_185_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_instSliceableRooSlice___auto__1(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRooSlice___lam__0(lean_object* v_carrier_187_, lean_object* v_range_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_carrier_187_);
lean_ctor_set(v___x_189_, 1, v_range_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRooSlice(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_cmp_193_){
_start:
{
lean_object* v___f_194_; 
v___f_194_ = ((lean_object*)(l_Std_TreeMap_Raw_instSliceableRooSlice___closed__0));
return v___f_194_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_instSliceableRooSlice___boxed(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_cmp_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_TreeMap_Raw_instSliceableRooSlice(v_00_u03b1_195_, v_00_u03b2_196_, v_cmp_197_);
lean_dec_ref(v_cmp_197_);
return v_res_198_;
}
}
static lean_object* _init_l_Std_TreeMap_Raw_toList__roo___auto__1(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1___closed__26);
return v___x_199_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Slice(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Slice(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeMap_Raw_Slice(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1 = _init_l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_instSliceableRiiSlice___auto__1);
l_Std_TreeMap_Raw_toList__rii___auto__1 = _init_l_Std_TreeMap_Raw_toList__rii___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_toList__rii___auto__1);
l_Std_TreeMap_Raw_instSliceableRicSlice___auto__1 = _init_l_Std_TreeMap_Raw_instSliceableRicSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_instSliceableRicSlice___auto__1);
l_Std_TreeMap_Raw_toList__ric___auto__1 = _init_l_Std_TreeMap_Raw_toList__ric___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_toList__ric___auto__1);
l_Std_TreeMap_Raw_instSliceableRioSlice___auto__1 = _init_l_Std_TreeMap_Raw_instSliceableRioSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_instSliceableRioSlice___auto__1);
l_Std_TreeMap_Raw_toList__rio___auto__1 = _init_l_Std_TreeMap_Raw_toList__rio___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_toList__rio___auto__1);
l_Std_TreeMap_Raw_instSliceableRciSlice___auto__1 = _init_l_Std_TreeMap_Raw_instSliceableRciSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_instSliceableRciSlice___auto__1);
l_Std_TreeMap_Raw_toList__rci___auto__1 = _init_l_Std_TreeMap_Raw_toList__rci___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_toList__rci___auto__1);
l_Std_TreeMap_Raw_instSliceableRcoSlice___auto__1 = _init_l_Std_TreeMap_Raw_instSliceableRcoSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_instSliceableRcoSlice___auto__1);
l_Std_TreeMap_Raw_toList__rco___auto__1 = _init_l_Std_TreeMap_Raw_toList__rco___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_toList__rco___auto__1);
l_Std_TreeMap_Raw_instSliceableRccSlice___auto__1 = _init_l_Std_TreeMap_Raw_instSliceableRccSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_instSliceableRccSlice___auto__1);
l_Std_TreeMap_Raw_toList__rcc___auto__1 = _init_l_Std_TreeMap_Raw_toList__rcc___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_toList__rcc___auto__1);
l_Std_TreeMap_Raw_instSliceableRoiSlice___auto__1 = _init_l_Std_TreeMap_Raw_instSliceableRoiSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_instSliceableRoiSlice___auto__1);
l_Std_TreeMap_Raw_toList__roi___auto__1 = _init_l_Std_TreeMap_Raw_toList__roi___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_toList__roi___auto__1);
l_Std_TreeMap_Raw_instSliceableRocSlice___auto__1 = _init_l_Std_TreeMap_Raw_instSliceableRocSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_instSliceableRocSlice___auto__1);
l_Std_TreeMap_Raw_toList__roc___auto__1 = _init_l_Std_TreeMap_Raw_toList__roc___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_toList__roc___auto__1);
l_Std_TreeMap_Raw_instSliceableRooSlice___auto__1 = _init_l_Std_TreeMap_Raw_instSliceableRooSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_instSliceableRooSlice___auto__1);
l_Std_TreeMap_Raw_toList__roo___auto__1 = _init_l_Std_TreeMap_Raw_toList__roo___auto__1();
lean_mark_persistent(l_Std_TreeMap_Raw_toList__roo___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Raw_Slice(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeMap_Raw_Slice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeMap_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeMap_Raw_Slice(builtin);
}
#ifdef __cplusplus
}
#endif
