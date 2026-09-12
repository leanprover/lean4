// Lean compiler output
// Module: Std.Data.TreeMap.Slice
// Imports: public import Std.Data.TreeMap.Raw.Slice public import Std.Data.TreeMap.Basic
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0_value;
static const lean_string_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1_value;
static const lean_string_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2_value;
static const lean_string_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__3 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__3_value;
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value;
static const lean_array_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5_value;
static const lean_string_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__6 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__6_value;
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value;
static const lean_string_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__8 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__8_value;
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__9 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__9_value;
static const lean_string_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__10 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__10_value;
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13;
static const lean_string_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14_value;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16;
static const lean_ctor_object l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__17 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__17_value;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25;
static lean_once_cell_t l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRiiSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRiiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_instSliceableRiiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_instSliceableRiiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_instSliceableRiiSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_instSliceableRiiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRiiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRiiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRiiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRiiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_toList__rii___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRicSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRicSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_instSliceableRicSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_instSliceableRicSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_instSliceableRicSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_instSliceableRicSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRicSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRicSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRicSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRicSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_toList__ric___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRioSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRioSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_instSliceableRioSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_instSliceableRioSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_instSliceableRioSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_instSliceableRioSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRioSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRioSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRioSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRioSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_toList__rio___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRciSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRciSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_instSliceableRciSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_instSliceableRciSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_instSliceableRciSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_instSliceableRciSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRciSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRciSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRciSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRciSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_toList__rci___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRcoSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRcoSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_instSliceableRcoSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_instSliceableRcoSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_instSliceableRcoSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_instSliceableRcoSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRcoSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRcoSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRcoSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRcoSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_toList__rco___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRccSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRccSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_instSliceableRccSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_instSliceableRccSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_instSliceableRccSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_instSliceableRccSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRccSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRccSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRccSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRccSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_toList__rcc___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRoiSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRoiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_instSliceableRoiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_instSliceableRoiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_instSliceableRoiSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_instSliceableRoiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRoiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRoiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRoiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRoiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_toList__roi___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRocSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRocSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_instSliceableRocSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_instSliceableRocSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_instSliceableRocSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_instSliceableRocSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRocSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRocSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRocSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRocSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_toList__roc___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRooSlice___auto__1;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRooSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_TreeMap_instSliceableRooSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_instSliceableRooSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_TreeMap_instSliceableRooSlice___redArg___closed__0 = (const lean_object*)&l_Std_TreeMap_instSliceableRooSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRooSlice___redArg();
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRooSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRooSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRooSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_toList__roo___auto__1;
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14));
v___x_34_ = lean_string_utf8_byte_size(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14));
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_box(0);
v___x_42_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__17));
v___x_43_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16);
v___x_44_ = lean_box(2);
v___x_45_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
lean_ctor_set(v___x_45_, 2, v___x_42_);
lean_ctor_set(v___x_45_, 3, v___x_41_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18);
v___x_47_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13);
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19);
v___x_50_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20);
v___x_54_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5));
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21);
v___x_57_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__9));
v___x_58_ = lean_box(2);
v___x_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22);
v___x_61_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23);
v___x_64_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7));
v___x_65_ = lean_box(2);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24);
v___x_68_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5));
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25);
v___x_71_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4));
v___x_72_ = lean_box(2);
v___x_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
return v___x_73_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRiiSlice___redArg___lam__0(lean_object* v_carrier_75_, lean_object* v_range_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v_carrier_75_);
lean_ctor_set(v___x_77_, 1, v_range_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRiiSlice___redArg(){
_start:
{
lean_object* v___f_80_; 
v___f_80_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___redArg___closed__0));
return v___f_80_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRiiSlice___redArg___boxed(lean_object* v___dummy_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_TreeMap_instSliceableRiiSlice___redArg();
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRiiSlice(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_cmp_85_){
_start:
{
lean_object* v___f_86_; 
v___f_86_ = ((lean_object*)(l_Std_TreeMap_instSliceableRiiSlice___redArg___closed__0));
return v___f_86_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRiiSlice___boxed(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_cmp_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_TreeMap_instSliceableRiiSlice(v_00_u03b1_87_, v_00_u03b2_88_, v_cmp_89_);
lean_dec_ref(v_cmp_89_);
return v_res_90_;
}
}
static lean_object* _init_l_Std_TreeMap_toList__rii___auto__1(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_91_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRicSlice___auto__1(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRicSlice___redArg___lam__0(lean_object* v_carrier_93_, lean_object* v_range_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v_carrier_93_);
lean_ctor_set(v___x_95_, 1, v_range_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRicSlice___redArg(){
_start:
{
lean_object* v___f_98_; 
v___f_98_ = ((lean_object*)(l_Std_TreeMap_instSliceableRicSlice___redArg___closed__0));
return v___f_98_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRicSlice___redArg___boxed(lean_object* v___dummy_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_TreeMap_instSliceableRicSlice___redArg();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRicSlice(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_cmp_103_){
_start:
{
lean_object* v___f_104_; 
v___f_104_ = ((lean_object*)(l_Std_TreeMap_instSliceableRicSlice___redArg___closed__0));
return v___f_104_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRicSlice___boxed(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_cmp_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_TreeMap_instSliceableRicSlice(v_00_u03b1_105_, v_00_u03b2_106_, v_cmp_107_);
lean_dec_ref(v_cmp_107_);
return v_res_108_;
}
}
static lean_object* _init_l_Std_TreeMap_toList__ric___auto__1(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_109_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRioSlice___auto__1(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRioSlice___redArg___lam__0(lean_object* v_carrier_111_, lean_object* v_range_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_carrier_111_);
lean_ctor_set(v___x_113_, 1, v_range_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRioSlice___redArg(){
_start:
{
lean_object* v___f_116_; 
v___f_116_ = ((lean_object*)(l_Std_TreeMap_instSliceableRioSlice___redArg___closed__0));
return v___f_116_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRioSlice___redArg___boxed(lean_object* v___dummy_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_TreeMap_instSliceableRioSlice___redArg();
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRioSlice(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_cmp_121_){
_start:
{
lean_object* v___f_122_; 
v___f_122_ = ((lean_object*)(l_Std_TreeMap_instSliceableRioSlice___redArg___closed__0));
return v___f_122_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRioSlice___boxed(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_cmp_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_TreeMap_instSliceableRioSlice(v_00_u03b1_123_, v_00_u03b2_124_, v_cmp_125_);
lean_dec_ref(v_cmp_125_);
return v_res_126_;
}
}
static lean_object* _init_l_Std_TreeMap_toList__rio___auto__1(void){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_127_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRciSlice___auto__1(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRciSlice___redArg___lam__0(lean_object* v_carrier_129_, lean_object* v_range_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v_carrier_129_);
lean_ctor_set(v___x_131_, 1, v_range_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRciSlice___redArg(){
_start:
{
lean_object* v___f_134_; 
v___f_134_ = ((lean_object*)(l_Std_TreeMap_instSliceableRciSlice___redArg___closed__0));
return v___f_134_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRciSlice___redArg___boxed(lean_object* v___dummy_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_TreeMap_instSliceableRciSlice___redArg();
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRciSlice(lean_object* v_00_u03b1_137_, lean_object* v_00_u03b2_138_, lean_object* v_cmp_139_){
_start:
{
lean_object* v___f_140_; 
v___f_140_ = ((lean_object*)(l_Std_TreeMap_instSliceableRciSlice___redArg___closed__0));
return v___f_140_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRciSlice___boxed(lean_object* v_00_u03b1_141_, lean_object* v_00_u03b2_142_, lean_object* v_cmp_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_TreeMap_instSliceableRciSlice(v_00_u03b1_141_, v_00_u03b2_142_, v_cmp_143_);
lean_dec_ref(v_cmp_143_);
return v_res_144_;
}
}
static lean_object* _init_l_Std_TreeMap_toList__rci___auto__1(void){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_145_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRcoSlice___auto__1(void){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRcoSlice___redArg___lam__0(lean_object* v_carrier_147_, lean_object* v_range_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v_carrier_147_);
lean_ctor_set(v___x_149_, 1, v_range_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRcoSlice___redArg(){
_start:
{
lean_object* v___f_152_; 
v___f_152_ = ((lean_object*)(l_Std_TreeMap_instSliceableRcoSlice___redArg___closed__0));
return v___f_152_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRcoSlice___redArg___boxed(lean_object* v___dummy_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_TreeMap_instSliceableRcoSlice___redArg();
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRcoSlice(lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_cmp_157_){
_start:
{
lean_object* v___f_158_; 
v___f_158_ = ((lean_object*)(l_Std_TreeMap_instSliceableRcoSlice___redArg___closed__0));
return v___f_158_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRcoSlice___boxed(lean_object* v_00_u03b1_159_, lean_object* v_00_u03b2_160_, lean_object* v_cmp_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_TreeMap_instSliceableRcoSlice(v_00_u03b1_159_, v_00_u03b2_160_, v_cmp_161_);
lean_dec_ref(v_cmp_161_);
return v_res_162_;
}
}
static lean_object* _init_l_Std_TreeMap_toList__rco___auto__1(void){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_163_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRccSlice___auto__1(void){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRccSlice___redArg___lam__0(lean_object* v_carrier_165_, lean_object* v_range_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v_carrier_165_);
lean_ctor_set(v___x_167_, 1, v_range_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRccSlice___redArg(){
_start:
{
lean_object* v___f_170_; 
v___f_170_ = ((lean_object*)(l_Std_TreeMap_instSliceableRccSlice___redArg___closed__0));
return v___f_170_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRccSlice___redArg___boxed(lean_object* v___dummy_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_TreeMap_instSliceableRccSlice___redArg();
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRccSlice(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_cmp_175_){
_start:
{
lean_object* v___f_176_; 
v___f_176_ = ((lean_object*)(l_Std_TreeMap_instSliceableRccSlice___redArg___closed__0));
return v___f_176_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRccSlice___boxed(lean_object* v_00_u03b1_177_, lean_object* v_00_u03b2_178_, lean_object* v_cmp_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_TreeMap_instSliceableRccSlice(v_00_u03b1_177_, v_00_u03b2_178_, v_cmp_179_);
lean_dec_ref(v_cmp_179_);
return v_res_180_;
}
}
static lean_object* _init_l_Std_TreeMap_toList__rcc___auto__1(void){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_181_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRoiSlice___auto__1(void){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRoiSlice___redArg___lam__0(lean_object* v_carrier_183_, lean_object* v_range_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_carrier_183_);
lean_ctor_set(v___x_185_, 1, v_range_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRoiSlice___redArg(){
_start:
{
lean_object* v___f_188_; 
v___f_188_ = ((lean_object*)(l_Std_TreeMap_instSliceableRoiSlice___redArg___closed__0));
return v___f_188_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRoiSlice___redArg___boxed(lean_object* v___dummy_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_TreeMap_instSliceableRoiSlice___redArg();
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRoiSlice(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_cmp_193_){
_start:
{
lean_object* v___f_194_; 
v___f_194_ = ((lean_object*)(l_Std_TreeMap_instSliceableRoiSlice___redArg___closed__0));
return v___f_194_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRoiSlice___boxed(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_cmp_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_TreeMap_instSliceableRoiSlice(v_00_u03b1_195_, v_00_u03b2_196_, v_cmp_197_);
lean_dec_ref(v_cmp_197_);
return v_res_198_;
}
}
static lean_object* _init_l_Std_TreeMap_toList__roi___auto__1(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_199_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRocSlice___auto__1(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRocSlice___redArg___lam__0(lean_object* v_carrier_201_, lean_object* v_range_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_carrier_201_);
lean_ctor_set(v___x_203_, 1, v_range_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRocSlice___redArg(){
_start:
{
lean_object* v___f_206_; 
v___f_206_ = ((lean_object*)(l_Std_TreeMap_instSliceableRocSlice___redArg___closed__0));
return v___f_206_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRocSlice___redArg___boxed(lean_object* v___dummy_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_TreeMap_instSliceableRocSlice___redArg();
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRocSlice(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_cmp_211_){
_start:
{
lean_object* v___f_212_; 
v___f_212_ = ((lean_object*)(l_Std_TreeMap_instSliceableRocSlice___redArg___closed__0));
return v___f_212_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRocSlice___boxed(lean_object* v_00_u03b1_213_, lean_object* v_00_u03b2_214_, lean_object* v_cmp_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_TreeMap_instSliceableRocSlice(v_00_u03b1_213_, v_00_u03b2_214_, v_cmp_215_);
lean_dec_ref(v_cmp_215_);
return v_res_216_;
}
}
static lean_object* _init_l_Std_TreeMap_toList__roc___auto__1(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_217_;
}
}
static lean_object* _init_l_Std_TreeMap_instSliceableRooSlice___auto__1(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRooSlice___redArg___lam__0(lean_object* v_carrier_219_, lean_object* v_range_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v_carrier_219_);
lean_ctor_set(v___x_221_, 1, v_range_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRooSlice___redArg(){
_start:
{
lean_object* v___f_224_; 
v___f_224_ = ((lean_object*)(l_Std_TreeMap_instSliceableRooSlice___redArg___closed__0));
return v___f_224_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRooSlice___redArg___boxed(lean_object* v___dummy_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_TreeMap_instSliceableRooSlice___redArg();
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRooSlice(lean_object* v_00_u03b1_227_, lean_object* v_00_u03b2_228_, lean_object* v_cmp_229_){
_start:
{
lean_object* v___f_230_; 
v___f_230_ = ((lean_object*)(l_Std_TreeMap_instSliceableRooSlice___redArg___closed__0));
return v___f_230_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instSliceableRooSlice___boxed(lean_object* v_00_u03b1_231_, lean_object* v_00_u03b2_232_, lean_object* v_cmp_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_TreeMap_instSliceableRooSlice(v_00_u03b1_231_, v_00_u03b2_232_, v_cmp_233_);
lean_dec_ref(v_cmp_233_);
return v_res_234_;
}
}
static lean_object* _init_l_Std_TreeMap_toList__roo___auto__1(void){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_once(&l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26, &l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once, _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26);
return v___x_235_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Slice(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeMap_Slice(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_TreeMap_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeMap_Slice(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_TreeMap_instSliceableRiiSlice___auto__1 = _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_instSliceableRiiSlice___auto__1);
l_Std_TreeMap_toList__rii___auto__1 = _init_l_Std_TreeMap_toList__rii___auto__1();
lean_mark_persistent(l_Std_TreeMap_toList__rii___auto__1);
l_Std_TreeMap_instSliceableRicSlice___auto__1 = _init_l_Std_TreeMap_instSliceableRicSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_instSliceableRicSlice___auto__1);
l_Std_TreeMap_toList__ric___auto__1 = _init_l_Std_TreeMap_toList__ric___auto__1();
lean_mark_persistent(l_Std_TreeMap_toList__ric___auto__1);
l_Std_TreeMap_instSliceableRioSlice___auto__1 = _init_l_Std_TreeMap_instSliceableRioSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_instSliceableRioSlice___auto__1);
l_Std_TreeMap_toList__rio___auto__1 = _init_l_Std_TreeMap_toList__rio___auto__1();
lean_mark_persistent(l_Std_TreeMap_toList__rio___auto__1);
l_Std_TreeMap_instSliceableRciSlice___auto__1 = _init_l_Std_TreeMap_instSliceableRciSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_instSliceableRciSlice___auto__1);
l_Std_TreeMap_toList__rci___auto__1 = _init_l_Std_TreeMap_toList__rci___auto__1();
lean_mark_persistent(l_Std_TreeMap_toList__rci___auto__1);
l_Std_TreeMap_instSliceableRcoSlice___auto__1 = _init_l_Std_TreeMap_instSliceableRcoSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_instSliceableRcoSlice___auto__1);
l_Std_TreeMap_toList__rco___auto__1 = _init_l_Std_TreeMap_toList__rco___auto__1();
lean_mark_persistent(l_Std_TreeMap_toList__rco___auto__1);
l_Std_TreeMap_instSliceableRccSlice___auto__1 = _init_l_Std_TreeMap_instSliceableRccSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_instSliceableRccSlice___auto__1);
l_Std_TreeMap_toList__rcc___auto__1 = _init_l_Std_TreeMap_toList__rcc___auto__1();
lean_mark_persistent(l_Std_TreeMap_toList__rcc___auto__1);
l_Std_TreeMap_instSliceableRoiSlice___auto__1 = _init_l_Std_TreeMap_instSliceableRoiSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_instSliceableRoiSlice___auto__1);
l_Std_TreeMap_toList__roi___auto__1 = _init_l_Std_TreeMap_toList__roi___auto__1();
lean_mark_persistent(l_Std_TreeMap_toList__roi___auto__1);
l_Std_TreeMap_instSliceableRocSlice___auto__1 = _init_l_Std_TreeMap_instSliceableRocSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_instSliceableRocSlice___auto__1);
l_Std_TreeMap_toList__roc___auto__1 = _init_l_Std_TreeMap_toList__roc___auto__1();
lean_mark_persistent(l_Std_TreeMap_toList__roc___auto__1);
l_Std_TreeMap_instSliceableRooSlice___auto__1 = _init_l_Std_TreeMap_instSliceableRooSlice___auto__1();
lean_mark_persistent(l_Std_TreeMap_instSliceableRooSlice___auto__1);
l_Std_TreeMap_toList__roo___auto__1 = _init_l_Std_TreeMap_toList__roo___auto__1();
lean_mark_persistent(l_Std_TreeMap_toList__roo___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_TreeMap_Raw_Slice(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeMap_Slice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_Raw_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeMap_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeMap_Slice(builtin);
}
#ifdef __cplusplus
}
#endif
